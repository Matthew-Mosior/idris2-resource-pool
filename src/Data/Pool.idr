||| Resource Pool
module Data.Pool

import public Data.Pool.Internal

import Data.Hashable
import System.Concurrency
import System.Info
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.List
import Data.Array
import IO.Async.Internal.Ref

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Configuration
--------------------------------------------------------------------------------

||| Create a PoolConfig with optional parameters having default values.
export
defaultPoolConfig :  IO a                     -- The action that creates a new resource.
                  -> (a -> IO ())             -- The action that destroys an existing resource.
                  -> Double                   -- Cache TTL (≥ 0.5).
                                              -- Note: The elapsed time before destroying a resource may be a little
                                              -- longer than requested, as the collector thread wakes at 1-second intervals.
                  -> (maxres ** LTE 1 maxres) -- The maximum number of resources to keep open across all stripes (≥ 1).
                                              -- Note: For each stripe, the number of resources is divided by the number of
                                              -- stripes and rounded up, hence the pool might end up creating up to N - 1
                                              -- resources more in total than specified, where N is the number of stripes.
                  -> PoolConfig a
defaultPoolConfig create free cachettl maxresources =
  MkPoolConfig create
               free
               (\cachettl => cachettl)
               maxresources
               Nothing
               ""

||| Set the number of stripes in the pool.
||| If set to Nothing (the default value), the pool will create the amount of
||| stripes equal to the number of capabilities. This ensures that threads never
||| compete over access to the same stripe and results in a very good performance
||| in a multi-threaded environment.
export
setNumStripes :  (pc : PoolConfig a)
              -> Maybe (n ** (LTE 1 n, LTE n (fst (poolmaxresources pc))))
              -> PoolConfig a
setNumStripes (MkPoolConfig create free cachettl (maxres ** prfmaxres) _ pclabel) numstripes =
  MkPoolConfig create
               free
               cachettl
               (maxres ** prfmaxres)
               numstripes
               pclabel

||| Assign a label to the pool.
export
setPoolLabel :  String
             -> PoolConfig a
             -> PoolConfig a
setPoolLabel label pc =
  { pclabel := label } pc

--------------------------------------------------------------------------------
--          Resource Management
--------------------------------------------------------------------------------

||| Take a resource from the pool, following the same results as `withResource`.
|||
||| This function returns both a resource and the `LocalPool` it came
||| from so that it may either be destroyed (via `destroyResource`) or returned
||| to the pool (via `putResource`).
takeResource :  Pool1 World a
             -> F1 World (a, LocalPool1 s a)
takeResource pool = mask_ $ do


||| Free resource entries in the stripes that fulfil a given condition.
export
cleanStripe :  (Entry a -> Bool)
            -> (a -> IO ())
            -> IORef (Stripe1 World a)
            -> F1' World
cleanStripe isstale free stripe t =
  let (MkStripe1 available cache queue queuer) # t := read1 stripe t
      (stale, fresh)                               := partition isstale cache
      ()                                       # t := write1 stripe (MkStripe1 available fresh queue queuer) t
    in traverse1_ (\(MkEntry e _) => ioToF1 (free e)) stale t
