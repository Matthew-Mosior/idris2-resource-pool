||| Resource Pool
module Data.Pool

import public Data.Pool.Internal

import Data.Hashable
import System.Concurrency
import System.Info
import Data.List
import Data.Array
import IO.Async.Internal.Ref

%language ElabReflection

%default total

||| Create a PoolConfig with optional parameters having default values.
export
defaultPoolConfig :  IO a                     -- The action that creates a new resource.
                  -> (a -> IO ())             -- The action that destroys an existing resource.
                  -> Double                   -- Cache TTL (≥ 0.5).
                                              -- Note: The elapsed time before destroying a resource may be a little
                                              -- longer than requested, as the collector thread wakes at 1-second intervals.
                  -> (maxRes ** LTE 1 maxRes) -- The maximum number of resources to keep open across all stripes (≥ 1).
                                              -- Note: For each stripe, the number of resources is divided by the number of
                                              -- stripes and rounded up, hence the pool might end up creating up to N - 1
                                              -- resources more in total than specified, where N is the number of stripes.
                  -> PoolConfig a
defaultPoolConfig create free cachettl maxresources =
  let (maxresvalue ** prf) = maxresources
    in MkPoolConfig create free (\cachettl => cachettl) (maxresvalue ** prf) Nothing

||| Set the number of stripes in the pool.
||| If set to Nothing (the default value), the pool will create the amount of
||| stripes equal to the number of capabilities. This ensures that threads never
||| compete over access to the same stripe and results in a very good performance
||| in a multi-threaded environment.
export
setNumStripes : {maxres : Nat} -> Maybe (n ** (LTE 1 n, LTE n maxres)) -> PoolConfig a -> PoolConfig a
setNumStripes {maxres} numstripes (MkPoolConfig create free cachettl (_ ** prfMaxRes) _) =
  MkPoolConfig create free cachettl (maxres ** prfMaxRes) numstripes

||| Free resource entries in the stripes that fulfil a given condition.
export
cleanStripe : (Entry a -> Bool) -> (a -> IO ()) -> Channel (Stripe a) -> IO ()
cleanStripe isstale free ch = do
  -- Read the stripe.
  (MkStripe available cache squeue squeuer) <- channelGet ch
  let (stale, fresh) = partition isstale cache
      newstripe      = MkStripe available fresh squeue squeuer
  -- Put the new stripe on the channel.
  channelPut ch newstripe
  -- Free the stale resources (ensuring each call to free doesn't crash everything).
  for_ stale $ \(MkEntry e _) =>
    free e
