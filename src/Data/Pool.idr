||| Resource Pool
module Data.Pool

import public Data.Pool.Internal

import Data.Hashable
import System.Concurrency
import Data.IORef
import Data.Array

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
defaultPoolConfig create free ttl maxresources =
  let (maxresvalue ** prf) = maxresources
    in MkPoolConfig create free (\ttl => ttl) (maxresvalue ** prf) Nothing

||| Set the number of stripes in the pool.
||| If set to Nothing (the default value), the pool will create the amount of
||| stripes equal to the number of capabilities. This ensures that threads never
||| compete over access to the same stripe and results in a very good performance
||| in a multi-threaded environment.
export
setNumStripes : Maybe (n ** (LTE 1 n, LTE n poolmaxresources)) -> PoolConfig a -> PoolConfig a
setNumStripes numStripes (MkPoolConfig create free ttl (maxres ** prf) numstripes) =
  MkPoolConfig create free ttl (maxres ** prf) numstripes
