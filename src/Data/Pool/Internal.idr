||| Resource Pool Internals
module Data.Pool.Internal

import Data.Nat
import System.Concurrency
import IO.Async.Internal.Ref
import Data.Array

%language ElabReflection

%default total

||| Configuration of a Pool.
||| Constraints:
||| poolcachettl -> The smallest acceptable value is 0.5.
||| poolmaxresources -> The smallest acceptable value is 1.
||| poolnumstripes -> The smallest acceptable value is 1, poolnumstripes must not be larger than poolmaxresources.
public export
data PoolConfig : (a : Type) -> Type where
  MkPoolConfig :  (createresource : IO a)
               -> (freeresource : (a -> IO ()))
               -> (poolcachettl : (ttl : Double) -> {auto prf : So (0.5 <= ttl)} -> Double)
               -> (poolmaxresources : (maxres ** LTE 1 maxRes))
               -> (poolnumstripes : Maybe (n ** (LTE 1 n, LTE n (fst poolmaxresources)))) 
               -> PoolConfig a

||| A queue of channels corresponding to threads
||| waiting for resources.
public export
data SQueue a = MkSQueue (Channel (Maybe a)) (SQueue a)
              | Empty

||| An existing resource currently sitting in a pool.
public export
data Entry : (a : Type) -> Type where
  MkEntry :  (entry : a)
          -> (lastused : Double)
          -> Entry a

||| Stripe of a resource pool.
||| If available is 0, the list of threads
||| waiting for a resource (each with an associated channel)
||| is squeue ++ reverse squeuer.
public export
data Stripe : (a : Type) -> Type where
  MkStripe :  (available : Nat)
           -> (cache : List (Entry a))
           -> (squeue : SQueue a)
           -> (squeuer : SQueue a)
           -> Stripe a

||| A single, local pool.
public export
data LocalPool : (a : Type) -> Type where
  MkLocalPool :  (stripeid : Nat)
              -> (stripevar : Channel (Stripe a))
              -> (cleanerref : IORef ())
              -> LocalPool a

||| Striped resource pool based on semaphores (See System.Concurrency).
public export
data Pool : (a : Type) -> Type where
  MkPool :  (poolconfig : PoolConfig a)
         -> (localpools : (Array (LocalPool a)))
         -> (reaperref : IORef ())
         -> Pool a
