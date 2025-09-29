||| Resource Pool Internals
module Data.Pool.Internal

import Data.Array.Core
import Data.Linear.Ref1
import Data.Nat
import Data.So

%language ElabReflection

%default total

||| Configuration of a Pool.
||| Constraints:
||| poolcachettl -> The smallest acceptable value is 0.5.
||| poolmaxresources -> The smallest acceptable value is 1.
||| poolnumstripes -> The smallest acceptable value is 1, poolnumstripes must not be larger than poolmaxresources.
public export
data PoolConfig : (a : Type) -> Type where
  MkPoolConfig :  (createresource   : IO a)
               -> (freeresource     : (a -> IO ()))
               -> (poolcachettl     : (ttl : Double) -> {auto prf : So (0.5 <= ttl)} -> Double)
               -> (poolmaxresources : (maxres ** LTE 1 maxres))
               -> (poolnumstripes   : Maybe (n ** (LTE 1 n, LTE n (fst poolmaxresources)))) 
               -> PoolConfig a

||| A queue of linear mutable references
||| corresponding to threads waiting for resources.
public export
data Queue1 : (s : Type) -> Type -> Type where
  QNode1 :  Ref s (Maybe a)
         -> Queue1 s a
         -> Queue1 s a
  QEnd1  :  Queue1 s a

||| An existing resource currently sitting in a pool.
public export
data Entry : (a : Type) -> Type where
  MkEntry :  (entry : a)
          -> (lastused : Double)
          -> Entry a

||| Stripe of a resource pool based on liner mutable queues.
||| If available is 0, the list of threads
||| waiting for a resource (each with an associated channel)
||| is queue ++ reverse queuer.
public export
data Stripe1 : (s : Type) -> (a : Type) -> Type where
  MkStripe1 :  (available : Nat)
            -> (cache : List (Entry a))
            -> (queue : Queue1 s a)
            -> (queuer : Queue1 s a)
            -> Stripe1 s a

||| A single, local pool based on a linear mutable stripe.
public export
data LocalPool1 : (s : Type) -> (a : Type) -> Type where
  MkLocalPool1 :  (stripeid : Nat)
               -> (stripevar : Ref s (Stripe1 s a))
               -> (cleanerref : IORef ())
               -> LocalPool1 s a

||| Striped resource pool based on linear mutable references.
public export
data Pool1 : (s : Type) -> (a : Type) -> Type where
  MkPool1 :  (poolconfig : PoolConfig a)
          -> (localpools : (MArray s n (LocalPool1 s a)))
          -> (reaperref : IORef ())
          -> Pool1 s a
