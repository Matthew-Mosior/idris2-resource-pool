||| Resource Pool Internals
module Data.Pool.Internal

import Data.Array.Core
import Data.Linear.Ref1
import Data.Nat
import Data.So
import System.Concurrency
import System.Posix.Timer
import System.Posix.Timer.Prim

%language ElabReflection

%default total

||| Configuration of a Pool.
|||
||| Constraints:
||| - poolcachettl -> The smallest acceptable value is 0.5.
||| - poolmaxresources -> The smallest acceptable value is 1.
||| - poolnumstripes -> The smallest acceptable value is 1, poolnumstripes must not be larger than poolmaxresources.
public export
record PoolConfig a where
  constructor MkPoolConfig
  createresource   : IO a
  freeresource     : a -> IO ()
  poolcachettl     : (ttl : Double) -> {auto prf : So (0.5 <= ttl)} -> Double
  poolmaxresources : (maxres ** LTE 1 maxres)
  poolnumstripes   : Maybe (n ** (LTE 1 n, LTE n (fst poolmaxresources)))
  poolconfiglabel  : String

||| A simple (persistent) FIFO queue.
|||
||| This is used to maintain an ordered collection of waiting threads.
||| Elements are appended at the tail and removed from the head.
|||
||| Notes:
||| - This representation has O(n) append.
||| - Under contention (with CAS updates), appends may be retried,
|||   so this structure favors simplicity over performance.
||| - It is typically used together with a secondary "reversed"
|||   queue to amortize costs (two-list queue pattern).
public export
data Queue a
  = QNode a (Queue a)
  | QEnd

||| A single waiting thread for a `TMVar1`.
|||
||| A `Waiter1` splits synchronization into two parts:
||| 1. `slot` (shared state):
|||  - A mutable cell where a producer writes the result:
|||   - `Nothing`  => the waiter is still waiting
|||   - `Just x`   => a value has been delivered OR the waiter is dead/canceled
||| 2. `wake` (notification):
|||  - A channel used to block the thread and wake it once a value is ready.
|||
||| Invariants:
||| - A producer MUST write to `slot` before signaling `wake`.
||| - A waiter MUST read `slot` after being woken.
|||
||| This design emulates STM-style shared ownership (`TMVar`)
||| while using channels for efficient blocking.
public export
data Waiter1 : (s : Type) -> (a : Type) -> Type where
  MkWaiter1 :  (slot : Ref s (Maybe a))
            -> (wake : Channel ())
            -> Waiter1 s a

||| A single-element concurrent container with blocking semantics.
|||
||| `TMVar1` is a CAS + channel-based reimplementation of the semantics of
||| a `TMVar` from Haskell.
|||
||| It consists of:
||| 1. `ref`:
|||  - The shared slot holding the value.
|||   - `Nothing`  => empty
|||   - `Just x`   => full
||| 2. `waiters`:
|||  - A queue of threads waiting to take a value.
|||  - Each waiter is represented by a `Waiter1`, which provides:
|||   - A shared slot for value handoff
|||   - A channel for blocking/wakeup
|||
||| Semantics:
||| - `takeTMVar1`:
|||  - Reads from `ref` if available.
|||  - Otherwise enqueues a waiter and blocks.
||| - `putTMVar1`:
|||  - If a waiter exists, delivers the value directly (bypassing `ref`).
|||  - Otherwise stores the value in `ref`.
|||  - Retries if already full.
|||
||| Invariants:
||| - No lost wakeups: enqueue is always followed by a re-check
||| - A waiter is woken if and only if its `slot` has been filled
||| - Dead/canceled waiters are detected via their `slot`
|||
||| This structure provides STM-like behavior using:
||| - CAS for atomicity
||| - explicit queues for scheduling
||| - channels for blocking
public export
data TMVar1 : (s : Type) -> (a : Type) -> Type where
  MkTMVar1 :  (ref : Ref s (Maybe a))
           -> (waiters : Ref s (Queue (Waiter1 s a)))
           -> TMVar1 s a

||| An existing resource currently sitting in a pool.
public export
data Entry : (a : Type) -> Type where
  MkEntry :  (entry : a)
          -> (lastused : IClock CLOCK_MONOTONIC)
          -> Entry a

||| Stripe of a resource pool based on liner mutable queues.
||| If available is 0, the list of threads
||| waiting for a resource (each with an associated channel)
||| is queue ++ reverse queuer.
public export
data Stripe : (s : Type) -> (a : Type) -> Type where
  MkStripe :  (available : Nat)
           -> (cache : List (Entry a))
           -> (queue : Queue (Waiter1 s a))
           -> (queuer : Queue (Waiter1 s a))
           -> Stripe s a

||| A linear mutable stripe.
public export
data Stripe1 : (s : Type) -> (a : Type) -> Type where
  MkStripe1 :  Ref s (Stripe s a)
            -> Stripe1 s a

||| A single, local pool based on a linear mutable stripe.
public export
data LocalPool1 : (s : Type) -> (a : Type) -> Type where
  MkLocalPool1 :  (stripeid : Nat)
               -> (stripevar : Stripe1 s a)
               -> (cleanerref : IORef ())
               -> LocalPool1 s a

||| Striped resource pool based on linear mutable references.
public export
data Pool1 : (s : Type) -> (a : Type) -> Type where
  MkPool1 :  (poolconfig : PoolConfig a)
          -> (localpools : (MArray s n (LocalPool1 s a)))
          -> (reaperref : IORef ())
          -> Pool1 s a
