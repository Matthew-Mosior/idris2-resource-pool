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
|||
public export
record PoolConfig a where
  constructor MkPoolConfig
  createresource   : IO a
  freeresource     : a -> IO ()
  poolcachettl     : Clock Duration
  poolmaxresources : (maxres ** LTE 1 maxres)
  poolnumstripes   : (n ** (LTE 1 n, LTE n (fst poolmaxresources)))
  poolconfiglabel  : String

||| A simple (persistent) FIFO queue.
|||
||| This is used to maintain an ordered collection of waiting threads.
||| Elements are appended at the tail and removed from the head.
|||
||| Notes:
||| - This representation has O(n) append.
||| - Under contention (with CAS updates), appends may be retried, so this structure favors simplicity over performance.
||| - It is typically used together with a secondary "reversed" queue to amortize costs (two-list queue pattern).
|||
public export
data Queue a
  = QNode a (Queue a)
  | QEnd

||| A pure waiting token representing a blocked thread.
|||
||| This contains no mutable state. All lifecycle tracking is handled
||| by the Stripe during dequeue / cancellation.
|||
||| Fields:
||| - `id`   : unique identifier for cancellation tracking
||| - `wake` : channel used to unblock the thread
|||
||| Invariants:
||| - Waiter is immutable
||| - Wake is single-use
||| - Cancellation is handled by Stripe (not locally)
|||
public export
data Waiter : (a : Type) -> Type where
  MkWaiter :  (id   : Nat)
           -> (wake : Channel (Maybe a))
           -> Waiter a

||| An existing resource currently sitting in a pool.
public export
data Entry : (a : Type) -> Type where
  MkEntry :  (entry : a)
          -> (lastused : IClock CLOCK_MONOTONIC)
          -> Entry a

||| Stripe is the only concurrent state machine in the system.
|||
||| It owns:
||| - Resource availability.
||| - Cached resources.
||| - All waiting threads.
||| - Cancellation tracking.
|||
||| All mutations occur via CAS on an enclosing Ref, `Stripe1 s a`.
|||
||| Fields:
||| - `available` : number of available resources
||| - `cache`     : reusable resources
||| - `queue`     : primary FIFO of waiters
||| - `queuer`    : secondary FIFO (amortized append)
||| - `nextId`    : fresh waiter id supply
||| - `cancelled` : list of cancelled waiter ids
|||
||| Invariants:
||| - Stripe is immutable between CAS updates.
||| - Queue ordering is authoritative.
||| - Cancelled waiters are lazily skipped.
|||
public export
data Stripe : (a : Type) -> Type where
  MkStripe :  (available : Nat)
           -> (cache : List (Entry a))
           -> (queue : Queue (Waiter a))
           -> (queuer : Queue (Waiter a))
           -> (nextid : Nat)
           -> (cancelled : Queue Nat)
           -> Stripe a

||| A linear mutable stripe.
public export
data Stripe1 : (s : Type) -> (a : Type) -> Type where
  MkStripe1 :  Ref s (Stripe a)
            -> Stripe1 s a

||| Effects emitted by a Stripe transition.
|||
||| These are collected during CAS computation and executed
||| only after a successful CAS commit.
|||
||| Guarantees:
||| - No IO inside CAS.
||| - No duplicated effects on retry.
||| - Deterministic state transitions.
|||
public export
data StripeEffect a
  = Wake (Channel (Maybe a)) (Maybe a)
  | WakeMany (List (Channel (Maybe a), Maybe a))
  | InsertWithTimestamp a
  | FreeMany (a -> IO ()) (List a)
  | None

||| Result of a Stripe state transition.
|||
||| Represents:
||| - The new Stripe state (to be CAS'd).
||| - Effects to run AFTER successful commit.
|||
||| Invariants:
||| - This must be treated as a one-shot value.
||| - If CAS fails, this MUST be discarded.
||| - Effects must NEVER be run unless CAS succeeds.
public export
record StripeStep a where
  constructor MkStripeStep
  stripe  : Stripe a
  effects : List (StripeEffect a)

||| A single, local pool based on a linear mutable stripe.
public export
data LocalPool1 : (s : Type) -> (a : Type) -> Type where
  MkLocalPool1 :  (stripeid : Nat)
               -> (stripevar : Stripe1 s a)
               -> (cleanerref : IORef ())
               -> LocalPool1 s a

||| Striped resource pool based on linear mutable references.
public export
data Pool1 : (s : Type) -> (n : Nat) -> (a : Type) -> Type where
  MkPool1 :  (poolconfig : PoolConfig a)
          -> (localpools : (MArray s n (LocalPool1 s a)))
          -> Pool1 s n a
