||| Resource Pool
module Data.Pool

import public Data.Pool.Internal

import Control.Monad.Elin
import Control.Monad.MCancel
import Data.Array
import Data.Array.Mutable
import Data.Hashable
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.List
import System.Concurrency
import System.Info
import System.Posix.Timer
import System.Posix.Timer.Prim
import Syntax.T1

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Cancellation check.
isCancelled :  Nat
            -> Queue Nat
            -> Bool
isCancelled _ QEnd         =
  False
isCancelled x (QNode y ys) =
  case x == y of
    True  =>
      True
    False =>
      isCancelled x ys

||| Append a value into the `Queue a`.
appendQ :  Queue a
        -> a
        -> Queue a
appendQ QEnd         x =
  QNode x QEnd
appendQ (QNode y ys) x =
  QNode y (appendQ ys x)

||| Revers a `Queue a`.
reverseQ :  Queue a
         -> Queue a
reverseQ q =
  go q QEnd
  where
    go :  Queue a
       -> Queue a
       -> Queue a
    go QEnd         acc =
      acc
    go (QNode x xs) acc =
      go xs (QNode x acc)

||| Append two `Queue a`.
appendAll :  Queue a
          -> Queue a
          -> Queue a
appendAll QEnd         ys =
  ys
appendAll (QNode x xs) ys =
  QNode x (appendAll xs ys)

||| Normalize two `Queue Waiter`s.
normalize :  Queue (Waiter a)
          -> Queue (Waiter a)
          -> Queue (Waiter a)
normalize QEnd q2 =
  reverseQ q2
normalize q1   q2 =
  appendAll q1 (reverseQ q2)

||| Dequeue first live waiter.
dequeueLive :  Queue (Waiter a)
            -> Queue Nat
            -> (Maybe (Waiter a), Queue (Waiter a))
dequeueLive QEnd                              cancelled =
  (Nothing, QEnd)
dequeueLive (QNode w@(MkWaiter id wake) rest) cancelled =
  case isCancelled id cancelled of
    True  =>
      dequeueLive rest cancelled
    False =>
      (Just w, rest)

||| Stripe-level dequeue.
dequeueStripe :  Stripe a
              -> (Maybe (Waiter a), Stripe a)
dequeueStripe (MkStripe available cache queue queuer nextid cancelled) =
  let fullq      = normalize queue queuer
      (mw, rest) = dequeueLive fullq cancelled
    in case mw of
         Nothing =>
           (Nothing, MkStripe available cache QEnd QEnd nextid cancelled)
         Just w  =>
           (Just w, MkStripe available cache rest QEnd nextid cancelled)

||| Execute `Stripe a` effects after CAS commit.
|||
||| This is the only place IO is performed for Stripe transitions.
|||
||| Guarantees:
||| - Effects are executed exactly once (only after successful CAS).
||| - Ordering is preserved.
||| - No effects are run on CAS retry.
|||
export
runEffects :  Stripe1 World a
           -> List (StripeEffect a)
           -> F1' World
runEffects mstripe effects t =
  traverse1_ (runEffect mstripe) effects t
  where
    grabTime : Elin World [Errno] (IClock CLOCK_MONOTONIC)
    grabTime = getTime CLOCK_MONOTONIC
    runEffect :  Stripe1 World a
              -> StripeEffect a
              -> F1' World
    runEffect _                     None                      t =
      () # t
    runEffect _                     (Wake ch val)             t =
      ioToF1 (channelPut ch val) t
    runEffect _                     (WakeMany pairs)          t =
      traverse1_ (\(ch,val) => ioToF1 (channelPut ch val))
                 pairs
                 t
    runEffect _                     (FreeMany free xs)        t =
      traverse1_ (\x => ioToF1 (free x)) xs t
    runEffect (MkStripe1 striperef) (InsertWithTimestamp val) t =
      let now # t := ioToF1 (runElinIO grabTime) t
        in case now of
             Left err   =>
               (assert_total $ idris_crash "Data.Pool.runEffects.runEffect: \{show err}") # t
             Right now' =>
               let entry := MkEntry val now'
                 in casupdate1 striperef (\(MkStripe available cache queue queuer nextid cancelled) =>
                                            (MkStripe available (entry :: cache) queue queuer nextid cancelled, ())
                                         ) t

||| Atomically apply a `Stripe a` transition and execute its effects.
|||
||| This is the central concurrency primitive of the `Stripe a` model.
|||
||| Behavior:
||| - Applies a pure state transition (`Stripe -> StripeStep`) under CAS.
||| - Retries automatically on contention using `casupdate1`.
||| - Extracts effects only from the successful committed transition.
||| - Executes effects exactly once after CAS succeeds.
|||
||| Guarantees:
||| - Linearizability, such that the `Stripe a` transition appears atomic.
||| - No duplicated effects (retries do not leak effects).
||| - No IO occurs during CAS evaluation.
||| - Effects are executed strictly after commit.
|||
||| Design Notes:
||| - `stepfn` must be pure (no IO, no external mutation).
||| - All side effects must be encoded in `StripeEffect a`.
||| - This function is the only place where `Stripe a` transitions are committed.
|||
export
casWithEffects :  Stripe1 World a
               -> (Stripe a -> StripeStep a)
               -> F1' World
casWithEffects (MkStripe1 striperef) stepfn t =
  let effects # t := casupdate1 striperef (\stripe =>
                                            let (MkStripeStep stripe' stripeeffects) = stepfn stripe
                                              in (stripe', stripeeffects)
                                          ) t
    in runEffects (MkStripe1 striperef) effects t

--------------------------------------------------------------------------------
--          Configuration
--------------------------------------------------------------------------------

||| Create a `PoolConfig a` with optional parameters having default values.
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

||| Set the number of stripes in the `PoolConfig a`.
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

||| Assign a label to the `PoolConfig a`.
export
setPoolLabel :  String
             -> PoolConfig a
             -> PoolConfig a
setPoolLabel label pc =
  { poolconfiglabel := label } pc

--------------------------------------------------------------------------------
--          Resource Management
--------------------------------------------------------------------------------

||| Get a `LocalPool World a`.
private
getLocalPool :  {n : Nat}
             -> MArray World n (LocalPool1 World a)
             -> F1 World (LocalPool1 World a)
getLocalPool pools t =
  case n == 1 of
    True  =>
      let sid  := 0
          sid' := remInt sid (cast {to=Int} n)
        in case tryNatToFin (cast {to=Nat} sid') of
             Nothing    =>
               (assert_total $ idris_crash "Data.Pool.getLocalPool: couldn't convert Nat to Fin") # t
             Just sid'' =>
               get pools sid'' t
    False =>
      let sid # t := ioToF1 getThreadId t
          sid'    := remInt sid (cast {to=Int} n)
        in case tryNatToFin (cast {to=Nat} sid') of
             Nothing    =>
               (assert_total $ idris_crash "Data.Pool.getLocalPool: couldn't convert Nat to Fin") # t
             Just sid'' =>
               get pools sid'' t
  where
    signumInt :  Int
              -> Int
    signumInt x =
      case x > 0 of
        True  =>
          1
        False =>
          case x < 0 of
            True  =>
              -1
            False =>
              0      
    quotInt :  Int
            -> Int
            -> Int
    quotInt x y =
      let q = x `div` y
          r = x `mod` y
        in case (r /= 0) && (signumInt x /= signumInt y) of
             True  =>
               q + 1
             False =>
               q
    remInt :  Int
           -> Int
           -> Int
    remInt x y =
      case y == 0 of
        True  =>
          assert_total $ idris_crash "division by zero"
        False =>
          x - (quotInt x y) * y

||| Deliver a value to a `Stripe a` state.
|||
||| This function:
||| - Updates Stripe state
||| - Emits wake effects
|||
||| Invariants:
||| - Each wake corresponds to a committed state transition.
||| - Queue ordering is preserved.
||| - Mo side effects occur during evaluation.
|||
export
signal :  Stripe a
       -> Maybe a
       -> StripeStep a
signal stripe@(MkStripe available cache queue queuer nextid cancelled) val =
  let (mw, MkStripe available' cache' queue' queuer' nextid' cancelled') = dequeueStripe stripe
    in case (mw, val) of
         -- Nothing to do
         (Nothing, Nothing)                  =>
           MkStripeStep (MkStripe available cache' queue' queuer' nextid' cancelled')
                        [None]
         -- No waiter, so store resoure, but defer timestamping
         (Nothing, Just val')                =>
           MkStripeStep (MkStripe (S available') cache' queue' queuer' nextid' cancelled')
                        [InsertWithTimestamp val']
         -- Waiter, but no value (rare / no-op)
         (Just _, Nothing)                   =>
           MkStripeStep (MkStripe available' cache' queue' queuer' nextid' cancelled')
                        [None]
         -- Deliver value directly
         (Just (MkWaiter _ wake), Just val') =>
           MkStripeStep (MkStripe available' cache' queue' queuer' nextid' cancelled')
                        [Wake wake (Just val')]

private
takeStep :  Stripe a
         -> IO (StripeStep a, Either a (Nat, Channel (Maybe a)))
takeStep (MkStripe available cache queue queuer nextid cancelled) =
  case cache of
    -- Slow path, enqueue waiter
    []                    => do
      wake        <- makeChannel
      let wid     = nextid
          waiter  = MkWaiter wid wake
          stripe' = MkStripe available cache queue (appendQ queuer waiter) (S nextid) cancelled
      pure (MkStripeStep stripe' [None], Right (wid, wake))
    -- Fast path, consume cached resource
    (MkEntry v _ :: rest) =>
      let stripe' = MkStripe (minus available 1) rest queue queuer nextid cancelled
        in pure (MkStripeStep stripe' [None], Left v)

private
putStep :  Stripe a
        -> a
        -> StripeStep a
putStep st v =
  signal st (Just v)

||| Block until a resource is delivered to this waiter.
|||
||| Behavior:
||| - Waits on the provided `Channel (Maybe a)` for a wakeup signal.
||| - Returns:
|||  - `Just a` if a resource is successfully delivered.
|||  - `Nothing` if the waiter is cancelled or destroyed.
|||
||| Cancellation:
||| - If the waiting thread is aborted, the `cleanup` handler is invoked.
||| - This atomically marks the waiter as cancelled by inserting its `wid` into the Stripe's `cancelled` queue.
||| - Cancellation is lazy, cancelled waiters are skipped during dequeue.
|||
||| Guarantees:
||| - No busy waiting, the thread blocks on a channel.
||| - No lost wakeups, every successful `signal` results in exactly one `channelPut` to a live waiter.
||| - Safe under races:
|||  - If cancellation happens before wake, waiter is skipped later.
|||  -  If wake happens before cancellation, value is delivered.
||| - Exactly-once semantics:
|||  - Each waiter receives at most one wakeup.
|||  - Each wakeup corresponds to a committed Stripe transition.
|||
||| Design Notes:
||| - This function performs no direct Stripe mutation except in `cleanup`.
||| - All coordination with producers happens via `signal` + `StripeEffect`.
||| - The `Channel (Maybe a)` encodes both success (`Just`) and termination (`Nothing`).
|||
||| Invariants:
||| - `wid` must be the same identifier used when enqueuing the waiter.
||| - The channel must be single-consumer and used exactly once.
||| - Stripe state remains the single source of truth for cancellation.
|||
export
waitForResource :  Stripe1 World a
                -> Nat               -- waiter id
                -> Channel (Maybe a) -- wake channel
                -> F1 World (Maybe a)
waitForResource mstripe wid wake t =
  let res # t := ioToF1 (runElinIO (waitForResource' mstripe wid wake)) t
    in case res of
         Right res' =>
           res' # t
         Left err   =>
           (assert_total $ idris_crash "Data.Pool.waitForResource: \{show err}") # t
  where
    cleanup :   Stripe1 World a
             -> Nat
             -> F1' World
    cleanup (MkStripe1 mstripe) wid t =
      casupdate1 mstripe (\(MkStripe available cache queue queuer nextid cancelled) =>
                           (MkStripe available cache queue queuer nextid (appendQ cancelled wid), ())
                         ) t
    waitForResource'' :  Channel (Maybe a)
                      -> F1 World (Maybe a)
    waitForResource'' wake t =
      ioToF1 (channelGet wake) t
    waitForResource' :  MCancel (Elin World)
                     => Stripe1 World a
                     -> Nat
                     -> Channel (Maybe a)
                     -> Elin World [Errno] (Maybe a)
    waitForResource' mstripe wid wake =
      onAbort (runIO (waitForResource'' wake)) (runIO (cleanup mstripe wid))

||| Destroy a resource instead of returning it to the `Pool1 World a`.
|||
||| Behavior:
||| - If a waiter exists, they are woken with `Nothing`.
||| - Otherwise, no state change occurs (resource is discarded).
|||
||| Guarantees:
||| - Waiters are not left blocked indefinitely.
||| - No resource is reinserted into the cache.
|||
export
destroyResource :  Stripe1 World a
                -> F1' World
destroyResource (MkStripe1 striperef) t =
  casWithEffects (MkStripe1 striperef) (\stripe => signal stripe Nothing) t

||| Return a resource to the `Pool1 World a`.
|||
||| Behavior:
||| - If a waiter exists, the resource is delivered directly.
||| - Otherwise, it is inserted into the cache with a timestamp.
|||
||| Guarantees:
||| - No resource is lost.
||| - Wakeups are ordered and deterministic.
|||
export
putResource :  Stripe1 World a
            -> a
            -> F1' World
putResource (MkStripe1 striperef) val t =
  casWithEffects (MkStripe1 striperef) (\stripe => signal stripe (Just val)) t

||| Free resource entries in the stripe that satisfy a predicate.
|||
||| Behavior:
||| - Removes stale entries from cache atomically.
||| - Emits a batched free effect.
||| - Ensures no resource is freed twice or leaked.
|||
||| Guarantees:
||| - Removal is atomic with respect to Stripe.
||| - Freeing happens after commit.
||| - Safe under contention and retries.
|||
private
cleanStripe :  (Entry a -> Bool)
            -> (a -> IO ())
            -> Stripe1 World a
            -> F1' World
cleanStripe isstale free (MkStripe1 striperef) t =
  casWithEffects (MkStripe1 striperef) step t
  where
    step :  Stripe a
         -> StripeStep a
    step (MkStripe available cache queue queuer nextid cancelled) =
      let (stale, fresh) = partition isstale cache
          freedvals      = map (\(MkEntry v _) => v) stale
        in MkStripeStep
             (MkStripe available fresh queue queuer nextid cancelled)
             ( case freedvals of
                 [] =>
                   [None]
                 xs =>
                   [FreeMany free xs]
             )

||| Destroy all resources in all stripes in the `Pool1 World a`.
|||
||| Behavior:
||| - Removes all cached resources from every stripe.
||| - Frees them via the provided `freeresource` function.
||| - Leaves wait queues untouched.
|||
||| Guarantees:
||| - Each resource is freed exactly once.
||| - No IO occurs during Stripe state transitions.
||| - Safe under contention (uses CAS + effect model).
|||
||| Notes:
||| - This only affects cached (idle) resources.
||| - Resources currently checked out are NOT affected.
|||
export
destroyAllResources :  {n : Nat}
                    -> Pool1 World a
                    -> MArray World n (LocalPool1 World a)
                    -> F1' World
destroyAllResources (MkPool1 (MkPoolConfig _ freeresource _ _ _ _) _ _) localpools t =
  go 0 n localpools t
  where
    go :  (o, x : Nat)
       -> {auto v : Ix x n}
       -> {auto 0 prf : LTE o $ ixToNat v}
       -> (arr : MArray World n (LocalPool1 World a))
       -> F1' World
    go o Z     _   t =
      () # t
    go o (S j) arr t =
      let MkLocalPool1 _ stripe1 _ # t := getIx arr j t
          ()                       # t := cleanStripe (const True) freeresource stripe1 t
        in go o j arr t

||| Restore one unit of available capacity in the `Stripe a`.
|||
||| Behavior:
||| - Increments `available` by 1.
||| - Does not modify cache or queue.
||| - Emits no effects.
|||
||| Used when resource creation fails after capacity was reserved.
|||
||| Guarantees:
||| - Atomic under CAS.
||| - No IO performed.
||| - Safe under contention.
|||
export
restoreSize :  Stripe1 World a
            -> F1' World
restoreSize (MkStripe1 striperef) t =
  casWithEffects (MkStripe1 striperef) step t
  where
    step :  Stripe a
         -> StripeStep a
    step (MkStripe available cache queue queuer nextid cancelled) =
      MkStripeStep
        (MkStripe (S available) cache queue queuer nextid cancelled)
        [None]

export
takeResource :  Pool1 World a
             -> F1 World (a, LocalPool1 World a)
takeResource pool@(MkPool1 poolconfig localpools _) t =
  let lp@(MkLocalPool1 _ stripe1@(MkStripe1 striperef) _) # t := getLocalPool localpools t
      -- Pre-allocate channel for slow path
      wake                                                # t := ioToF1 makeChannel t
      (effects, result)                                   # t :=
        casupdate1 striperef (\(MkStripe available cache queue queuer nextid cancelled) =>
                                case cache of
                                  -- fast path
                                  MkEntry v _ :: rest =>
                                    let none : List (StripeEffect a)
                                        none    = [None]
                                        stripe' = MkStripe (minus available 1)
                                                           rest
                                                           queue
                                                           queuer
                                                           nextid
                                                           cancelled
                                      in ( stripe'
                                         , (none, Left v)
                                         )
                                  -- slow path
                                  []                  =>
                                    let none : List (StripeEffect a)
                                        none    = [None]
                                        wid     = nextid
                                        waiter  = MkWaiter wid wake
                                        stripe' = MkStripe available
                                                           cache
                                                           queue
                                                           (appendQ queuer waiter)
                                                           (S nextid)
                                                           cancelled
                                      in ( stripe'
                                         , (none, Right (wid, wake))
                                         )
                             ) t
      -- Run effects after commit
      ()                # t := runEffects stripe1 effects t
    in case result of
         -- fast path
         Left v =>
           (v, lp) # t
         -- slow path
         Right (wid, wake) =>
           let mres # t := waitForResource stripe1 wid wake t
             in case mres of
                  -- woken with resource
                  Just v =>
                    (v, lp) # t
                  -- need to create
                  Nothing =>
                    let res # t := ioToF1 (runElinIO (createWithCleanup poolconfig stripe1)) t
                      in case res of
                           Right v =>
                             (v, lp) # t
                           Left err =>
                             (assert_total $ idris_crash "Data.Pool.takeResource: \{show err}") # t
  where    
    createWithCleanup :  PoolConfig a
                      -> Stripe1 World a
                      -> Elin World [Errno] a
    createWithCleanup (MkPoolConfig createResource _ _ _ _ _) stripe =
      onAbort (liftIO createResource) (runIO (restoreSize stripe))
