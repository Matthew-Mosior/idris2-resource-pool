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

%language ElabReflection

%default total

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

private
signal :  Stripe1 World a
       -> Maybe a
       -> F1 World (Stripe1 World a)
signal (MkStripe1 stripe) ma t =
  let (MkStripe available cache queue queuer) # t := read1 stripe t
    in case available == 0 of
         True  =>
           loop cache queue queuer t 
         False =>
           case ma of
             Nothing  =>
               let newentry    := cache
                   stripe1 # t := ref1 (MkStripe (plus available 1) newentry queue queuer) t
                 in MkStripe1 stripe1 # t
             Just ma' => 
               let now     # t := ioToF1 (runElinIO grabTime) t
                 in case now of
                      Left  _    =>
                        -- Only happens if we can't get time
                        (assert_total $ idris_crash "Data.Pool.signal: grabTime failed") # t
                      Right now' =>
                        let newentry    := MkEntry ma' now'
                            stripe1 # t := ref1 (MkStripe (plus available 1) [newentry] queue queuer) t
                          in MkStripe1 stripe1 # t
  where
    reverseQueue :  Queue (Waiter1 World a)
                 -> F1 World (Queue (Waiter1 World a))
    reverseQueue q = go QEnd q
      where
        go :  Queue (Waiter1 World a)
           -> Queue (Waiter1 World a)
           -> F1 World (Queue (Waiter1 World a))
        go q acc t =
          case q of
            QEnd       =>
              acc # t
            QNode x xs =>
              (assert_total $ go (QNode x acc) xs) t
    grabTime : Elin World [Errno] (IClock CLOCK_MONOTONIC)
    grabTime = getTime CLOCK_MONOTONIC
    loop :  List (Entry a)
         -> Queue (Waiter1 World a)
         -> Queue (Waiter1 World a)
         -> F1 World (Stripe1 World a)
    loop cache QEnd         QEnd t =
      case ma of
        Nothing  =>
          let stripe # t := ref1 ( MkStripe 1
                                            cache
                                            QEnd
                                            QEnd
                                 ) t
            in MkStripe1 stripe # t 
        Just ma' =>
          let now # t := ioToF1 (runElinIO grabTime) t
            in case now of
                 Left  _    =>
                   -- Only happens if we can't get time
                   (assert_total $ idris_crash "Data.Pool.signal.loop: grabTime failed") # t
                 Right now' =>
                   let newentry   := MkEntry ma' now'
                       newcache   := newentry :: cache
                       stripe # t := ref1 ( MkStripe 1
                                                     newcache
                                                     QEnd
                                                     QEnd
                                          ) t
                     in MkStripe1 stripe # t 
    loop cache QEnd                             qr    t =
      let qr' # t := reverseQueue qr t
        in (assert_total $ loop cache qr' QEnd) t
    loop cache (QNode (MkWaiter1 slot wake) ws) qr    t =
      let cur # t := read1 slot t
        in case cur of
             Just _  =>
               -- Dead waiter, skip
               (assert_total $ loop cache ws qr) t
             Nothing =>
               -- Live waiter, deliver
               let wrote # t := casupdate1 slot (\slot' =>
                                                  case slot' of
                                                    Nothing =>
                                                      (ma, True)
                                                    Just x  =>
                                                      (Just x, False)
                                                ) t
                 in case wrote of
                      True  =>
                        let ()        # t := ioToF1 (channelPut wake ()) t
                            newstripe # t := ref1 ( MkStripe 0
                                                             cache
                                                             ws
                                                             qr
                                                  ) t
                          in MkStripe1 newstripe # t 
                      False =>
                        -- lost race, treat as dead waiter
                        (assert_total $ loop cache ws qr) t

private
takeTMVar1 :  TMVar1 World a
           -> F1 World a
takeTMVar1 (MkTMVar1 ref waiters) t =
  let m # t := tryTake t
    in case m of
    Just x  =>
      x # t
    Nothing =>
          -- Create waiter
      let slot # t := ref1 Nothing t
          wake # t := ioToF1 makeChannel t
          w        := MkWaiter1 slot wake
          -- Enqueue ourselves
          ()   # t := casmod1 waiters (\q =>
                                        case q of
                                          QEnd =>
                                            QNode w QEnd
                                          QNode x xs =>
                                            let go :  Queue (Waiter1 World a)
                                                   -> Queue (Waiter1 World a)
                                                go QEnd         = QNode w QEnd
                                                go (QNode y ys) = QNode y (go ys)
                                              in QNode x (go xs)
                                      ) t
          -- Re-check after enqueue
          m2   # t := tryTake t
        in case m2 of
             Just x  =>
               x # t
             Nothing =>
                   -- Wait to be woken
               let () # t := ioToF1 (channelGet wake) t
                   -- Read delivered value
                   mv # t := read1 slot t
                 in case mv of
                      Just x  =>
                        x # t
                      Nothing =>
                        -- Should not happen if protocol is correct
                        (assert_total $ idris_crash "Data.Pool.takeTMVar1: impossible") # t
  where
    tryTake : F1 World (Maybe a)
    tryTake t =
      casupdate1 ref (\cur =>
                       case cur of
                         Nothing =>
                           (Nothing, Nothing)
                         Just x  =>
                           (Nothing, Just x)
                     ) t

private
tryTakeTMVar1 :  TMVar1 s a
              -> F1 s (Maybe a)
tryTakeTMVar1 (MkTMVar1 ref _) t =
  casupdate1 ref (\cur =>
                   case cur of
                     Nothing =>
                       (Nothing, Nothing)
                     Just x  =>
                       (Nothing, Just x)
                 ) t

private
putTMVar1 :  TMVar1 World a
          -> a
          -> F1' World
putTMVar1 (MkTMVar1 ref waiters) val t =
  let mw # t := dequeueWaiter waiters t
    in case mw of
         Nothing                    =>
           let success # t := tryPut ref val t
             in case success of
                  True  =>
                    () # t
                  False =>
                    (assert_total $ putTMVar1 (MkTMVar1 ref waiters) val) t
         Just (MkWaiter1 slot wake) =>
           let curslot # t := read1 slot t
             in case curslot of
                  Just _  =>
                    -- stale waiter, skip
                    (assert_total $ putTMVar1 (MkTMVar1 ref waiters) val) t
                  Nothing =>
                    let _ # t := casupdate1 slot (\slot' =>
                                                   (Just val, ()) 
                                                 ) t
                      in ioToF1 (channelPut wake ()) t
  where
    tryPut :  Ref World (Maybe a)
           -> a
           -> F1 World Bool
    tryPut ref v t =
      casupdate1 ref (\cur =>
                       case cur of
                         Nothing =>
                           (Just v, True)
                         Just _  =>
                           (cur, False)
                     ) t
    dequeueWaiter :  Ref s (Queue (Waiter1 s a))
                  -> F1 s (Maybe (Waiter1 s a))
    dequeueWaiter ref t =
      casupdate1 ref (\q =>
                       case q of
                         QEnd         =>
                           (QEnd, Nothing)
                         QNode w rest =>
                           (rest, Just w)
                     ) t

||| Wait for the resource to be put into a given `TMVar1 World a`.
export
waitForResource :  TMVar1 World (Maybe a)
                -> Stripe1 World a
                -> F1 World (Maybe a)
waitForResource q mstripe t =
  let res # t := ioToF1 (runElinIO (waitForResource' q mstripe)) t
    in case res of
         Right res =>
           res # t
         Left err =>
           (assert_total $ idris_crash "Data.Pool.waitForResource: \{show err}") # t
  where
    cleanup' :  TMVar1 World (Maybe a)
             -> Stripe1 World a
             -> F1' World
    cleanup' (MkTMVar1 ref waiters) (MkStripe1 mstripe) t =
      let m # t := tryTakeTMVar1 (MkTMVar1 ref waiters) t
        in case m of
             Nothing =>
               -- Still waiting.  Mark ourselves as "dead".
               -- This ensures producers can skip us.
               putTMVar1 (MkTMVar1 ref waiters) Nothing t
             Just ma =>   
               -- We did recieve a value before being canceled.
               -- Pass it to someone else.
               let MkStripe1 newstripe # t := signal (MkStripe1 mstripe) ma t
                   newstripe'          # t := read1 newstripe t
                 in casupdate1 mstripe (\mstripe' =>
                                         (newstripe', ())
                                       ) t
    waitForResource' :  MCancel (Elin World)
                     => TMVar1 World (Maybe a)
                     -> Stripe1 World a
                     -> Elin World [Errno] (Maybe a)
    waitForResource' q mstripe =
      onAbort (runIO (takeTMVar1 q)) (runIO (cleanup' q mstripe))

||| Destroy a resource.
||| Note that this will ignore any exceptions.
export
destroyResource :  Pool1 World a
                -> LocalPool1 World a
                -> a
                -> F1' World
destroyResource pool lp x t =
  let res # t := ioToF1 (runElinIO (destroy pool lp x)) t
    in case res of
         Right _  =>
           () # t
         Left err =>
          (assert_total $ idris_crash "Data.Pool.destroyResource: \{show err}") # t
  where
    destroy' :  LocalPool1 World a
             -> F1' World
    destroy' lp@(MkLocalPool1 _ stripe@(MkStripe1 stripevar) _) t =
      let MkStripe1 stripevar' # t := signal stripe Nothing t
          stripevar''          # t := read1 stripevar' t
        in casupdate1 stripevar (\_ =>
                                  (stripevar'', ())
                                ) t
    destroy :  MCancel (Elin World)
            => Pool1 World a
            -> LocalPool1 World a
            -> a
            -> Elin World [Errno] ()
    destroy (MkPool1 (MkPoolConfig _ freeresource _ _ _ _) _ _) lp x =
      uncancelable $ \_ => do
        runIO (destroy' lp)
        liftIO (freeresource x)

||| Return a resource to the given `LocalPool1 World a`.
export
putResource :  LocalPool1 World a
            -> a
            -> F1' World
putResource (MkLocalPool1 _ stripe@(MkStripe1 stripevar) _) x t =
  let MkStripe1 stripevar' # t := signal stripe (Just x) t
      stripevar''          # t := read1 stripevar' t
    in casupdate1 stripevar (\_ =>
                              (stripevar'', ())
                            ) t

||| Free resource entries in the stripes that fulfill a given condition.
private
cleanStripe :  (Entry a -> Bool)
            -> (a -> IO ())
            -> Stripe1 World a
            -> F1' World
cleanStripe isstale free (MkStripe1 stripevar) t =
  let res # t := ioToF1 (runElinIO (clean isstale free (MkStripe1 stripevar))) t
    in case res of
         Right _ =>
           () # t
         Left err =>
           (assert_total $ idris_crash "Data.Pool.cleanStripe: \{show err}") # t
  where
    clean' :  (Entry a -> Bool)
           -> (a -> IO ())
           -> Stripe1 World a
           -> F1' World
    clean' isstale free (MkStripe1 stripevar) t =
      let (MkStripe available cache queue queuer) # t := read1 stripevar t
          (stale, fresh)                              := partition isstale cache
          ()                                      # t := casupdate1 stripevar (\(MkStripe available _ queue queuer) =>
                                                                                (MkStripe available fresh queue queuer, ())
                                                                              ) t
        in traverse1_ (\(MkEntry e _) => ioToF1 (free e)) stale t
    clean :  MCancel (Elin World)
          => (Entry a -> Bool)
          -> (a -> IO ())
          -> Stripe1 World a
          -> Elin World [Errno] ()
    clean isstale free (MkStripe1 stripevar) =
      uncancelable $ \_ =>
        runIO (clean' isstale free (MkStripe1 stripevar))

||| Destroy all resources in all stripes in the `Pool1 s a`.
|||
||| Note that this will ignore any exceptions in the destroy function.
|||
||| This function is useful when you detect that all resources in the pool are
||| broken. For example after a database has been restarted all connections
||| opened before the restart will be broken. In that case it's better to close
||| those connections so that 'takeResource' won't take a broken connection from
||| the pool but will open a new connection instead.
|||
||| Another use-case for this function is that when you know you are done with
||| the pool you can destroy all idle resources immediately instead of waiting on
||| the garbage collector to destroy them, thus freeing up those resources
||| sooner.
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

{-
private
takeAvailableResource :  Pool1 World a
                      -> LocalPool1 World a
                      -> Stripe1 World a
                      -> F1 World (a, LocalPool1 World a)
takeAvailableResource pool lp stripe t =
-}

{-
||| Take a resource from the `Pool1 World a`, following the same
||| results as `withResource`.
export
takeResource :  Pool1 World a
             -> IO (a, LocalPool1 World a)
takeResource pool = do
  Right res <- runElinIO (takeResource' pool)
    | Left err =>
        assert_total $ idris_crash "Data.Pool.takeResource: \{show err}"
  pure res
  where
    clean' :  (Entry a -> Bool)
           -> (a -> IO ())
           -> Stripe1 World a
           -> F1' World
    clean' isstale free (MkStripe1 stripevar) t =
      let (MkStripe available cache queue queuer) # t := read1 stripevar t
          (stale, fresh)                              := partition isstale cache
          ()                                      # t := casupdate1 stripevar (\(MkStripe available _ queue queuer) =>
                                                                                (MkStripe available fresh queue queuer, ())
                                                                              ) t
        in traverse1_ (\(MkEntry e _) => ioToF1 (free e)) stale t
    takeResource' :  MCancel (Elin World)
                  => (Entry a -> Bool)
                  -> (a -> IO ())
                  -> Stripe1 World a
                  -> Elin World [Errno] ()
    takeResource' (MkPool1 (MkPoolConfig _ freeresource _ _ _ _) _ _) localpools =
      uncancelable $ \_ =>
        runIO (clean' isstale free (MkStripe1 stripevar))
-}
