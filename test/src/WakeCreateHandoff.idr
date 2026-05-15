module WakeCreateHandoff

import Types
import Utils

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Concurrency
import System.Posix.Time

export
test_wakeCreateHandoff : IO ()
test_wakeCreateHandoff = do
  createdref <- newref 0
  let create : IO TestResource
      create = do
        runIO (casmod1 createdref (`plus` 1))
        pure (MkTestResource 0)
      free : TestResource -> IO ()
      free _ = pure ()
      cfg : PoolConfig TestResource
      cfg =
        MkPoolConfig
          create
          free
          (duration 60 0)
          (1 ** LTESucc LTEZero)
          (1 ** (LTESucc LTEZero,
                  LTESucc LTEZero))
          "wake-create"
  pool <- runIO (newPool 1 cfg)
  -- exhaust pool
  (r1, MkLocalPool1 _ stripe _) <- runIO (takeResource pool)
  -- waiter coordination
  started <- makeChannel
  acquired <- newref False
  -- waiter thread
  tid <-
    fork $ do
      channelPut started ()
      (r2, _) <- runIO (takeResource pool)
      writeref acquired True
      runIO (putResource pool stripe r2)
  -- ensure waiter enqueued
  channelGet started
  usleep 10000
  -- destroy original resource
  runIO (destroyResource stripe)
  -- wait for thread
  threadWait tid
  -- waiter should wake via Create
  sleep 1
  acquiredresult <- readref acquired
  createdcount   <- readref createdref
  when (not acquiredresult) $
    assert_total $ idris_crash "waiter never acquired replacement resource"
  when (createdcount /= 2) $
    assert_total $ idris_crash ("unexpected create count: " ++ show createdcount)
