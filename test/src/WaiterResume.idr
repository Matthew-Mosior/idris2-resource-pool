module WaiterResume

import Types
import Utils

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Posix.Time

private
incCreated : TestStats -> IO ()
incCreated stats =
  runIO (casmod1 stats.created (`plus` 1))

export
test_waiterResume : IO ()
test_waiterResume = do
  stats <- newTestStats
  let create : IO TestResource
      create = do
        incCreated stats
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
          "waiter-resume"
  pool <- runIO (newPool 1 cfg)
  case pool of
    Left errs   =>
      die "Error creating new pool"
    Right pool' => do
      thread1done <- newref False
      thread2done <- newref False
      tid1 <-
        fork $ do
          withr <-
            runIO $
              withResource pool' $ \_ => do
                usleep 300000
          case withr of
            Left  _ =>
              die "Error calling withResource"
            Right _ =>
              writeref thread1done True
      -- ensure thread1 acquires first
      usleep 50000
      tid2 <-
        fork $ do
          withr <-
            runIO $
              withResource pool' $ \_ => do
                pure ()
          case withr of
            Left  _ =>
              die "Error calling withResource"
            Right _ =>
              writeref thread2done True
      threadWait tid1
      threadWait tid2
      d1 <- readref thread1done
      d2 <- readref thread2done
      created <- readref stats.created
      when (d1 /= True) $
        die "thread1 did not finish"
      when (d2 /= True) $
        die "thread2 did not resume"
      when (created /= 1) $
        die "expected exactly one created resource"
