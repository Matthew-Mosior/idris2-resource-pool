module WaiterResume

import Types

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Posix.Time

private
newTestStats : IO TestStats
newTestStats = do
  created <- newref 0
  freed   <- newref 0
  active  <- newref 0
  maxseen <- newref 0
  pure $
    MkTestStats
      created
      freed
      active
      maxseen

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
  thread1done <- newref False
  thread2done <- newref False
  tid1 <-
    fork $ do
      runIO $
        withResource pool $ \_ => do
          usleep 300000
      writeref thread1done True
  -- ensure thread1 acquires first
  usleep 50000
  tid2 <-
    fork $ do
      runIO $
        withResource pool $ \_ => do
          pure ()
      writeref thread2done True
  threadWait tid1
  threadWait tid2
  d1 <- readref thread1done
  d2 <- readref thread2done
  created <- readref stats.created
  when (d1 /= True) $
    assert_total $ idris_crash "thread1 did not finish"
  when (d2 /= True) $
    assert_total $ idris_crash "thread2 did not resume"
  when (created /= 1) $
    assert_total $ idris_crash "expected exactly one created resource"
