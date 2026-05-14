module FIFO

import Types

import Data.Linear.Ref1
import Data.List
import Data.Nat
import Data.Pool
import System
import System.Concurrency
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
test_fifo : IO ()
test_fifo = do
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
          "fifo"
  pool <- runIO (newPool 1 cfg)
  (r, lp@(MkLocalPool1 _ stripe _)) <- runIO (takeResource pool)
  orderref <- newref []
  starts <- traverse (\_ => makeChannel) [0,1,2,3,4,5,6,7,8,9]
  for_ (zip [0,1,2,3,4,5,6,7,8,9] starts) $ \(i, start) =>
    fork $ do
     channelGet start
     (r2, _) <- runIO (takeResource pool)
     runIO (casmod1 orderref (\xs => (xs ++ [i])))
     runIO (putResource pool stripe r2)
  -- deterministically enqueue in order
  for_ starts $ \start => do
    channelPut start ()
    usleep 10
  -- release initial resource
  runIO (putResource pool stripe r)
  sleep 1
  result <- readref orderref
  when (result /= (the (List Nat) [0,1,2,3,4,5,6,7,8,9])) $
    assert_total $ idris_crash "out of order: \{show result}"
