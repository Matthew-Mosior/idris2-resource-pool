module FIFO

import Types
import Utils

import Data.Linear.Ref1
import Data.List
import Data.Nat
import Data.Pool
import System
import System.Concurrency
import System.Posix.Time

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
  case pool of
    Left errs   =>
      die "Error creating new pool"
    Right pool' => do
      taker <- runIO (takeResource pool')
      case taker of
        Left _                                =>
          die "Error calling takeResource"
        Right (r, lp@(MkLocalPool1 _ stripe)) => do
          orderref <- newref []
          starts <- traverse (\_ => makeChannel) [0,1,2,3,4,5,6,7,8,9]
          for_ (zip [0,1,2,3,4,5,6,7,8,9] starts) $ \(i, start) =>
            fork $ do
             channelGet start
             taker' <- runIO (takeResource pool')
             case taker' of
               Left _        =>
                 die "Error calling takeResource"
               Right (r2, _) => do
                 runIO (casmod1 orderref (\xs => (xs ++ [i])))
                 putr <- runIO (putResource pool' stripe r2)
                 case putr of
                   Left  _ =>
                     die "Error calling putResource"
                   Right _ =>
                     pure ()
          -- deterministically enqueue in order
          for_ starts $ \start => do
            channelPut start ()
            usleep 10
          -- release initial resource
          putr <- runIO (putResource pool' stripe r)
          case putr of
            Left  _ =>
              die "Error calling putResource"
            Right _ => do
              sleep 1
              result <- readref orderref
              when (result /= (the (List Nat) [0,1,2,3,4,5,6,7,8,9])) $
                die "out of order: \{show result}"
