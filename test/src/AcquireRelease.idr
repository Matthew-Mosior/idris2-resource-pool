module AcquireRelease

import Types

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Posix.Time

export
test_basicAcquireRelease : IO ()
test_basicAcquireRelease = do
  created <- newref 0
  freed   <- newref 0
  let create : IO TestResource
      create = do
        runIO (casmod1 created (`plus` 1))
        pure (MkTestResource 0)
      free : TestResource -> IO ()
      free _ = runIO (casmod1 freed (`plus` 1))
      cfg : PoolConfig TestResource
      cfg =
        MkPoolConfig
          create
          free
          (duration 60 0)
          (1 ** LTESucc LTEZero)
          (1 ** (LTESucc LTEZero, LTESucc LTEZero))
          "basic"
  pool <- runIO (newPool 1 cfg)
  case pool of
    Left errs   =>
      die "Error creating new pool"
    Right pool' => do
      withr <- runIO $ withResource pool' (\_ => pure ())
      case withr of
        Left _   =>
          die "Error calling withResource"
        Right _  => do
          withr' <- runIO $ withResource pool' (\_ => pure ())
          case withr' of
            Left _   =>
              die "Error calling withResource"
            Right _  => do
              c <- readref created
              f <- readref freed
              when (c /= 1) $
                die "test_basicAcquireRelease: expected exactly one created resource"
              when (f /= 0) $
                die "test_basicAcquireRelease: expected zero freed resources"
