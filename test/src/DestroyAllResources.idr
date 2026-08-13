module DestroyAllResources

import Types

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Posix.Time

export
test_destroyAllResources : IO ()
test_destroyAllResources = do
  created <- newref 0
  freed   <- newref 0
  let create : IO TestResource
      create = do
        runIO (casmod1 created (`plus` 1))
        pure (MkTestResource 0)
      free : TestResource -> IO ()
      free _ =
        runIO (casmod1 freed (`plus` 1))
      cfg : PoolConfig TestResource
      cfg =
        MkPoolConfig
          create
          free
          (duration 60 0)
          (2 ** LTESucc LTEZero)
          (1 ** (LTESucc LTEZero, LTESucc LTEZero))
          "destroy"
  pool <- runIO (newPool 1 cfg)
  case pool of
    Left errs   =>
      die "Error creating new pool"
    Right pool'@(MkPool1 _ pools _) => do
      -- create + cache one resource
      withr <- runIO $ withResource pool' (\_ => pure ())
      case withr of
        Left ()  =>
          die "Error calling withResource"
        Right _  => do
          withr' <- runIO $ withResource pool' (\_ => pure ())
          case withr' of
            Left ()  =>
              die "Error calling withResource"
            Right _  => do
              -- destroy idle cache
              runIO $ destroyAllResources pool' pools
              -- must still work afterwards
              withr'' <- runIO $ withResource pool' (\_ => pure ())
              case withr'' of
                Left ()  =>
                  die "Error calling withResource"
                Right _  => do
                  c <- readref created
                  f <- readref freed
                  when (c /= 2) $
                    die "expected resource recreation after destroy"
                  when (f /= 1) $
                    die "expected exactly one freed resource"
