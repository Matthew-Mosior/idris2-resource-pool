module IdleCleanup

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

private
incFreed : TestStats -> IO ()
incFreed stats =
  runIO (casmod1 stats.freed (`plus` 1))

export
test_idleCleanup : IO ()
test_idleCleanup = do
  stats  <- newTestStats
  nextid <- newref 0
  let create : IO TestResource
      create = do
        incCreated stats
        rid <- runIO (casupdate1 nextid (\x => (S x, x)))
        pure (MkTestResource rid)
      free : TestResource -> IO ()
      free _ =
        incFreed stats
      cfg : PoolConfig TestResource
      cfg =
        MkPoolConfig
          create
          free
          -- very short TTL
          (duration 0 100000)
          (1 ** LTESucc LTEZero)
          (1 ** (LTESucc LTEZero,
                  LTESucc LTEZero))
          "idle-cleanup"
  pool <- runIO (newPool 1 cfg)
  case pool of
    Left errs   =>
      die "Error creating new pool"
    Right pool' => do
      -- create + cache resource
      withr <- runIO (withResource pool' (\_ => pure ()))
      case withr of
        Left () =>
          die "Error calling withResource"
        Right _ => do
          c1 <- readref stats.created
          f1 <- readref stats.freed
          when (c1 /= 1) $
            assert_total $
              idris_crash "expected one created resource"
          when (f1 /= 0) $
            assert_total $
              idris_crash "expected zero freed resources"
          -- wait beyond TTL
          usleep 300000
          -- trigger cleanup path
          withr' <- runIO (withResource pool' (\_ => pure ()))
          case withr' of
            Left () =>
              die "Error calling withResource"
            Right _ => do
              c2 <- readref stats.created
              f2 <- readref stats.freed
              -- old resource should have been evicted
              when (f2 /= 1) $
                die "expected one freed idle resource"
              -- new resource should have been created
              when (c2 /= 2) $
                die "expected resource recreation after idle cleanup"
