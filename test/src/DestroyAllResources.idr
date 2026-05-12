module DestroyAllResources

import Types

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
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
  pool@(MkPool1 _ pools) <- runIO (newPool 1 cfg)
  -- create + cache one resource
  runIO $ withResource pool (\_ => pure ())
  runIO $ withResource pool (\_ => pure ())
  -- destroy idle cache
  runIO $ destroyAllResources pool pools
  -- must still work afterwards
  runIO $ withResource pool (\_ => pure ())
  c <- readref created
  f <- readref freed
  when (c /= 2) $
    assert_total $ idris_crash "expected resource recreation after destroy"
  when (f /= 1) $
    assert_total $ idris_crash "expected exactly one freed resource"
