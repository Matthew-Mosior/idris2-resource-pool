module StripeLocality

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
test_stripeLocality : IO ()
test_stripeLocality = do
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
          (8 ** LTESucc LTEZero)
          (4 ** (LTESucc LTEZero,
                  LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))
          "locality"
  pool <- runIO (newPool 4 cfg)
  stripeids <- for [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] $ \_ => do
    (r, MkLocalPool1 sid stripe _) <- runIO (takeResource pool)
    runIO (putResource pool stripe r)
    pure sid
  case stripeids of
    []        =>
      pure ()
    (x :: xs) =>
      when (any (/= x) xs) $
        assert_total $ idris_crash ("stripe locality violated: " ++ show stripeids)
