module ResourceLocality

import Types
import Utils

import Data.Linear.Ref1
import Data.Nat
import Data.Pool
import System
import System.Posix.Time

export
test_resourceLocality : IO ()
test_resourceLocality = do
  nextId <- newref 0
  let create : IO TestResource
      create = do
        rid <- readref nextId
        writeref nextId (rid + 1)
        pure (MkTestResource rid)
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
          "resource-locality"
  pool <- runIO (newPool 4 cfg)
  observations <- for [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] $ \_ => do
    (r@(MkTestResource rid), MkLocalPool1 sid stripe _) <- runIO (takeResource pool)
    runIO (putResource pool stripe r)
    pure (sid, rid)
  case observations of
    []                                      =>
      pure ()
    ((expectedstripe, expectedrid) :: rest) =>
      for_ rest $ \(sid, rid) =>
        when (sid /= expectedstripe || rid /= expectedrid) $
          assert_total $ idris_crash ("locality violation: " ++ show observations)
