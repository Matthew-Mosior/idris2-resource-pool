module MaxResourcesBound

import Types

import Data.Linear.Ref1
import Data.List
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

private
incFreed : TestStats -> IO ()
incFreed stats =
  runIO (casmod1 stats.freed (`plus` 1))

private
resourceEnter : TestStats -> IO ()
resourceEnter stats = do
  runIO (casmod1 stats.active (`plus` 1))
  a <- readref stats.active
  m <- readref stats.maxseen
  when (a > m) $
    writeref stats.maxseen a

private
resourceExit : TestStats -> IO ()
resourceExit stats =
  runIO (casmod1 stats.active pred)

export
test_maxResourcesBound : IO ()
test_maxResourcesBound = do
  stats  <- newTestStats
  nextid <- newref 0
  let create : IO TestResource
      create = do
        incCreated stats
        rid <- runIO (casupdate1 nextid (\x => (S x, x)))
        pure (MkTestResource rid)
      free : TestResource -> IO ()
      free _ = pure ()
      cfg : PoolConfig TestResource
      cfg =
        MkPoolConfig
          create
          free
          (duration 60 0)
          (4 ** LTESucc LTEZero)
          (2 ** (LTESucc LTEZero,
                  LTESucc (LTESucc LTEZero)))
          "bound"
  pool <- runIO (newPool 2 cfg)
  tids <- for (replicate 50 ()) $ \n =>
            fork $ do
              runIO $
                withResource pool $ \_ => do
                  resourceEnter stats
                  usleep 10000
                  resourceExit stats
  for_ tids $ \tid =>
    threadWait tid
  peak <- readref stats.maxseen
  totalresources <- readref stats.created
  when (peak > 4) $
    assert_total $
      idris_crash ("resource limit exceeded: " ++ show peak)
  when (totalresources > 4) $
    assert_total $
      idris_crash ("created too many resources: " ++ show totalresources)
