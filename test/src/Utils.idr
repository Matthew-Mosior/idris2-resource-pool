module Utils

import Types

import Data.Linear.Ref1

export
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
