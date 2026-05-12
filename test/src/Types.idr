module Types

import Data.Linear.Ref1

public export
record TestResource where
  constructor MkTestResource
  rid : Nat

public export
record TestStats where
  constructor MkTestStats
  created  : IORef Nat
  freed    : IORef Nat
  active   : IORef Nat
  maxseen  : IORef Nat
