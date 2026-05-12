module Main

import AcquireRelease
import DestroyAllResources
import IdleCleanup
import MaxResourcesBound
import WaiterResume

main : IO ()
main = do
  () <- test_basicAcquireRelease
  () <- test_destroyAllResources
  () <- test_maxResourcesBound
  () <- test_idleCleanup
  test_waiterResume
