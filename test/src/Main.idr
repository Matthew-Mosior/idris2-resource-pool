module Main

import AcquireRelease
import DestroyAllResources
import FIFO
import IdleCleanup
import MaxResourcesBound
import StripeLocality
import WaiterResume
import WakeCreateHandoff

main : IO ()
main = do
  () <- test_basicAcquireRelease
  () <- test_destroyAllResources
  () <- test_maxResourcesBound
  () <- test_idleCleanup
  () <- test_waiterResume
  () <- test_fifo
  () <- test_stripeLocality
  test_wakeCreateHandoff
