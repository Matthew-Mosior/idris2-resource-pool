# Test Suite

This resource pool implementation has several major correctness properties:

1. Resource conservation
   - Resources are never duplicated.
   - Resources are never leaked.
   - Total live resources never exceed capacity.
2. FIFO waiter fairness
   - Blocked waiters resume in enqueue order.
3.  Wakeup correctness.
   - Wakeups are not lost.
   - Cancelled waiters do not consume wakeups.
   - Wake/Create semantics are correct.
4. Stripe locality
   - Threads consistently hit the same stripe.
   - Cached resources remain local to their stripe.
5. Cleanup correctness
   - Idle resources eventually free.
   - Cleanup never frees live resources.
6. CAS/effect correctness
   - Side effects execute exactly once.
   - Retries never duplicate effects.

Each test isolates and verifies one of the above properties.

## test_basicAcquireRelease

This is the foundational sanity test that verifies:
- Resource reuse.
- Cache insertion.
- No unnecessary frees.
- Basic acquire/release lifecycle.

## test_destroyAllResources

This validates explicit cache destruction:
- Cached resources are actually freed.
- Only idle resources are destroyed.
- Pool remains usable afterward.
- Resource recreation works after destruction.

## test_fifo

This is one of the most important tests in the suite, as it verifies the fairness of the waiter queue:
- FIFO waiter ordering.
- Enqueue ordering correctness.
- CAS queue semantics.
- Dequeue correctness.
- Wake ordering correctness.
- Absence of scheduler-induced reordering.

## test_idleCleanup

This validates TTL-based cleanup, as it verifies:
- Stale resource eviction.
- Cleanup correctness.
- Cleanup triggering.
- Free-after-CAS semantics.
- Recreation after eviction.

## test_maxResourcesBound

This validates the one of the single most important safety properties, as it verifies that the pool **never** exceeds maxresources, even under heavy concurrency.

## test_resourceLocality

This validates stripe-local resource reuse, which is extremely important for scalability, and it verifies:
- Returned resources stay on their stripe.
- Same thread repeatedly sees same resource.
- No cross-stripe migration.
- Cache locality works.

## test_stripeLocality

This validates deterministic thread-to-stripe mapping:
- Stable stripe hashing.
- Deterministic thread assignment.
- Thread affinity to stripe.

## test_waiterResume

This validates waiter wakeup correctness, as it verifies:
- Blocked waiter resumes.
- Waiter receives returned resource.
- No extra creation occurs.
- Wakeup path works.

## test_wakeCreateHandoff

This is one of the most subtle tests, since it validates the `Create` wake protocol, as it verifies:
- Destroyed resources restore creation ability.
- Waiters wake with `Create`.
- Waiters correctly create replacement resources.
- No deadlock after destruction.
