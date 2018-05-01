Require Export Reify.Benchmarks.CanonicalStructures.

Goal True.
  do_test_CanonicalStructures true slow.
  do_test_CanonicalStructures false slow.
Abort.
