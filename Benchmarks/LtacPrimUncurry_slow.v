Require Export Reify.Benchmarks.LtacPrimUncurry.

Goal True.
  do_test_LtacPrimUncurry true slow.
  do_test_LtacPrimUncurry false slow.
Abort.
