Require Export Reify.Benchmarks.LtacVariants.

Goal True.
  do_test_LtacVariants true slow.
  do_test_LtacVariants false slow.
Abort.
