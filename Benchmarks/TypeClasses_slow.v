Require Export Reify.Benchmarks.TypeClasses.

Goal True.
  do_test_TypeClasses true slow.
  do_test_TypeClasses false slow.
Abort.
