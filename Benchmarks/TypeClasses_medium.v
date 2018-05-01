Require Export Reify.Benchmarks.TypeClasses.

Goal True.
  do_test_TypeClasses true medium.
  do_test_TypeClasses false medium.
Abort.
