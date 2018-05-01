Require Export Reify.Benchmarks.Ltac2.

Goal True.
  do_test_Ltac2 true slow.
  do_test_Ltac2 false slow.
Abort.
