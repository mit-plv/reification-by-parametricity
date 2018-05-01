Require Export Reify.Benchmarks.Ltac2.

Goal True.
  do_test_Ltac2 true medium.
  do_test_Ltac2 false medium.
Abort.
