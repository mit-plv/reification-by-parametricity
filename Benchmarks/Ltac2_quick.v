Require Export Reify.Benchmarks.Ltac2.

Goal True.
  do_test_Ltac2 true quick.
  do_test_Ltac2 false quick.
Abort.
