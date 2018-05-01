Require Export Reify.Benchmarks.Mtac2.

Goal True.
  do_test_Mtac2 true slow.
  do_test_Mtac2 false slow.
Abort.
