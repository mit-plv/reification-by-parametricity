Require Export Reify.Benchmarks.Printing.

Goal True.
  do_test_Printing true slow.
  do_test_Printing false slow.
Abort.
