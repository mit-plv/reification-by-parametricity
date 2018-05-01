Require Export Reify.Benchmarks.Stats.

Goal True.
  do_test_Stats true slow.
  do_test_Stats false slow.
Abort.
