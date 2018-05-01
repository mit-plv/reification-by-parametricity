Require Export Reify.Benchmarks.Parametricity.

Goal True.
  do_test_Parametricity true slow.
  do_test_Parametricity false slow.
Abort.
