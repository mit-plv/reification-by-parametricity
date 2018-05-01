Require Export Reify.Benchmarks.Parametricity.

Goal True.
  do_test_Parametricity true medium.
  do_test_Parametricity false medium.
Abort.
