Require Export Reify.Benchmarks.Parametricity.

Goal True.
  do_test_Parametricity true quick.
  do_test_Parametricity false quick.
Abort.
