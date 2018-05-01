Require Export Reify.Benchmarks.QuoteFlat.

Goal True.
  do_test_QuoteFlat true slow.
  do_test_QuoteFlat false slow.
Abort.
