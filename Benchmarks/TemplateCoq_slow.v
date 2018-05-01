Require Export Reify.Benchmarks.TemplateCoq.

Goal True.
  do_test_TemplateCoq true slow.
  do_test_TemplateCoq false slow.
Abort.
