Require Export Reify.Benchmarks.TemplateCoq.

Goal True.
  do_test_TemplateCoq true quick.
  do_test_TemplateCoq false quick.
Abort.
