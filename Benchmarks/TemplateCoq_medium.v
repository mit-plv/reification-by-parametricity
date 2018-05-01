Require Export Reify.Benchmarks.TemplateCoq.

Goal True.
  do_test_TemplateCoq true medium.
  do_test_TemplateCoq false medium.
Abort.
