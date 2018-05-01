Require Export Reify.BenchmarkScaffolding.
Require Export Reify.TemplateCoq.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match is_flat with
     | false => 9 * 1000 (* 10000 stack overflows *)
     | true => 30 * 1000
     end.

Ltac do_test_TemplateCoq is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "TemplateCoq" big (do_cbv) (noop) (TemplateCoq.do_Reify_rhs) (TemplateCoq.post_Reify_rhs) n refP) max_n is_flat speed.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_TemplateCoq true test.
  Redirect "/tmp/silence" do_test_TemplateCoq false test.
Abort.
