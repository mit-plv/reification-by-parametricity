Require Export Reify.BenchmarkScaffolding.
Require Export Reify.QuoteFlat.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 30 * 1000
     | medium, true => 30 * 1000
     | _, false => 0
     | slow, _ => 30 * 1000
     end.

Ltac do_test_QuoteFlat is_flat speed :=
  lazymatch is_flat with
  | true
    =>
    scaffold_test ltac:(fun big n refP => do_test_with "QuoteFlat" big (do_cbv) (noop) (QuoteFlat.do_Reify_rhs) (QuoteFlat.post_Reify_rhs) n refP) max_n is_flat speed;
    idtac
  | false => idtac
  end.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_QuoteFlat true test.
  Redirect "/tmp/silence" do_test_QuoteFlat false test.
Abort.
