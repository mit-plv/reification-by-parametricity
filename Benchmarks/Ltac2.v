Require Export Reify.BenchmarkScaffolding.
Require Export Reify.Ltac2 Reify.Ltac2LowLevel.

Definition max_n_low_level (is_flat : bool) (speed : speed_classifier) : nat
  := match speed with
     | _ => 30 * 1000
     end.
Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 300
     | medium, false => 1450
     | slow, _ => 30 * 1000
     end.

Ltac do_test_Ltac2 is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "Ltac2LowLevel" big (do_cbv) (noop) (Ltac2LowLevel.do_Reify_rhs) (Ltac2LowLevel.post_Reify_rhs) n refP) max_n_low_level is_flat speed;
  scaffold_test ltac:(fun big n refP => do_test_with "Ltac2" big (do_cbv) (noop) (Ltac2.do_Reify_rhs) (Ltac2.post_Reify_rhs) n refP) max_n is_flat speed;
  idtac.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_Ltac2 true test.
  Redirect "/tmp/silence" do_test_Ltac2 false test.
Abort.
