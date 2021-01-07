Require Export Reify.BenchmarkScaffolding.
Require Export Reify.Mtac2Unfolded.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 300
     | medium, false => 2 * 1000
     | _, _ => 30 * 1000
     end.

Ltac do_test_Mtac2Unfolded is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "Mtac2Unfolded" big (do_cbv) (noop) (Mtac2Unfolded.do_Reify_rhs) (Mtac2Unfolded.post_Reify_rhs) n refP) max_n is_flat speed.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_Mtac2Unfolded true test.
  Redirect "/tmp/silence" do_test_Mtac2Unfolded false test.
Abort.
