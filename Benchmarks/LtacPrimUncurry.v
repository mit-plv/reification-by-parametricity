Require Export Reify.BenchmarkScaffolding.
Require Export Reify.LtacPrimUncurry.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 175
     | medium, false => 700
     | slow, _ => 30 * 1000
     end.

Ltac do_test_LtacPrimUncurry is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "LtacPrimUncurry" big (do_cbv) (noop) (LtacPrimUncurry.do_Reify_rhs) (LtacPrimUncurry.post_Reify_rhs) n refP) max_n is_flat speed.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_LtacPrimUncurry true test.
  Redirect "/tmp/silence" do_test_LtacPrimUncurry false test.
Abort.
