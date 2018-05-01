Require Export Reify.BenchmarkScaffolding.
Require Export Reify.Parametricity.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed with
     | _ => 30 * 1000
     end.
Definition max_n_reif_after_beta (is_flat : bool) (speed : speed_classifier) : nat
  := match speed with
     | quick => 5 * 1000
     | medium => 30 * 1000
     | slow => 30 * 1000
     end.

Ltac do_test_Parametricity is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "Parametricity; beta" big (do_cbv_delta) (noop) (Parametricity.do_Reify_rhs) (Parametricity.post_Reify_rhs) n refP) max_n is_flat speed;
  scaffold_test ltac:(fun big n refP => do_test_with "beta; Parametricity" big (do_cbv) (noop) (Parametricity.do_Reify_rhs) (Parametricity.post_Reify_rhs) n refP) max_n_reif_after_beta is_flat speed;
  idtac.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_Parametricity true test.
  Redirect "/tmp/silence" do_test_Parametricity false test.
Abort.
