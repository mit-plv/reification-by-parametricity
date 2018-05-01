Require Export Reify.BenchmarkScaffolding.
Require Export Reify.OCaml.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed with
     | _ => 30 * 1000
     end.

Ltac do_test_OCaml is_flat speed :=
  scaffold_test ltac:(fun big n refP => do_test_with "OCaml" big (do_cbv) (noop) (OCaml.do_Reify_rhs) (OCaml.post_Reify_rhs) n refP) max_n is_flat speed.


Goal True. (* test *)
  Redirect "/tmp/silence" do_test_OCaml true test.
  Redirect "/tmp/silence" do_test_OCaml false test.
Abort.
