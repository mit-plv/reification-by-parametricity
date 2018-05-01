Require Export Reify.BenchmarkScaffolding.
Require Export Reify.TypeClasses
        Reify.TypeClassesBodyFlatPHOAS
        Reify.TypeClassesBodyHOAS.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 85
     | medium, false => 300
     | slow, _ => 30 * 1000
     end.

Definition max_n_HOAS (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 375
     | medium, false => 2 * 1000
     | slow, _ => 30 * 1000
     end.

Ltac do_test_TypeClasses is_flat speed :=
  scaffold_test
    ltac:(fun big n refP
          => lazymatch is_flat with
             | true
               =>
               do_test_with "TypeClassesBodyFlatPHOAS" big (do_cbv) (noop) (TypeClassesBodyFlatPHOAS.do_Reify_rhs) (TypeClassesBodyFlatPHOAS.post_Reify_rhs) n refP
             | false => idtac
             end;
             do_test_with "TypeClasses" big (do_cbv) (noop) (TypeClasses.do_Reify_rhs) (TypeClasses.post_Reify_rhs) n refP;
             idtac)
           max_n is_flat speed;
  scaffold_test
    ltac:(fun big n refP
          => do_test_with "TypeClassesBodyHOAS" big (do_cbv) (noop) (TypeClassesBodyHOAS.do_Reify_rhs) (TypeClassesBodyHOAS.post_Reify_rhs) n refP)
           max_n_HOAS is_flat speed;
  idtac.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_TypeClasses true test.
  Redirect "/tmp/silence" do_test_TypeClasses false test.
Abort.
