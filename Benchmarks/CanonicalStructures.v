Require Export Reify.BenchmarkScaffolding.
Require Export
        Reify.CanonicalStructuresFlatHOAS
        Reify.CanonicalStructuresFlatPHOAS
        Reify.CanonicalStructuresHOAS
        Reify.CanonicalStructuresPHOAS.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 60
     | medium, false => 200
     | slow, _ => 30 * 1000
     end.

Ltac do_test_CanonicalStructures is_flat speed :=
  lazymatch is_flat with
  | true
    =>
    scaffold_test
      ltac:(fun big n refP
            => do_test_with "CanonicalStructuresFlatHOAS" big (do_cbv) (CanonicalStructuresFlatHOAS.pre_Reify_rhs) (CanonicalStructuresFlatHOAS.do_Reify_rhs) (CanonicalStructuresFlatHOAS.post_Reify_rhs) n refP;
               do_test_with "CanonicalStructuresFlatPHOAS" big (do_cbv) (CanonicalStructuresFlatPHOAS.pre_Reify_rhs) (CanonicalStructuresFlatPHOAS.do_Reify_rhs) (CanonicalStructuresFlatPHOAS.post_Reify_rhs) n refP;
               idtac)
             max_n is_flat speed;
    idtac
  | false => idtac
  end;
  scaffold_test
    ltac:(fun big n refP
          => do_test_with "CanonicalStructuresHOAS" big (do_cbv) (CanonicalStructuresHOAS.pre_Reify_rhs) (CanonicalStructuresHOAS.do_Reify_rhs) (CanonicalStructuresHOAS.post_Reify_rhs) n refP;
             do_test_with "CanonicalStructuresPHOAS" big (do_cbv) (CanonicalStructuresPHOAS.pre_Reify_rhs) (CanonicalStructuresPHOAS.do_Reify_rhs) (CanonicalStructuresPHOAS.post_Reify_rhs) n refP;
             idtac)
           max_n is_flat speed;
  idtac.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_CanonicalStructures true test.
  Redirect "/tmp/silence" do_test_CanonicalStructures false test.
Abort.
