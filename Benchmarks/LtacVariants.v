Require Export Reify.BenchmarkScaffolding.
Require Export
        Reify.LtacTCPrimPair Reify.LtacTCGallinaCtx Reify.LtacTCExplicitCtx
        Reify.LtacTacInTermPrimPair Reify.LtacTacInTermGallinaCtx Reify.LtacTacInTermExplicitCtx.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 6 * 1000
     | medium, true => 30 * 1000
     | quick, false => 300
     | medium, false => 2 * 1000
     | slow, _ => 30 * 1000
     end.

Ltac do_test_LtacVariants is_flat speed :=
  scaffold_test
    ltac:(fun big n refP
          => do_test_with "LtacTCPrimPair" big (do_cbv) (noop) (LtacTCPrimPair.do_Reify_rhs) (LtacTCPrimPair.post_Reify_rhs) n refP;
             do_test_with "LtacTCGallinaCtx" big (do_cbv) (noop) (LtacTCGallinaCtx.do_Reify_rhs) (LtacTCGallinaCtx.post_Reify_rhs) n refP;
             do_test_with "LtacTCExplicitCtx" big (do_cbv) (noop) (LtacTCExplicitCtx.do_Reify_rhs) (LtacTCExplicitCtx.post_Reify_rhs) n refP;
             do_test_with "LtacTacInTermPrimPair" big (do_cbv) (noop) (LtacTacInTermPrimPair.do_Reify_rhs) (LtacTacInTermPrimPair.post_Reify_rhs) n refP;
             do_test_with "LtacTacInTermGallinaCtx" big (do_cbv) (noop) (LtacTacInTermGallinaCtx.do_Reify_rhs) (LtacTacInTermGallinaCtx.post_Reify_rhs) n refP;
             do_test_with "LtacTacInTermExplicitCtx" big (do_cbv) (noop) (LtacTacInTermExplicitCtx.do_Reify_rhs) (LtacTacInTermExplicitCtx.post_Reify_rhs) n refP;
             idtac
         ) max_n is_flat speed.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_LtacVariants true test.
  Redirect "/tmp/silence" do_test_LtacVariants false test.
Abort.
