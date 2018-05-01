Require Export Coq.Strings.String.
Require Export Reify.BenchmarkScaffolding.
Require Export Reify.PHOAS.

Global Set Printing Width 1000000.
Global Notation "0" := NatO : expr_scope.
Global Notation "1" := (NatS 0) : expr_scope.

Definition max_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | _, true => 30 * 1000
     | quick, false => 300
     | medium, false => 2 * 1000
     | slow, _ => 30 * 1000
     end.

Global Open Scope string_scope.

Tactic Notation "do_printing_test" constr(name) constr(big) tactic3(do_print) constr(n) :=
  let n := (eval lazy in (nat_of_count n)) in
  once (
      idtac "Doing printing (n=" n ") for" name "with" big ":";
      once (time "printing" do_print ())
    ).

Ltac do_test_Printing is_flat speed :=
  scaffold_test
    ltac:(fun big n refP
          => do_printing_test
               "Printing" big
               (fun _ => idtac refP)
               n
         )
           max_n is_flat speed.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_Printing true test.
  Redirect "/tmp/silence" do_test_Printing false test.
Abort.
