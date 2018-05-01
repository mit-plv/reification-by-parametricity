(** * Reification in OCaml *)
Require Import Reify.ReifyCommon.
Require Import Reify.OCamlReify.
(** See [OCamlReify.v] and [reify_plugin.ml4] for the implementation code. *)

Ltac Reify_cps term tac :=
  quote_term_cps
    [var, Type] (@Var) (@NatO) (@NatS) (@NatMul) (@LetIn) O S Nat.mul (@Let_In)
    term tac.

Ltac reify_cps var term tac :=
  Reify_cps term ltac:(fun rt => tac (rt var)).

Ltac do_Reify_rhs _ := do_Reify_rhs_of_cps Reify_cps ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of_cps Reify_cps ().
