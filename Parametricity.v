(** * Reification by parametricity *)
Require Import Reify.ReifyCommon.

Ltac Reify x :=
  let rx := lazymatch (eval pattern nat, O, S, Nat.mul, (@Let_In nat nat) in x) with
            | ?rx _ _ _ _ _ => rx end in
  let rx := lazymatch rx with fun N : Set => ?rx => constr:(fun N : Type => rx) end in
  let __ := type of rx in (* propagate universe constraints, c.f., https://github.com/coq/coq/issues/5996 *)
  constr:(fun var : Type => rx (@expr var) (@NatO var) (@NatS var) (@NatMul var)
                               (fun x' f' => @LetIn var x' (fun v => f' (@Var var v)))).

Ltac reify var x :=
  let rx := Reify x in
  constr:(rx var).

Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
