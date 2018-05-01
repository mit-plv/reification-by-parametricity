(** * Reification by the quote plugin *)
Require Import Coq.quote.Quote.
Require Import Reify.ReifyCommon.

Inductive qexpr : Set :=
| qNatO : qexpr
| qNatS : qexpr -> qexpr
| qNatMul (x y : qexpr)
| qConst (k : nat).

Module Export Exports.
  Fixpoint qdenote (e : qexpr) : nat
    := match e with
       | qNatO => O
       | qNatS x => S (qdenote x)
       | qNatMul x y => Nat.mul (qdenote x) (qdenote y)
       | qConst k => k
       end.
End Exports.

Fixpoint compile_nat {var} (n : nat) : @expr var
  := match n with
     | O => NatO
     | S x => NatS (compile_nat x)
     end.

Fixpoint compile {var} (e : qexpr) : @expr var
  := match e with
     | qNatO => NatO
     | qNatS x => NatS (compile x)
     | qNatMul x y => NatMul (compile x) (compile y)
     | qConst k => compile_nat k
     end.

Definition Compile (e : qexpr) : Expr := fun var => compile e.

Ltac reify_cps var term tac :=
  quote qdenote [S O] in term using
    (fun v => lazymatch v with qdenote ?v => tac (@compile var v) end).

Ltac Reify_cps term tac :=
  quote qdenote [S O] in term using
    (fun v => lazymatch v with qdenote ?v => tac (@Compile v) end).

Ltac do_Reify_rhs _ := do_Reify_rhs_of_cps Reify_cps ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of_cps Reify_cps ().
