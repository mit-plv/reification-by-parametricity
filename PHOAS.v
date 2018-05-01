(** * Expression trees in PHOAS *)
Require Import Reify.Common.

Inductive expr {var : Type} : Type :=
| NatO : expr
| NatS : expr -> expr
| LetIn (v : expr) (f : var -> expr)
| Var (v : var)
| NatMul (x y : expr).

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.

Infix "*" := NatMul : expr_scope.
Notation "'elet' x := v 'in' f" := (LetIn v (fun x => f%expr)) : expr_scope.
Notation "$$ x" := (Var x) (at level 9, format "$$ x") : expr_scope.

Fixpoint denote (e : @expr nat) : nat
  := match e with
     | NatO => O
     | NatS x => S (denote x)
     | LetIn v f => dlet x := denote v in denote (f x)
     | Var v => v
     | NatMul x y => denote x * denote y
     end.

Definition Expr := forall var, @expr var.
Definition Denote (e : Expr) := denote (e _).
