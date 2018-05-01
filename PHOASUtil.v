(** * Utility functions for PHOAS *)
Require Import Reify.Common.
Require Import Reify.PHOAS.

Module PHOAS.
  Export Reify.PHOAS.

  Fixpoint beq_helper (e1 e2 : @expr nat) (base : nat) : bool
    := match e1, e2 with
       | LetIn v1 f1, LetIn v2 f2
         => if beq_helper v1 v2 base
            then beq_helper (f1 base) (f2 base) (S base)
            else false
       | Var v1, Var v2 => Nat.eqb v1 v2
       | NatO, NatO => true
       | NatS x, NatS y => beq_helper x y base
       | NatMul x1 y1, NatMul x2 y2
         => andb (beq_helper x1 x2 base) (beq_helper y1 y2 base)
       | LetIn _ _, _
       | Var _, _
       | NatO, _
       | NatS _, _
       | NatMul _ _, _
         => false
       end.
  Definition beq (e1 e2 : @expr nat) : bool := beq_helper e1 e2 O.
  Definition Beq (e1 e2 : Expr) : bool := beq (e1 _) (e2 _).
End PHOAS.
