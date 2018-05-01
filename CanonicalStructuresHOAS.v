(** * Canonical-structure based reification *)
(** This version reifies to [@expr nat], and supports let-binders. *)

Require Import Reify.CanonicalStructuresReifyCommon.

(** structure for packaging a nat expr and its reification *)

Structure tagged_nat := tag { untag :> nat }.
Structure reified_of :=
  reify { nat_of : tagged_nat ; reified_nat_of :> @expr nat }.

(** tags to control the order of application *)

Definition var_tag := tag.
Definition S_tag := var_tag.
Definition O_tag := S_tag.
Definition let_in_tag := O_tag.

(** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

Module Export Exports.
  Canonical Structure mul_tag n := let_in_tag n.
  Canonical Structure reify_var n
    := reify (var_tag n) (@Var nat n).
  Canonical Structure reify_O
    := reify (O_tag O) (@NatO nat).
  Canonical Structure reify_S x
    := reify (S_tag (S (nat_of x))) (@NatS nat x).
  Canonical Structure reify_mul x y
    := reify (mul_tag (nat_of x * nat_of y))
             (@NatMul nat x y).
  Canonical Structure reify_let_in v f
    := reify (let_in_tag (nllet x := untag (nat_of v) in nat_of (f x)))
             (elet x := reified_nat_of v in reified_nat_of (f x)).
End Exports.

Ltac pre_Reify_rhs _ := make_pre_Reify_rhs nat_of untag true false.

(** N.B. we must thunk the constants so as to not focus the goal *)

Ltac do_Reify_rhs _ := make_do_Reify_rhs ltac:(fun _ => denote)
                                         ltac:(fun _ => reified_nat_of)
                                         ltac:(fun x => x).
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := pre_Reify_rhs (); do_Reify_rhs (); post_Reify_rhs ().
