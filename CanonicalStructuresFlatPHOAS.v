(** * Canonical-structure based reification *)
(** This version reifies to [Expr], and does not support
    let-binders. *)

Require Import Reify.CanonicalStructuresReifyCommon.

(** structure for packaging a nat expr and its reification *)

Structure tagged_nat := tag { untag :> nat }.
Structure reified_of :=
  reify { nat_of : tagged_nat ; reified_nat_of :> Expr }.

(** tags to control the order of application *)

Definition S_tag := tag.
Definition O_tag := S_tag.

(** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

Module Export Exports.
  Canonical Structure mul_tag n := O_tag n.
  Canonical Structure reify_O
    := reify (O_tag 0) (@NatO).
  Canonical Structure reify_S x
    := reify (S_tag (S (nat_of x))) (fun var => @NatS var (reified_nat_of x var)).
  Canonical Structure reify_mul x y
    := reify (mul_tag (nat_of x * nat_of y))
             (fun var => @NatMul var (reified_nat_of x var) (reified_nat_of y var)).
End Exports.

(** We take advantage of not needing to lock [Let_In] to avoid a
    rewrite by passing [false] to the [do_lock_letin] argument of
    [make_pre_Reify_rhs] *)

Ltac pre_Reify_rhs _ := make_pre_Reify_rhs nat_of untag false false.

(** N.B. we must thunk the constants so as to not focus the goal *)

Ltac do_Reify_rhs _ := make_do_Reify_rhs ltac:(fun _ => Denote)
                                         ltac:(fun _ => reified_nat_of)
                                         ltac:(fun x => x).
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := pre_Reify_rhs (); do_Reify_rhs (); post_Reify_rhs ().
