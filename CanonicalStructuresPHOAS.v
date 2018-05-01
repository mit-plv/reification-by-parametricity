(** * Canonical-structure based reification *)
(** This version reifies to [Expr], and supports let-binders. *)

Require Import Coq.Lists.List.
Require Import Reify.CanonicalStructuresReifyCommon.

Local Notation context := (list nat).

Structure tagged_nat (ctx : context) := tag { untag :> nat }.

Structure reified_of (ctx : context) :=
  reify { nat_of : tagged_nat ctx ;
          reified_nat_of :> forall var, list var -> (forall T, T) -> @expr var }.

Definition var_tl_tag := tag.
Definition var_hd_tag := var_tl_tag.
Definition S_tag := var_hd_tag.
Definition O_tag := S_tag.
Definition mul_tag := O_tag.

(** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

Module Export Exports.
  Canonical Structure letin_tag ctx n := mul_tag ctx n.

  Canonical Structure reify_O ctx
    := reify (O_tag ctx 0) (fun var _ _ => @NatO var).
  Canonical Structure reify_S ctx x
    := reify (@S_tag ctx (S (@nat_of ctx x)))
             (fun var vs phantom => @NatS var (x var vs phantom)).
  Canonical Structure reify_mul ctx x y
    := reify (@mul_tag ctx (@nat_of ctx x * @nat_of ctx y))
             (fun var vs phantom => @NatMul var (x var vs phantom) (y var vs phantom)).
  Canonical Structure reify_var_hd n ctx
    := reify (var_hd_tag (n :: ctx) n)
             (fun var vs phantom => @Var var (List.hd (phantom _) vs)).
  Canonical Structure reify_var_tl n ctx x
    := reify (var_tl_tag (n :: ctx) (@nat_of ctx x))
             (fun var vs phantom => reified_nat_of x (List.tl vs) phantom).
  Canonical Structure reify_letin ctx v f
    := reify (letin_tag
                ctx
                (nllet x := @nat_of ctx v in
                 @nat_of (x :: ctx) (f x)))
             (fun var vs phantom
              => elet x := reified_nat_of v vs phantom in
                 reified_nat_of (f (phantom _)) (x :: vs) phantom)%expr.
End Exports.

Definition ReifiedNatOf (e : reified_of nil) : (forall T, T) -> Expr
  := fun phantom var => reified_nat_of e nil phantom.

Ltac pre_Reify_rhs _ := make_pre_Reify_rhs (@nat_of nil) (@untag nil) true false.

(** N.B. we must thunk the constants so as to not focus the goal *)

Ltac do_Reify_rhs _ :=
  make_do_Reify_rhs
    ltac:(fun _ => Denote) ltac:(fun _ => ReifiedNatOf)
    ltac:(fun e =>
            lazymatch e with
            | fun _ => ?e => e
            | _ => ReifyCommon.error_cant_elim_deps e
            end).
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := pre_Reify_rhs (); do_Reify_rhs (); post_Reify_rhs ().
