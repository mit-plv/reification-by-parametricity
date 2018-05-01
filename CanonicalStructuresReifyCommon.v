(** * Reification by canonical structures *)
Require Import Reify.NamedTimers.
Require Import Reify.Common.
Require Export Reify.ReifyCommon.
Require Import Reify.PHOAS.

(** Take care of initial locking of mul, letin, etc. *)

Ltac make_pre_Reify_rhs nat_of untag do_lock_letin do_lock_natmul :=
  let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
  let e := fresh "e" in
  let T := fresh in
  evar (T : Type);
  evar (e : T);
  subst T;
  cut (untag (nat_of e) = RHS);
  [ subst e
  | lazymatch do_lock_letin with
    | true => rewrite ?lock_Let_In_nat
    | false => idtac
    end;
    lazymatch do_lock_natmul with
    | true => rewrite ?lock_Nat_mul
    | false => idtac
    end;
    cbv [e]; clear e ].

(** N.B. we must thunk the constants so as to not focus the goal *)

Ltac make_do_Reify_rhs denote reified_nat_of postprocess :=
  [ >
  | restart_timer "norm reif";
    time "actual reif" refine eq_refl ];
  let denote := denote () in
  let reified_nat_of := reified_nat_of () in
  let e := lazymatch goal with |- ?untag (?nat_of ?e) = _ -> ?LHS = _ => e end in
  let __ := crun ltac:(restart_timer "eval lazy") in
  let e' := (eval lazy in (reified_nat_of e)) in
  let __ := crun ltac:(finish_timing ("Tactic call") "eval lazy") in
  let __ := crun ltac:(restart_timer "postprocess") in
  let e' := postprocess e' in
  let __ := crun ltac:(finish_timing ("Tactic call") "postprocess") in
  let __ := crun ltac:(finish_timing ("Tactic call") "norm reif") in
  time "intros _" intros _;
  time "lazy beta iota" lazy beta iota;
  if_doing_trans ltac:(fun _ => time "transitivity (Denote rv)"
                                     transitivity (denote e')).
