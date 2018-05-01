(** * Factored code common to many variants of reification *)
Require Import Reify.NamedTimers.
Require Export Reify.Common.
Require Export Reify.PHOAS.

Notation do_transitivity := false (only parsing).

(** We provide a tactic to run a tactic in a constr context. *)

Ltac crun tac :=
  match goal with
  | _ => tac
  end.

(** Note: If you want to preserve variable names on reification, there
    are many hoops to jump through. We write a [refresh] tactic which
    permits preserving binder names at a nontrivial performance
    overhead. *)

(** c.f. %\url{https://github.com/coq/coq/issues/5448}%,
         %\url{https://github.com/coq/coq/issues/6315}%,
         %\url{https://github.com/coq/coq/issues/6559}% *)

Ltac require_same_var n1 n2 :=
  let c1 := constr:(fun n1 n2 : Set => ltac:(exact n1)) in
  let c2 := constr:(fun n1 n2 : Set => ltac:(exact n2)) in
  first [ constr_eq c1 c2
        | fail 1 "Not the same var:" n1 "and" n2 "(via constr_eq" c1 c2 ")" ].
Ltac is_same_var n1 n2 :=
  match goal with
  | _ => let __ := match goal with _ => require_same_var n1 n2 end in
         true
  | _ => false
  end.
Ltac is_underscore v :=
  let v' := fresh v in
  let v' := fresh v' in
  is_same_var v v'.

(** Note that [fresh_tac] must be [ltac:(fun n => fresh n)];
    c.f. %\url{https://github.com/coq/coq/issues/6559}% *)

Ltac refresh n fresh_tac :=
  let n_is_underscore := is_underscore n in
  let n' := lazymatch n_is_underscore with
            | true => fresh
            | false => fresh_tac n
            end in
  let n' := fresh_tac n' in
  n'.

(** However, this comes at a significant cost in speed, so we do not
    try to preserve variable names, and this tactic is unused in our
    benchmark. *)

Ltac Reify_of reify x :=
  constr:(fun var : Type => ltac:(let v := reify var x in exact v)).

Ltac if_doing_trans tac :=
  let do_trans := constr:(do_transitivity) in
  lazymatch do_trans with
  | true => tac ()
  | false => idtac
  end.

(** We ask for dummy arguments for most things, because it is good
    practice to indicate that this tactic should not be run at the
    call-site (when it's passed to another tactic), but at the
    use-site. *)

Ltac do_Reify_rhs_of_cps_with_denote Reify_cps Denote _ :=
  let v := lazymatch goal with |- ?LHS = ?v => v end in
  let __ := crun ltac:(restart_timer "norm reif") in
  let __ := crun ltac:(restart_timer "actual reif") in
  Reify_cps v ltac:(
    fun rv
    => let __ := crun ltac:(finish_timing ("Tactic call") "actual reif") in
       let __ := crun ltac:(restart_timer "eval lazy") in
       let rv := (eval lazy in rv) in
       let __ := crun ltac:(finish_timing ("Tactic call") "eval lazy") in
       let __ := crun ltac:(finish_timing ("Tactic call") "norm reif") in
       time "lazy beta iota" lazy beta iota;
       if_doing_trans
         ltac:(fun _
               => time "transitivity (Denote rv)"
                       transitivity (Denote rv))).
Ltac do_Reify_rhs_of_cps Reify_cps _ :=
  do_Reify_rhs_of_cps_with_denote Reify_cps Denote ().
Ltac do_Reify_rhs_of_with_denote Reify Denote _ :=
  do_Reify_rhs_of_cps_with_denote
    ltac:(fun v tac => let rv := Reify v in tac rv) Denote ().
Ltac do_Reify_rhs_of Reify _ :=
  do_Reify_rhs_of_with_denote Reify Denote ().
Ltac post_Reify_rhs _ :=
  [ > ..
  | if_doing_trans ltac:(fun _ => lazy [Denote denote]; reflexivity) ].
Ltac Reify_rhs_of_cps Reify_cps _ :=
  do_Reify_rhs_of_cps Reify_cps (); post_Reify_rhs ().
Ltac Reify_rhs_of Reify _ :=
  do_Reify_rhs_of Reify (); post_Reify_rhs ().

Ltac error_cant_elim_deps f :=
  let __ := match goal with
            | _ => idtac "Failed to eliminate functional dependencies in" f
            end in
  constr:(I : I).

Ltac error_bad_function f :=
  let __ := match goal with
            | _ => idtac "Bad let-in function" f
            end in
  constr:(I : I).

Ltac error_bad_term term :=
  let __ := match goal with
            | _ => idtac "Unrecognized term:" term
            end in
  let ret := constr:(term : I) in
  constr:(I : I).
