(** * Recursing under binders with typeclasses, tracking variables by pairing *)
Require Import Reify.ReifyCommon.
Require Import Reify.PrimPair.

(** Points of note:

    - We use primitive projections for pairing to speed up typing.

    - We make sure to fill in all implicit arguments explicitly, to
      minimize the number of evars generated; evars are one of the
      main bottlenecks.

    - We make use of a trick from "%[coqdev]% beta1 and zeta1
      reduction"%\footnote{\url{https://sympa.inria.fr/sympa/arc/coqdev/2016-01/msg00060.html}}%
      to bind names with a single-branch [match] statement without
      incurring extra β or ζ reductions.

    - We give the [return] clause on the [match] statement explicitly
      to work around
      %\url{https://github.com/coq/coq/issues/6252\#issuecomment-347041995}%
      and prevent extra backtracking, as well as preventing extra evar
      allocation.

    - In the [Hint] used to tie the recursive knot, we run [intros]
      before binding any terms to avoid playing fast and loose with
      binders, because we will sometimes be presented with goals with
      unintroduced binders.  If we did not call [intros] first,
      instead binding [?var] and [?term] in the hint pattern rule,
      they might contain unbound identifiers, causing reification to
      fail when it tried to deal with them. *)

Class reify_cls (var : Type) (term : nat) := do_reify : @expr var.

Ltac reify var term :=
  let reify_rec term := reify var term in
  lazymatch term with
  | fst (?term, ?v)
    => constr:(@Var var v)
  | _
    =>
    lazymatch term with
    | O => constr:(@NatO var)
    | S ?x
      => let rx := reify_rec x in
         constr:(@NatS var rx)
    | ?x * ?y
      => let rx := reify_rec x in
         let ry := reify_rec y in
         constr:(@NatMul var rx ry)
    | (dlet x := ?v in ?f)
      => let rv := reify_rec v in
         let not_x := fresh (*x *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
         let not_x2 := fresh (*not_x *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
         let rf
             :=
             lazymatch
               constr:(_ : forall (not_x : nat) (not_x2 : var),
                          @reify_cls
                            var
                            match @fst nat var (@pair nat var not_x not_x2)
                                  return nat
                            with
                            | x => f
                            end)
             with
             | fun _ => ?f => f
             | ?f => error_cant_elim_deps f
             end in
         constr:(@LetIn var rv rf)
    | ?v
      => error_bad_term v
    end
  end.

Ltac Reify x := Reify_of reify x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().

Global Hint Extern 0 (@reify_cls _ _)
=> (intros;
      lazymatch goal with
      | [ |- @reify_cls ?var ?term ]
        => let res := reify var term in
           exact res
      end) : typeclass_instances.
