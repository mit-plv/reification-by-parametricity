(** * Recursing under binders with typeclasses, tracking variables with explicit contexts *)
Require Import Reify.ReifyCommon.

(** Points of note:

    - We make sure to fill in all implicit arguments explicitly, to
      minimize the number of evars generated; evars are one of the
      main bottlenecks.

    - In the [Hint] used to tie the recursive knot, we run [intros]
      before binding any terms to avoid playing fast and loose with
      binders, because we will sometimes be presented with goals with
      unintroduced binders.  If we did not call [intros] first,
      instead binding [?var] and [?term] in the hint pattern rule,
      they might contain unbound identifiers, causing reification to
      fail when it tried to deal with them. *)

Module var_context.
  Inductive var_context {var : Type} :=
  | nil
  | cons (n : nat) (v : var) (xs : var_context).
End var_context.

Class reify_helper_cls (var : Type) (term : nat)
      (ctx : @var_context.var_context var)
  := do_reify_helper : @expr var.

Ltac reify_helper var term ctx :=
  let reify_rec term := reify_helper var term ctx in
  lazymatch ctx with
  | context[var_context.cons term ?v _]
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
         let rf
             :=
             lazymatch
               constr:(_ : forall (x : nat) (not_x : var),
                          @reify_helper_cls
                            var f (@var_context.cons var x not_x ctx))
             with
             | fun _ => ?f => f
             | ?f => error_cant_elim_deps f
             end in
         constr:(@LetIn var rv rf)
    | ?v
      => error_bad_term v
    end
  end.

Ltac reify var x :=
  reify_helper var x (@var_context.nil var).
Ltac Reify x := Reify_of reify x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().

Global Hint Extern 0 (@reify_helper_cls _ _ _)
=> (intros;
      lazymatch goal with
      | [ |- @reify_helper_cls ?var ?term ?ctx ]
        => let res := reify_helper var term ctx in
           exact res
      end) : typeclass_instances.
