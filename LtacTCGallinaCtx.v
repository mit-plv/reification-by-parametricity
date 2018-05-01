(** * Recursing under binders with typeclasses, tracking variables with Gallina contexts *)
Require Import Reify.ReifyCommon.

(** Points of note:

    - We make sure to fill in all implicit arguments explicitly, to
      minimize the number of evars generated; evars are one of the
      main bottlenecks.

    - We do not use a typeclass for the variable case to avoid
      typeclass search when it's not needed.

    - In the [Hint] used to tie the recursive knot, we run [intros]
      before binding any terms to avoid playing fast and loose with
      binders, because we will sometimes be presented with goals with
      unintroduced binders.  If we did not call [intros] first,
      instead binding [?var] and [?term] in the hint pattern rule,
      they might contain unbound identifiers, causing reification to
      fail when it tried to deal with them. *)

Class reify_cls (var : Type) (term : nat) := do_reify : @expr var.

(** Much like typeclass-based reification, we introduce a definition
    to track which [nat] binders reify to which [var] binders,
    searching the context for such hypotheses. *)

Definition var_for {var : Type} (n : nat) (v : var) := False.

Ltac reify var term :=
  let reify_rec term := reify var term in
  lazymatch goal with
  | [ H : var_for term ?v |- _ ]
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
               constr:(_ : forall (x : nat) (not_x : var)
                                  (_ : @var_for var x not_x),
                          @reify_cls var f)
             with
             | fun _ v' _ => @?f v' => f
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
