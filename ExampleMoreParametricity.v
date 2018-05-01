(** * Reification by parametricity: More Examples *)
Require Import Coq.Lists.List.
Reserved Notation "'λ' x .. y , t"
         (at level 200, x binder, y binder, right associativity,
          format "'λ'  x .. y , '//' t").
Reserved Infix "@" (left associativity, at level 11).

Module Import NatExpr.
  (** ** Expressions of natural numbers *)
  (** Here we show how to reify simple expressions of natural numbers
      into syntax trees.  Note that we place [expr] in [Set] to avoid
      having to adjust [Type] binders.  See [AbstractionList] for an
      example with [expr] in [Type]. *)

  Inductive expr {var : Set} : Set :=
  | NatO : expr
  | NatS : expr -> expr
  | NatMul : expr -> expr -> expr
  | NatAdd : expr -> expr -> expr
  | Var : var -> expr.

  Fixpoint denote (e : @expr nat) : nat
    := match e with
       | NatO => O
       | NatS x => S (denote x)
       | NatMul x y => denote x * denote y
       | NatAdd x y => denote x + denote y
       | Var v => v
       end.

  Definition Expr := forall var, @expr var.
  Definition Denote (e : Expr) : nat := denote (e nat).

  Ltac Reify x :=
    let rx := lazymatch (eval pattern nat, O, S, Nat.mul, Nat.add in x) with
              | ?rx _ _ _ _ _ => rx end in
    constr:(fun var => rx (@expr var) NatO NatS NatMul NatAdd).

  Goal True.
    let v := Reify (1 * 2 + 3) in
    pose v as r.
    (** Now we check that we get what we expected to get *)

    pose (eq_refl
          : r = (fun var
                 => NatAdd
                      (NatMul (NatS NatO) (NatS (NatS NatO)))
                      (NatS (NatS (NatS NatO))))).
  Abort.
End NatExpr.

Module Import ForallExistsImpl.
  (** ** ℕ expressions with variables *)
  (** Here we show how to reify quantified formulas of natural numbers
      into PHOAS.  Note that we place [expr] in [Set] to avoid having
      to adjust [Type] binders.  See [AbstractionList] for an example
      with [expr] in [Type]. *)
  (* Open terms that are implicitly universally quantified over the
  free variables are transformed into explicitly universally
  quantified statements on the fly. *)

  Inductive type := NAT | PROP.

  Inductive expr {var : Set} : Set :=
  | Forall (P : var -> expr) : expr
  | Exists (P : var -> expr) : expr
  | And (x y : expr) : expr
  | Imp (x y : expr) : expr
  | LtNat (x y : @NatExpr.expr var) : expr
  | EqNat (x y : @NatExpr.expr var) : expr.

  Fixpoint denote (e : @expr nat) : Prop
    := match e with
       | Forall P => forall n, denote (P n)
       | Exists P => exists n, denote (P n)
       | And x y => denote x /\ denote y
       | Imp x y => denote x -> denote y
       | LtNat x y => NatExpr.denote x < NatExpr.denote y
       | EqNat x y => NatExpr.denote x = NatExpr.denote y
       end.

  Definition Expr := forall var, @expr var.
  Definition Denote (e : Expr) := denote (e nat).

  (** Note that we cannot [pattern] over ``[forall]'', nor ``[->]'',
      so this method cannot really handle [forall].  However, we can
      handle it in prenex positions by recursively reverting the
      context, and replacing [forall] and [->] with custom definitions
      accessible to [pattern]. *)

  Definition _forall {T} (P : T -> Prop) := forall (x : T), P x.
  Definition impl (A B : Prop) := A -> B.
  Ltac Reify x :=
    let rx := lazymatch (eval pattern nat, Prop, O, S, Nat.mul, Nat.add, lt,
                         (@eq nat), and, impl, (@ex nat), (@_forall nat)
                          in x) with
              | ?rx _ _ _ _ _ _ _ _ _ _ _ _ => rx end in
    constr:(fun var
            => rx (@NatExpr.expr var) (@expr var)
                  NatO NatS NatMul NatAdd LtNat EqNat And Imp
                  (fun P => @Exists var (fun v => P (Var v)))
                  (fun P => @Forall var (fun v => P (Var v)))).

  Ltac revert_all_for_pattern :=
    repeat (match goal with H : _ |- _ => revert H end;
            lazymatch goal with
            | [ |- forall n : nat, @?P n ] => change (@_forall nat P)
            | [ |- ?A -> ?B ] => change (impl A B)
            end).
  Ltac Reify_goal :=
    (** First we revert things *)

    revert_all_for_pattern;
    (** Now we reify *)

    let g := match goal with |- ?G => G end in
    let rg := Reify g in
    change (Denote rg).

  (** We make a notation to display the goal more easily. *)

  Delimit Scope expr_scope with expr.
  Bind Scope expr_scope with expr.
  Bind Scope expr_scope with NatExpr.expr.
  Notation "∀ x .. y , P"
    := (Forall (fun x => .. (Forall (fun y => P)) .. ))
         (at level 200, x binder, y binder, right associativity,
          format "'[  ' ∀  x  ..  y ']' ,  P") : expr_scope.
  Notation "∃ x .. y , P"
    := (Exists (fun x => .. (Exists (fun y => P)) .. ))
         (at level 200, x binder, y binder, right associativity,
          format "'[  ' ∃  x  ..  y ']' ,  P") : expr_scope.
  Infix "*" := NatMul : expr_scope.
  Infix "+" := NatAdd : expr_scope.
  Infix "<" := LtNat : expr_scope.
  Infix "=" := EqNat : expr_scope.

  Goal forall a b, 0 < b -> exists q r, a = q * b + r /\ r < b.
    intros.
    Reify_goal.
    (** Now we check that we got what we want *)

    cbv beta.
    lazymatch goal with
    | [ |- Denote
             (fun var =>
                ∀ a b,
                  Imp
                    (NatO < Var b)
                    (∃ q r,
                        And
                          (Var a = Var q * Var b + Var r)
                          (Var r < Var b)))%expr ]
      => idtac
    end.
  Abort.
End ForallExistsImpl.

Module HigherOrderFunctionsTakingLambdas.
  (** ** Expressions involving λ *)
  (** What if we have abstraction nodes?  The trick is to pair them
      with the higher-order function which takes in the λ.  We use the
      example of [sum_upto n f := f 0 + f 1 + f 2 + ... + f n].  Note
      that we place [expr] in [Set] to avoid having to adjust [Type]
      binders.  See [AbstractionList] for an example with [expr] in
      [Type]. *)

  Inductive type := NAT | ARROW (a b : type).
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.
  Infix "->" := ARROW : etype_scope.
  Inductive expr {var : type -> Set} : type -> Set :=
  | Var {t} (v : var t) : expr t
  | NatO : expr NAT
  | NatS : expr (NAT -> NAT)
  | NatAdd : expr (NAT -> NAT -> NAT)
  | NatMul : expr (NAT -> NAT -> NAT)
  | Sum_UpTo : expr (NAT -> (NAT -> NAT) -> NAT)
  | App {a b} : expr (a -> b) -> expr a -> expr b
  | Abs {a b} (f : var a -> expr b) : expr (a -> b).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Notation "'λ'  x .. y , t"
    := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
  Infix "@" := App : expr_scope.

  Fixpoint type_denote (t : type) : Set
    := match t with
       | NAT => nat
       | ARROW a b => type_denote a -> type_denote b
       end.

  Definition sum_upto (n : nat) (f : nat -> nat) : nat
    := List.fold_left Nat.add (List.map f (List.seq 0 (S n))) 0.

  Fixpoint denote {t} (e : @expr type_denote t) : type_denote t
    := match e with
       | Var v => v
       | NatO => O
       | NatS => S
       | NatMul => Nat.mul
       | NatAdd => Nat.add
       | Sum_UpTo => sum_upto
       | App f x => denote f (denote x)
       | Abs f => fun x => denote (f x)
       end.

  Definition Expr t := forall var, @expr var t.
  Definition Denote {t} (e : Expr t) := denote (e type_denote).

  (** To reify these sorts of terms, the trick is to pair [App] and
      [Abs] nodes with the functions. *)

  Ltac Reify x :=
    let rx := lazymatch (eval pattern nat, O, S, Nat.mul, Nat.add, sum_upto
                          in x) with
              | ?rx _ _ _ _ _ _ => rx end in
    constr:(fun var
            => (rx (@expr var NAT)
                   NatO
                   (fun a => NatS @ a)
                   (fun a b => NatMul @ a @ b)
                   (fun a b => NatAdd @ a @ b)
                   (fun n f => Sum_UpTo @ n @ (λ v, f (Var v))))%expr).

  Goal True.
    let r := Reify (sum_upto (1 * 2 + 3) (fun x => x)) in
    pose r as rx.
    (** Now we check that we got what we wanted *)

    pose (eq_refl
          : rx
            = (fun var =>
                 Sum_UpTo
                   @ (NatAdd
                        @ (NatMul @ (NatS @ NatO) @ (NatS @ (NatS @ NatO)))
                        @ (NatS @ (NatS @ (NatS @ NatO))))
                   @ (λ v, Var v))%expr).
  Abort.
End HigherOrderFunctionsTakingLambdas.

Module TopLevelLambda.
  (** ** Expressions involving λ at the top-level *)
  (** What if we have abstraction nodes at the top level?  Here,
      again, we have to handle them one-by-one, to deal with the fact
      that we cannot [pattern] over ``[->]''.  Note that we place
      [expr] in [Set] to avoid having to adjust [Type] binders.  See
      [AbstractionList] for an example with [expr] in [Type]. *)

  Inductive type := NAT | ARROW (a b : type).
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.
  Infix "->" := ARROW : etype_scope.
  Inductive expr {var : type -> Set} : type -> Set :=
  | NatOf (e : @NatExpr.expr (var NAT)) : expr NAT
  | Abs {a b} (f : var a -> expr b) : expr (a -> b).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Notation "'λ'  x .. y , t"
    := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.

  Fixpoint type_denote (t : type) : Set
    := match t with
       | NAT => nat
       | ARROW a b => type_denote a -> type_denote b
       end.

  Fixpoint denote {t} (e : @expr type_denote t) : type_denote t
    := match e with
       | NatOf e => NatExpr.denote e
       | Abs f => fun x => denote (f x)
       end.

  Definition Expr t := forall var, @expr var t.
  Definition Denote {t} (e : Expr t) := denote (e type_denote).

  (** The standard reification by parametricity will return a Gallina
      function.  To reify top-level λs, we must add the [Abs] nodes
      recursively. *)

  Ltac post_reify var rx :=
    lazymatch type of rx with
    | @NatExpr.expr ?varNAT -> _
      => let v := fresh in
         let rf :=
             constr:(
               fun v : varNAT
               => ltac:(let rf := post_reify var (rx (@NatExpr.Var varNAT v)) in
                        exact rf)) in
         constr:(@Abs var NAT _ rf)
    | _
      => constr:(@NatOf var rx)
    end.
  Ltac Reify x :=
    constr:(fun var : type -> Set
            => ltac:(let rx := NatExpr.Reify x in
                     let rf := post_reify var (rx (var NAT)) in
                     exact rf)).

  Goal True.
    let r := Reify (fun x y => x * x * y * y) in
    pose r as rx.
    (** Now we check that we got what we wanted *)

    cbv beta in rx.
    pose (eq_refl
          : rx
            = (fun var =>
                 (λ x y, NatOf (Var x * Var x * Var y * Var y)))%expr).
  Abort.
End TopLevelLambda.

Module PolymorphicHigherOrder.
  (** ** List Expressions involving λ *)
  (** What if we have abstraction nodes?  The trick is to pair them
      with the higher-order function which takes in the λ.  We use the
      example of [list] with [map]. *)

  Inductive type := NAT | LIST (t : type) | ARROW (a b : type).
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.
  Infix "->" := ARROW : etype_scope.
  Inductive expr {var : type -> Type} : type -> Type :=
  | Var {t} (v : var t) : expr t
  | Nil {t} : expr (LIST t)
  | Cons {t} : expr (t -> LIST t -> LIST t)
  | NatO : expr NAT
  | NatS : expr (NAT -> NAT)
  | NatMul : expr (NAT -> NAT -> NAT)
  | Map {a b} : expr ((a -> b) -> LIST a -> LIST b)
  | App {a b} : expr (a -> b) -> expr a -> expr b
  | Abs {a b} (f : var a -> expr b) : expr (a -> b).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Notation "'λ'  x .. y , t"
    := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
  Infix "@" := App : expr_scope.

  Fixpoint type_denote (t : type) : Type
    := match t with
       | NAT => nat
       | LIST t => list (type_denote t)
       | ARROW a b => type_denote a -> type_denote b
       end.

  Fixpoint denote {t} (e : @expr type_denote t) : type_denote t
    := match e with
       | Var v => v
       | @Nil _ t => @nil (type_denote t)
       | @Cons _ t => @cons (type_denote t)
       | NatO => O
       | NatS => S
       | NatMul => Nat.mul
       | @Map _ a b => @List.map (type_denote a) (type_denote b)
       | App f x => denote f (denote x)
       | Abs f => fun x => denote (f x)
       end.

  Definition Expr t := forall var, @expr var t.
  Definition Denote {t} (e : Expr t) := denote (e type_denote).

  (** To reify these sorts of terms, the trick is to pair [App] and
      [Abs] nodes with the functions.  Note also that there must be a
      clear distinction between types that we reify and types that we
      don't; we choose here to handle only [list nat], but we could
      extend this to include, e.g., [list (list nat)] and [list (nat
      -> nat)].  We can't extend it to handle [list (anything)]
      without changing the type of type codes, because we need a clear
      separation between what we reify and what we don't. *)

  (** Due to %\url{https://github.com/coq/coq/issues/7195}%, we can
      only adjust types on the first binder, so we need a function
      that swaps the first two binders. *)

  Ltac swap_first_two_binders x :=
    lazymatch x with
    | fun a b => @?x' b a => x'
    end.
  Ltac adjust_first_binder_to_type rx :=
    lazymatch rx with
    | (fun (N : Set) => ?rx) => constr:(fun (N : Type) => rx)
    end.
  Ltac Reify x :=
    let rx := lazymatch (eval pattern nat, (list nat), O, S, Nat.mul,
                         (@nil nat), (@cons nat), (@List.map nat nat)
                          in x) with
              | ?rx _ _ _ _ _ _ _ _ => rx end in
    let rx := adjust_first_binder_to_type rx in
    let rx := swap_first_two_binders rx in
    let rx := adjust_first_binder_to_type rx in
    let rx := swap_first_two_binders rx in
    (** Now we propagate universe constraints, because [nat] is in
        [Set] but [expr] is in [Type]; c.f.,
        %\url{https://github.com/coq/coq/issues/5996}% *)

    let __ := type of rx in
    constr:(fun var
            => (rx (@expr var NAT) (@expr var (LIST NAT))
                   NatO
                   (fun a => NatS @ a)
                   (fun a b => NatMul @ a @ b)
                   Nil
                   (fun v vs => Cons @ v @ vs)
                   (fun f ls => Map @ (λ v, f (Var v)) @ ls))%expr).

  Goal True.
    let r := Reify (List.map (fun x => x * x) (1 :: 2 :: 3 :: nil)) in
    pose r as rx.
    (** Now we check that we got what we wanted *)

    pose (eq_refl
          : rx
            = (fun var =>
                 Map
                   @ (λ v : var NAT, NatMul @ Var v @ Var v)
                   @ (Cons
                        @ (NatS @ NatO)
                        @ (Cons
                             @ (NatS @ (NatS @ NatO))
                             @ (Cons
                                  @ (NatS @ (NatS @ (NatS @ NatO)))
                                  @ Nil))))%expr).
  Abort.
End PolymorphicHigherOrder.
