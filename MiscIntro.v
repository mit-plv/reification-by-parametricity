(** * Miscellaneous code from paper intro *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.

(** ** Proof script primer code *)
Goal forall x, x + 0 = 0 + x.
  induction x as [|x IHx].
  all: simpl Nat.add.
  2: rewrite IHx.
  all: reflexivity.
Qed.


Inductive is_even : nat -> Prop :=
| even_O : is_even O
| even_SS : forall x, is_even x -> is_even (S (S x)).

Goal is_even (let x := 100 * 100 * 100 * 100 in
              let y := x * x * x * x in
              y * y * y * y).
Abort.

(** ** Reflective automation primer code *)
Fixpoint check_is_even (n : nat) : bool
  := match n with
     | O => true
     | S O => false
     | S (S n) => check_is_even n
     end.

Theorem soundness (n : nat) : check_is_even n = true -> is_even n.
Proof.
  revert n; fix 1; destruct n as [|[|n]].
  { constructor. }
  { intro H; inversion H. }
  { specialize (soundness n).
    simpl; intro H'; constructor; intuition. }
Qed.

Goal is_even 2000.
  Time repeat (apply even_SS || apply even_O). (* 1.8 s *)
  Undo.
  Time apply soundness; vm_compute; reflexivity. (* 0.004 s *)
Qed.

Goal is_even (10 * 10 * 10 * 10).
  Time apply soundness; vm_compute; reflexivity. (* 0.001 s *)
Qed.

Goal is_even (10 * 10 * 10 * 10 * 10 * 10).
  Time apply soundness; vm_compute; reflexivity. (* 0.044 s *)
Qed.

Goal is_even (10 * 10 * 10 * 10 * 10 * 10 * 10).
  Time apply soundness; vm_compute; reflexivity. (* 0.396 s *)
Qed.

(*
Goal is_even (10 * 10 * 10 * 10 * 10 * 10 * 10 * 10 * 10).
  Time apply soundness; vm_compute; reflexivity. (* 174.322 secs (151.332u,22.468s) *)
Qed.
*)

(** ** Reflective syntax primer code *)
Inductive expr :=
| NatO : expr
| NatS : expr -> expr
| NatMul : expr -> expr -> expr.

Fixpoint denote (t : expr) : nat
  := match t with
     | NatO => O
     | NatS x => S (denote x)
     | NatMul x y => denote x * denote y
     end.

Fixpoint check_is_even_expr (t : expr) : bool
  := match t with
     | NatO => true
     | NatS x => negb (check_is_even_expr x)
     | NatMul x y => orb (check_is_even_expr x) (check_is_even_expr y)
     end.

Notation is_even_or_odd x := ({is_even x} + {~is_even x}).

Lemma is_even_or_odd_x : forall x, (is_even x /\ ~is_even (S x))
                                   \/ (~is_even x /\ is_even (S x)).
Proof.
  induction x as [|x [[IHx0 IHx1]|[IHx0 IHx1]]].
  { left; split; try constructor; intro H; inversion H. }
  { right; split; [ | constructor ]; assumption. }
  { left; split; [ assumption | intro H; inversion_clear H; apply IHx0; assumption ]. }
Qed.

Definition is_even_or_odd_S x (pf : is_even_or_odd x) : is_even_or_odd (S x).
Proof.
  destruct pf as [pf|pf]; [ right | left ];
    abstract (destruct (is_even_or_odd_x x) as [[H0 H1]|[H0 H1]]; tauto).
Defined.

Definition is_even_or_odd_sum
           x y
  : (is_even x /\ is_even y /\ is_even (x + y))
    \/ (~is_even x /\ ~is_even y /\ is_even (x + y))
    \/ (is_even x /\ ~is_even y /\ ~is_even (x + y))
    \/ (~is_even x /\ is_even y /\ ~is_even (x + y)).
Proof.
  revert y; induction x as [|x IHx];
    intro y;
    [ | destruct (is_even_or_odd_x x) as [H|H]; specialize (IHx (S y));
        rewrite <- !plus_n_Sm in IHx ];
    destruct (is_even_or_odd_x y) as [Hy|Hy];
    intuition.
  { left; repeat constructor; assumption. }
  { right; right; left; repeat constructor; assumption. }
Qed.

Definition is_even_or_odd_mul_helper
           x y
  : (is_even x /\ is_even y /\ is_even (x * y))
    \/ (~is_even x /\ is_even y /\ is_even (x * y))
    \/ (is_even x /\ ~is_even y /\ is_even (x * y))
    \/ (~is_even x /\ ~is_even y /\ ~is_even (x * y)).
Proof.
  induction x as [|x IHx]; simpl.
  { destruct (is_even_or_odd_x y); intuition.
    { left; repeat constructor; assumption. }
    { right; right; left; repeat constructor; assumption. } }
  { pose proof (is_even_or_odd_sum y (x * y)).
    pose proof (is_even_or_odd_x x).
    intuition. }
Qed.

Definition is_even_or_odd_mul x y (Hx : is_even_or_odd x) (Hy : is_even_or_odd y)
  : is_even_or_odd (x * y).
Proof.
  destruct Hx, Hy; [ left | left | left | right ];
    abstract (pose proof (is_even_or_odd_mul_helper x y); intuition).
Defined.

Lemma check_is_even_expr_correct (e : expr)
  : check_is_even_expr e = true <-> is_even (denote e).
Proof.
  induction e; simpl in *.
  { repeat constructor. }
  { rewrite negb_true_iff, <- not_true_iff_false, IHe.
    edestruct (is_even_or_odd_x (denote e)); intuition. }
  { rewrite orb_true_iff, IHe1, IHe2.
    edestruct is_even_or_odd_mul_helper;
      intuition solve [ intuition eauto ]. }
Qed.

Theorem check_is_even_expr_sound (e : expr)
  : check_is_even_expr e = true -> is_even (denote e).
Proof. intro; apply check_is_even_expr_correct; assumption. Qed.

Fixpoint nat_to_expr (v : nat) : expr
  := match v with
     | O => NatO
     | S v => NatS (nat_to_expr v)
     end.
Coercion nat_to_expr : nat >-> expr.
Local Infix "*" := NatMul : expr_scope.
Delimit Scope expr_scope with expr.
Open Scope expr_scope.

Set Printing Coercions.
Goal is_even (denote (10 * 10 * 10 * 10 * 10 * 10 * 10 * 10 * 10)%expr).
  Time apply check_is_even_expr_sound; vm_compute; reflexivity. (* 0 s *)
Qed.

Goal is_even (denote (let x0 := 100 * 100 * 100 * 100 in
                      let x1 := x0 * x0 * x0 * x0 in
                      let x2 := x1 * x1 * x1 * x1 in
                      x2)).
  Time apply check_is_even_expr_sound; vm_compute; reflexivity. (* 0.001 s *)
Qed.

Goal is_even (denote (let x0 := 10 * 10 in
                      let x1 := x0 * x0 in
                      let x2 := x1 * x1 in
                      let x3 := x2 * x2 in
                      let x4 := x3 * x3 in
                      let x5 := x4 * x4 in
                      let x6 := x5 * x5 in
                      let x7 := x6 * x6 in
                      let x8 := x7 * x7 in
                      let x9 := x8 * x8 in
                      let x10 := x9 * x9 in
                      let x11 := x10 * x10 in
                      let x12 := x11 * x11 in
                      let x13 := x12 * x12 in
                      let x14 := x13 * x13 in
                      let x15 := x14 * x14 in
                      let x16 := x15 * x15 in
                      let x17 := x16 * x16 in
                      let x18 := x17 * x17 in
                      let x19 := x18 * x18 in
                      let x20 := x19 * x19 in
                      let x21 := x20 * x20 in
                      let x22 := x21 * x21 in
                      let x23 := x22 * x22 in
                      let x24 := x23 * x23 in
                      x24)).
  Time apply check_is_even_expr_sound; vm_compute; reflexivity. (* 19.13 s *)
Qed.

(** *** With let-in nodes *)
Module WithLetIn.
  Reserved Notation "'dlet' x := v 'in' f"
           (at level 200, f at level 200,
            format "'dlet'  x  :=  v  'in' '//' f").
  Reserved Notation "'elet' x := v 'in' f"
           (at level 200, f at level 200,
            format "'elet'  x  :=  v  'in' '//' f").
  Inductive expr {var : Type} :=
  | NatO : expr
  | NatS : expr -> expr
  | NatMul : expr -> expr -> expr
  | Var : var -> expr
  | LetIn : expr -> (var -> expr) -> expr.
  Definition Let_In {A B} (v : A) (f : A -> B) := let x := v in f x.
  Notation "'dlet' x := v 'in' f" := (Let_In v (fun x => f)).
  Notation "'elet' x := v 'in' f" := (LetIn v (fun x => f)).

  Inductive wf {var1 var2 : Type} (G : list (var1 * var2)) : @expr var1 -> @expr var2 -> Prop :=
  | wfO : wf G NatO NatO
  | wfS : forall x x', wf G x x' -> wf G (NatS x) (NatS x')
  | wfMul : forall x y x' y',
      wf G x x'
      -> wf G y y'
      -> wf G (NatMul x y) (NatMul x' y')
  | wfVar : forall v1 v2,
      List.In (v1, v2) G
      -> wf G (Var v1) (Var v2)
  | wfLetIn : forall x f x' f',
      wf G x x'
      -> (forall v1 v2, wf ((v1, v2)::G) (f v1) (f' v2))
      -> wf G (LetIn x f) (LetIn x' f').

  Fixpoint denote (t : @expr nat) : nat
    := match t with
       | NatO => O
       | NatS x => S (denote x)
       | NatMul x y => denote x * denote y
       | Var x => x
       | LetIn x f => dlet y := denote x in denote (f y)
       end.

  Fixpoint check_is_even_expr (t : @expr bool) : bool
    := match t with
       | NatO => true
       | NatS x => negb (check_is_even_expr x)
       | NatMul x y => orb (check_is_even_expr x) (check_is_even_expr y)
       | Var x => x
       | LetIn x f => dlet y := check_is_even_expr x in check_is_even_expr (f y)
       end.

  Definition Expr := forall var, @expr var.
  Definition Denote (e : Expr) := denote (e _).
  Definition CheckIsEvenExpr (e : Expr) := check_is_even_expr (e _).
  Definition Wf (e : Expr) := forall var1 var2, wf nil (e var1) (e var2).

  Lemma check_is_even_expr_correct G (e1 e2 : expr) (Hwf : wf G e1 e2)
        (HG : forall v1 v2, List.In (v1, v2) G -> (v1 = true <-> is_even v2))
    : check_is_even_expr e1 = true <-> is_even (denote e2).
  Proof.
    induction Hwf; simpl in *.
    { repeat constructor. }
    { rewrite negb_true_iff, <- not_true_iff_false, IHHwf by assumption.
      let x' := match goal with |- ~is_even (denote ?x') <-> _ => x' end in
      edestruct (is_even_or_odd_x (denote x')); intuition. }
    { rewrite orb_true_iff, IHHwf1, IHHwf2 by assumption.
      edestruct is_even_or_odd_mul_helper;
        intuition solve [ intuition eauto ]. }
    { eauto. }
    { cbv [Let_In].
      let IH := match goal with H : forall v1 v2, (forall v3 v4, _ -> _ <-> _) -> _ <-> _ |- _ => H end in
      apply IH.
      intros ?? [H'|H'].
      { inversion_clear H'; eauto. }
      { eauto. } }
  Qed.

  Lemma CheckIsEvenExprCorrect (E : Expr) (Hwf : Wf E)
    : CheckIsEvenExpr E = true <-> is_even (Denote E).
  Proof.
    apply check_is_even_expr_correct with (G:=nil); simpl; eauto; tauto.
  Qed.

  Theorem CheckIsEvenExprSound (e : Expr) (Hwf : Wf e)
    : CheckIsEvenExpr e = true -> is_even (Denote e).
  Proof. intro; apply CheckIsEvenExprCorrect; assumption. Qed.

  (** We could write this: *)

  Ltac prove_wf_step :=
    repeat intro;
    lazymatch goal with
    | [ |- List.In _ _ ] => compute; eauto
    | [ |- wf _ _ _ ] => constructor
    end.
  Ltac prove_wf :=
    repeat prove_wf_step.

  (** But that is itself slow.  We can instead compress the
      well-formedness proof by, effectively, refreshing all of the
      [Var] nodes.  We instantiate [var] with [nat] and then use this
      sort-of de Bruijn instantation of PHOAS to pull variable nodes
      from a [list].  We can then replace the proof of well-formedness
      by a proof that this process of refreshing [Var] nodes leaves
      the syntax tree unchanged, which can be proven with a single
      [eq_refl] proof term. *)

  Fixpoint unnatify {var} (G : list var) (e : @expr nat) : @expr var
    := match e with
       | NatO => NatO
       | NatS x => NatS (@unnatify var G x)
       | NatMul x y => NatMul (@unnatify var G x) (@unnatify var G y)
       | Var x => List.nth_default NatO (List.rev (List.map Var G)) x
       | LetIn x f => LetIn (@unnatify var G x)
                            (fun v => @unnatify var (v::G) (f (List.length G)))
       end.

  Lemma map_nth_error_None A B (f : A -> B) n (ls : list A)
    : nth_error ls n = None -> nth_error (map f ls) n = None.
  Proof.
    revert ls; induction n, ls; simpl; try congruence; eauto.
  Qed.

  Lemma wf_unnatify {var1 var2} G e
    : @wf var1 var2 G (@unnatify var1 (List.map (@fst _ _) G) e)
          (@unnatify var2 (List.map (@snd _ _) G) e).
  Proof.
    revert G; induction e; simpl; repeat constructor; eauto; intros.
    { rewrite <- !map_rev, !map_map; unfold nth_default.
      let v := match goal with |- context[nth_error _ ?v] => v end in
      destruct (nth_error (rev G) v) eqn:H;
        pose proof H as H'; pose proof H as H0;
        [ eapply map_nth_error in H; eapply map_nth_error in H'
        | eapply map_nth_error_None in H; eapply map_nth_error_None in H' ];
        rewrite H, H'; constructor.
      rewrite <- surjective_pairing, in_rev.
      eapply nth_error_In; eassumption. }
    { rewrite !map_length.
      match goal with H : _ |- _ => apply H end. }
  Qed.

  Lemma WfByUnnatify (E : Expr)
    : (E = (fun var => @unnatify var nil (E nat)))
      -> Wf E.
  Proof.
    intro H; rewrite H; intros ??; apply wf_unnatify with (G:=nil).
  Qed.

  Ltac prove_wf_fast :=
    refine (WfByUnnatify _ _);
    vm_compute; reflexivity.

  Ltac Reify x :=
    let r := lazymatch (eval pattern nat, O, S, Nat.mul, (@Let_In nat nat) in x) with
             | (fun N : Set => ?f) _ _ _ _ _ => constr:(fun N : Type => f) end in
    let __ := type of r in
    constr:(fun var => r (@expr var) NatO NatS NatMul
                         (fun x' f => LetIn x' (fun v => f (Var v)))).

  Local Open Scope nat_scope.

  (** We must tell Coq to unfold [Denote] and [denote] before
      unfolding things like [Let_In], or else the [refine] below will
      be very, very slow.  We do this with [Strategy]. *)
  Strategy -10 [Denote denote].
  Goal is_even (dlet x0 := 10 * 10 in
                dlet x1 := x0 * x0 in
                dlet x2 := x1 * x1 in
                dlet x3 := x2 * x2 in
                dlet x4 := x3 * x3 in
                dlet x5 := x4 * x4 in
                dlet x6 := x5 * x5 in
                dlet x7 := x6 * x6 in
                dlet x8 := x7 * x7 in
                dlet x9 := x8 * x8 in
                dlet x10 := x9 * x9 in
                dlet x11 := x10 * x10 in
                dlet x12 := x11 * x11 in
                dlet x13 := x12 * x12 in
                dlet x14 := x13 * x13 in
                dlet x15 := x14 * x14 in
                dlet x16 := x15 * x15 in
                dlet x17 := x16 * x16 in
                dlet x18 := x17 * x17 in
                dlet x19 := x18 * x18 in
                dlet x20 := x19 * x19 in
                dlet x21 := x20 * x20 in
                dlet x22 := x21 * x21 in
                dlet x23 := x22 * x22 in
                dlet x24 := x23 * x23 in
                x24)%nat.
  Proof.
    Time lazymatch goal with
         | [ |- is_even ?v ]
           => let e := Reify v in
              refine (CheckIsEvenExprSound e _ _);
                [ prove_wf_fast
                | vm_compute; reflexivity ]
         end. (* 0.012 s *)
  Qed.
End WithLetIn.
