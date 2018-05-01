(** * Self-contained example of reification by parametricity on flat expressions *)
Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

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

Module Import EvennessChecking.
  (** ** Theory on checking evenness of expressions *)
  Inductive is_even : nat -> Prop :=
  | even_O : is_even O
  | even_SS : forall x, is_even x -> is_even (S (S x)).

  Fixpoint check_is_even_expr (t : expr) : bool
    := match t with
       | NatO => true
       | NatS x
         => negb (check_is_even_expr x)
       | NatMul x y
         => orb (check_is_even_expr x) (check_is_even_expr y)
       end.

  Notation is_even_or_odd x := ({is_even x} + {~is_even x}).

  Lemma is_even_or_odd_x : forall x, (is_even x /\ ~is_even (S x))
                                     \/ (~is_even x /\ is_even (S x)).
  Proof.
    induction x as [|x [[IHx0 IHx1]|[IHx0 IHx1]]].
    { left; split; try constructor; intro H; inversion H. }
    { right; split; [ | constructor ]; assumption. }
    { left; split;
        [ assumption
        | intro H; inversion_clear H; apply IHx0; assumption ]. }
  Qed.

  Definition is_even_or_odd_S x (pf : is_even_or_odd x)
    : is_even_or_odd (S x).
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

  Definition is_even_or_odd_mul x y
             (Hx : is_even_or_odd x) (Hy : is_even_or_odd y)
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

  Lemma cut_is_even_eq (x y : nat) (H : x = y) (Hx : is_even x)
    : is_even y.
  Proof. subst; assumption. Qed.
End EvennessChecking.

(** ** Reification by parametricity *)
Ltac Reify x :=
  let rx := lazymatch (eval pattern nat, O, S, Nat.mul in x) with
            | ?rx _ _ _ _ => rx end in
  constr:(rx expr NatO NatS NatMul).

Ltac Reify_rhs _ :=
  lazymatch goal with
  | [ |- _ = ?RHS ]
    => let rv := Reify RHS in
       transitivity (denote rv);
       [ | lazy [denote]; reflexivity ]
  end.

(** ** Using reification to check evenness *)

Goal is_even (let x0 := 100 * 100 * 100 * 100 in
              let x1 := x0 * x0 * x0 * x0 in
              let x2 := x1 * x1 * x1 * x1 in
              x2).
Proof.
  eapply cut_is_even_eq.
  { Reify_rhs ().
    reflexivity. }
  apply check_is_even_expr_sound; vm_compute; reflexivity.
Qed.
