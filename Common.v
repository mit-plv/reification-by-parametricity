(** * Common Notations for Reification By Parametricity *)
(** ** Introductory Notations *)
Global Set Implicit Arguments.
Reserved Notation "'dlet' x := v 'in' f"
         (at level 200, f at level 200,
          format "'dlet'  x  :=  v  'in' '//' f").
Reserved Notation "'nllet' x := v 'in' f"
         (at level 200, f at level 200,
          format "'nllet'  x  :=  v  'in' '//' f").
Reserved Notation "'elet' x := v 'in' f"
         (at level 200, f at level 200,
          format "'elet'  x  :=  v  'in' '//' f").
Definition Let_In {A B} (v : A) (f : A -> B) : B
  := let x := v in f x.
Notation "'dlet' x := v 'in' f" := (Let_In v (fun x => f)).
Definition key : unit. exact tt. Qed.
Definition lock {A} (v : A) : A := match key with tt => v end.
Lemma unlock {A} (v : A) : lock v = v.
Proof. unfold lock; destruct key; reflexivity. Qed.
Definition LockedLet_In_nat : nat -> (nat -> nat) -> nat
  := lock (@Let_In nat nat).
Definition locked_nat_mul := lock Nat.mul.
Notation "'nllet' x := v 'in' f"
  := (LockedLet_In_nat v (fun x => f)).
Definition lock_Let_In_nat : @Let_In nat nat = LockedLet_In_nat
  := eq_sym (unlock _).
Definition lock_Nat_mul : Nat.mul = locked_nat_mul
  := eq_sym (unlock _).
