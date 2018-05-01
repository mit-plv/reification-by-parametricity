(** * Typeclass-based reification *)
Require Import Reify.ReifyCommon.

Local Generalizable Variables x y rx ry f rf.
Section with_var.
  Context {var : Type}.

  Class reify_of (term : nat) (rterm : @expr var) := {}.
  Global Instance reify_NatMul `{reify_of x rx, reify_of y ry}
    : reify_of (x * y) (rx * ry).
  Global Instance reify_LetIn `{reify_of x rx}
         `{forall y ry, reify_of y (Var ry) -> reify_of (f y) (rf ry)}
    : reify_of (dlet y := x in f y) (elet ry := rx in rf ry).
  Global Instance reify_S `{reify_of x rx}
    : reify_of (S x) (NatS rx).
  Global Instance reify_O
    : reify_of O NatO.
End with_var.

(** This must be commented out pre-8.6; it tells Coq to not try to
    infer reifications if it doesn't fully know what term it's
    reifying. *)

Hint Mode reify_of - ! - : typeclass_instances.
Hint Opaque Nat.mul Let_In : typeclass_instances.

Ltac reify var x :=
  let c := constr:(_ : @reify_of var x _) in
  lazymatch type of c with
  | reify_of _ ?rx => rx
  end.

Ltac Reify x :=
  let c := constr:(fun var => (_ : @reify_of var x _)) in
  lazymatch type of c with
  | forall var, reify_of _ (@?rx var) => rx
  end.

Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
