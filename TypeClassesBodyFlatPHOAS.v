(** * Typeclass-based reification *)
(** We can also do typeclass-based reification where we return the
    reified term in the body rather than in the type.  However, this
    method does not work well with binders, because there's no easy
    way to eliminate the dependency on the unreified binder when
    reifying to PHOAS. *)

Require Import Reify.ReifyCommon.

Local Generalizable Variables x y rx ry f rf.
Section with_var.
  Context {var : Type}.

  Class reify_of (term : nat) := rterm : @expr var.
  Global Instance reify_NatMul `{rx : reify_of x, ry : reify_of y}
    : reify_of (x * y) := (rx * ry)%expr.
  Global Instance reify_S `{rx : reify_of x}
    : reify_of (S x) := NatS rx.
  Global Instance reify_O
    : reify_of O := NatO.
End with_var.

(** This must be commented out pre-8.6; it tells Coq to not try to
    infer reifications if it doesn't fully know what term it's
    reifying. *)

Hint Mode reify_of - ! : typeclass_instances.
Hint Opaque Nat.mul : typeclass_instances.

Ltac reify var x :=
  constr:(_ : @reify_of var x).

Ltac Reify x :=
  constr:(_ : forall var, @reify_of var x).

Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
