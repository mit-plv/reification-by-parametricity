(** * Reification by Mtac2 *)
Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import Reify.ReifyCommon.
Require Import Mtac2.Mtac2.
Require Import Mtac2.DecomposeApp.
Import M.notations.

(** Points of note:

    - We use %\verb|=n>|% to avoid unnecessary normalization /
      reduction *)

Module var_context.
  Inductive var_context {var : Type} :=
  | nil
  | cons (n : nat) (v : var) (xs : var_context).
End var_context.
Fixpoint find_in_ctx {var : Type} (term : nat)
         (ctx : @var_context.var_context var)
  : M (option var)
  := match ctx with
     | var_context.nil => M.ret None
     | var_context.cons term' v xs
       => (mif M.unify term term' UniMatchNoRed then
             M.ret (Some v)
           else
             find_in_ctx term xs)
     end.

Definition mor {A} (t1 t2 : M A) : M A :=
  M.mtry' t1 (fun _ => t2).
Notation "a '_or_' b" := (mor a b)  (at level 50).

Definition reify_helper {var : Type} (term : nat)
           (ctx : @var_context.var_context var)
  : M (@expr var)
  := ((mfix2 reify_helper (term : nat)
             (ctx : @var_context.var_context var)
       : M (@expr var) :=
         lvar <- find_in_ctx term ctx;
           match lvar with
           | Some v => M.ret (@Var var v)
           | None
             =>
             <[decapp term with O]> UniMatchNoRed (M.ret (@NatO var)) _or_
             <[decapp term with S]> UniMatchNoRed (fun x : nat =>
                rx <- reify_helper x ctx;
                M.ret (@NatS var rx)) _or_
             <[decapp term with Nat.mul]> UniMatchNoRed (fun x y : nat =>
                rx <- reify_helper x ctx;
                ry <- reify_helper y ctx;
                M.ret (@NatMul var rx ry)) _or_
             <[decapp term with (@Let_In nat nat)]> UniMatchNoRed (fun v f =>
                rv <- reify_helper v ctx;
                rf <- (M.nu
                         (FreshFrom f) mNone
                         (fun x : nat
                          => M.nu
                               (FreshFrom f) mNone
                               (fun vx : var
                                => let fx := reduce (RedWhd [rl:RedBeta]) (f x) in
                                   rf <- reify_helper fx (var_context.cons x vx ctx);
                                   M.abs_fun vx rf)));
                M.ret (@LetIn var rv rf))
           end) term ctx).
Definition reify (var : Type) (term : nat) : M (@expr var)
  := reify_helper term var_context.nil.
Definition Reify (term : nat) : M Expr
  := \nu var:Type, r <- reify var term; M.abs_fun var r.

Ltac Reify' x := constr:(ltac:(mrun (@Reify x))).
Ltac Reify x := Reify' x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of ltac:(Reify) ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of ltac:(Reify) ().
