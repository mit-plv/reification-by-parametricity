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

Definition find_in_ctx {var : Type} (term : nat) :=
  Eval lazy beta match iota delta [M_InDepMatcher idmatcher_match idmatcher_return M.mmatch'] in
  fix find_in_ctx (ctx : @var_context.var_context var) {struct ctx} : M (option var)
  := match ctx with
      | var_context.cons term' v xs =>
        mmatch term' with
        | [#] term | =n> M.ret (Some v)
        | _ => M.ret None
        end
      | _ => M.ret None
      end.

Definition reify_helper {var : Type} (term : nat) (ctx : @var_context.var_context var) : M (@expr var) :=
  Eval lazy beta match iota delta [M_InDepMatcher idmatcher_match idmatcher_return M.mmatch'] in
  (mfix2 reify_helper (term : nat) (ctx : @var_context.var_context var) : M (@expr var) :=
     lvar <- find_in_ctx term ctx;
     match lvar with
     | Some v => M.ret (@Var var v)
     | None =>
       mmatch term with
       | [#] O | =n> M.ret (@NatO var)
       | [#] S | x =n>
         rx <- reify_helper x ctx;
         M.ret (@NatS var rx)
       | [#] Nat.mul | x y =n>
         rx <- reify_helper x ctx;
         ry <- reify_helper y ctx;
         M.ret (@NatMul var rx ry)
       | [#] @Let_In nat nat | v f =n>
         rv <- reify_helper v ctx;
         rf <- (M.nu (FreshFrom f) mNone
                     (fun x : nat
                       => M.nu Generate mNone
                               (fun vx : var
                               => let fx := reduce (RedWhd [rl:RedBeta]) (f x) in
                                   rf <- reify_helper fx (var_context.cons x vx ctx);
                                     M.abs_fun vx rf)));
         M.ret (@LetIn var rv rf)
       end
     end) term ctx.

Definition reify (var : Type) (term : nat) : M (@expr var)
  := reify_helper term var_context.nil.
Definition Reify (term : nat) : M Expr
  := \nu var:Type, r <- reify var term; M.abs_fun var r.

Ltac Reify' x := constr:(ltac:(mrun (@Reify x))).
Ltac Reify x := Reify' x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of ltac:(Reify) ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of ltac:(Reify) ().
