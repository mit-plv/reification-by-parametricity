(** * Reification by template-coq *)
Require Coq.Strings.String.
Require Import Reify.ReifyCommon.
Require Import Template.Ast.
Require Import Template.Template.

Module Compile.
  Import Coq.Strings.String.
  Scheme Equality for string.

  Section with_var.
    Context {var : Type}.
    Axiom bad : var.
    Fixpoint compile (e : term) (ctx : list var) : @expr var
      := match e with
         | tRel idx => Var (List.nth_default bad ctx idx)
         | tCast e _ _
           => compile e ctx
         | tConstruct (mkInd Bp 0) 0 _
           => @NatO var
         | tApp f4 (_ :: _ :: x :: tLambda _ _ f :: nil)
           => @LetIn var (compile x ctx)
                     (fun x' => compile f (x' :: ctx))
         | tApp f2 (x :: y :: nil)
           => @NatMul var (compile x ctx) (compile y ctx)
         | tApp f1 (x :: nil)
           => @NatS var (compile x ctx)
         | _
           => Var bad
         end%list.
  End with_var.
  Definition Compile (e : term) : Expr := fun var => @compile var e nil.
End Compile.

Ltac reify_cps var term tac :=
  quote_term term (fun v => tac (@Compile.compile var v)).

Ltac Reify_cps term tac :=
  quote_term term (fun v => tac (Compile.Compile v)).

Ltac do_Reify_rhs _ := do_Reify_rhs_of_cps Reify_cps ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of_cps Reify_cps ().
