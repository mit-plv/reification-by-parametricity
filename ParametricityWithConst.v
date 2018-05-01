(** * Reification by parametricity, with a routine for handling constants recursively *)
Require Import Reify.ReifyCommon.

(** This file contains the extra code to handle constants recursively.
    We advise against using this code, and provide it as a proof of
    concept only. *)

(** expects:
    - [var] - the PHOAS var type
    - [find_const term found_tac not_found_tac], a tactical which
      looks for constants in [term], invokes [found_tac] with the
      constant if it finds one, and invokes [not_found_tac ()] if it
      finds none.
    - [plug_const var term const], a tactic which takes a term and a
      constant, and plugs in the reified version of [const] *)

Ltac reify_with_consts var find_const plug_const term :=
  find_const
    term
    ltac:(fun c
          => let rx := lazymatch (eval pattern c in term) with
                       | ?term _ => term
                       end in
             let rx := reify_with_consts find_const plug_const term in
             plug_const var rx c)
    ltac:(fun _
          => let rx :=
                 lazymatch
                   (eval pattern nat, Nat.mul, (@Let_In nat (fun _ => nat)), O, S
                     in term)
                 with
                 | ?rx _ _ _ _ _ => rx
                 end in
             let rx := lazymatch rx with
                       | fun N : Set => ?rx => constr:(fun N : Type => rx)
                       end in
             let __ := type of rx in (* propagate universe constraints, c.f., https://github.com/coq/coq/issues/5996 *)
             constr:(rx (@expr var) (@NatMul var)
                        (fun x' f'
                         => @LetIn var x'
                                   (fun v => f' (@Var var v)))
                        (@NatO var) (@NatS var))).
Ltac Reify_with_consts find_const plug_const term :=
  constr:(fun var : Type
          => ltac:(let rx := reify_with_consts var find_const plug_const term in
                   exact rx)).
