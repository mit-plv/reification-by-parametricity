(** * Reification by Ltac2, copying Ltac1 *)

(** This file contains the Ltac2 version of Ltac1 reification, from
    [LtacTacInTermExplicitCtx.v]. *)

Require Import Reify.ReifyCommon.
Require Import Reify.Ltac2Common.
Import Ltac2.Init.
Import Ltac2.Notations.

Ltac2 rec reify_helper
      (var : constr)
      (term : constr)
      (ctx : (ident * ident) list)
  :=
    let reify_rec term := reify_helper var term ctx in
    Control.plus
      (fun ()
       => match Constr.Unsafe.kind (Constr.strip_casts term) with
          | Constr.Unsafe.Var x
            => let v := Ident.find x ctx in
               let v := Constr.Unsafe.make (Constr.Unsafe.Var v) in
               constr:(@Var $var $v)
          | _ => Control.zero Not_found
          end)
      (fun _
       => (lazy_match! term with
          | 0 => constr:(@NatO $var)
          | S ?x
            => let rx := reify_rec x in
               constr:(@NatS $var $rx)
          | ?x * ?y
            => let rx := reify_rec x in
               let ry := reify_rec y in
               constr:(@NatMul $var $rx $ry)
          | (dlet x := ?v in @?f x)
            => let rv := reify_rec v in

               (** We assume the invariant that all bound variables
                     show up as [Rel] nodes rather than [Var] nodes *)

               match Constr.Unsafe.kind f with
               | Constr.Unsafe.Lambda id t c
                 => let c_set := Fresh.Free.of_ids
                                   (List.map (fun (id, _, _) => id)
                                             (Control.hyps ())) in
                    let c_set := Fresh.Free.union
                                   c_set
                                   (Fresh.Free.of_constr c) in
                    let x_base := match id with
                                  | Some id => id
                                  | None => @x
                                  end in
                    let x := Fresh.fresh c_set x_base in
                    let c_set := Fresh.Free.union
                                   c_set
                                   (Fresh.Free.of_ids [x]) in
                    let not_x := Fresh.fresh c_set x_base in
                    let ctx := (x, not_x) :: ctx in
                    let c := Constr.Unsafe.substnl
                               [Constr.Unsafe.make (Constr.Unsafe.Var x)]
                               0
                               c in
                    let ret :=
                        Constr.in_context
                          x t
                          (fun ()
                           => let rf :=
                                  Constr.in_context
                                    not_x var
                                    (fun ()
                                     => let rf := reify_helper var c ctx in
                                        Control.refine (fun () => rf)) in
                              Control.refine (fun () => rf)) in
                    (lazy_match! ret with
                    | fun _ => ?rf
                      => constr:(@LetIn $var $rv $rf)
                    | ?f
                      => let msg :=
                             Message.concat
                               (Message.of_string
                                  "Failed to eliminate functional dependencies in ")
                               (Message.of_constr f) in
                         Message.print msg;
                           Control.zero
                             (Tactic_failure (Some msg))
                     end)
               | _ => let msg :=
                          Message.concat
                            (Message.of_string "Bad let-in function: ")
                            (Message.of_constr f) in
                      Message.print msg;
                        Control.zero (Tactic_failure (Some msg))
               end
          | _
            => let msg := Message.concat
                            (Message.of_string "Unrecognized term: ")
                            (Message.of_constr term) in
               Message.print msg;
                 Control.zero (Tactic_failure (Some msg))
           end)).

Ltac2 reify (var : constr) (term : constr) := reify_helper var term [].

Ltac reify var term :=
  let __ := Ltac1.save_ltac1_result (var, term) in
  let ret :=
      constr:(ltac2:(let args := Ltac1.get_ltac1_result () in
                     (lazy_match! args with
                     | (?var, ?term)
                       => let rv := reify var term in
                          Control.refine (fun () => rv)
                     | _ => Control.throw Not_found
                      end))) in
  let __ := Ltac1.clear_ltac1_results () in
  ret.

Ltac Reify x := Reify_of reify x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs := ReifyCommon.post_Reify_rhs.
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
