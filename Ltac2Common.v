(** * Common utility definitions for Ltac2 *)
Require Ltac2.Ltac2.
Import Ltac2.Init.
Import Ltac2.Notations.

Module List.
  Ltac2 rec map f ls :=
    match ls with
    | [] => []
    | l :: ls => f l :: map f ls
    end.
End List.
Module Ident.
  Ltac2 rec find_error id xs :=
    match xs with
    | [] => None
    | x :: xs
      => let ((id', val)) := x in
         match Ident.equal id id' with
         | true => Some val
         | false => find_error id xs
         end
    end.
  Ltac2 find id xs :=
    match find_error id xs with
    | None => Control.zero Not_found
    | Some val => val
    end.
End Ident.
Module Array.
  Ltac2 rec to_list_aux (ls : 'a array) (start : int) :=
    match Int.equal (Int.compare start (Array.length ls)) -1 with
    | true => Array.get ls start :: to_list_aux ls (Int.mul start 1)
    | false => []
    end.
  Ltac2 to_list (ls : 'a array) := to_list_aux ls 0.
End Array.
Module Constr.
  Ltac2 rec strip_casts term :=
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Cast term' _ _ => strip_casts term'
    | _ => term
    end.
  Module Unsafe.
    Ltac2 beta1 (c : constr) :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.App f args
        => match Constr.Unsafe.kind f with
           | Constr.Unsafe.Lambda id ty f
             => Constr.Unsafe.substnl (Array.to_list args) 0 f
           | _ => c
           end
      | _ => c
      end.
    Ltac2 zeta1 (c : constr) :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.LetIn id v ty f
        => Constr.Unsafe.substnl [v] 0 f
      | _ => c
      end.
  End Unsafe.
End Constr.
Module Ltac1.
  Class Ltac1Result {T} (v : T) := {}.
  Class Ltac1Results {T} (v : list T) := {}.
  Class Ltac2Result {T} (v : T) := {}.
  Ltac save_ltac1_result v :=
    match goal with
    | _ => assert (Ltac1Result v) by constructor
    end.
  Ltac clear_ltac1_results _ :=
    match goal with
    | _ => repeat match goal with
                  | [ H : Ltac1Result _ |- _ ] => clear H
                  end
    end.
  Ltac2 get_ltac1_result () :=
    (lazy_match! goal with
    | [ id : Ltac1Result ?v |- _ ]
      => Std.clear [id]; v
     end).

  Ltac save_ltac1_results v :=
    match goal with
    | _ => assert (Ltac1Result v) by constructor
    end.
  Ltac2 save_ltac2_result v :=
    Std.cut '(Ltac2Result $v);
      Control.dispatch
        [(fun ()
          => Std.intros false [Std.IntroNaming (Std.IntroFresh @res)])
         ;
         (fun () => Notations.constructor)].
  Ltac get_ltac2_result _ :=
    lazymatch goal with
    | [ res : Ltac2Result ?v |- _ ]
      => let __ := match goal with
                   | _ => clear res
                   end in
         v
    end.
  Ltac2 from_ltac1 (save_args : constr) (tac : unit -> unit) :=
    let beta_flag :=
        {
          Std.rBeta := true; Std.rMatch := false;
          Std.rFix := false; Std.rCofix := false;
          Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
        } in
    let c := '(ltac2:(save_ltac2_result save_args;
                        tac ();
                        let v := get_ltac1_result () in
                        Control.refine (fun () => v))) in
    Constr.Unsafe.zeta1 (Constr.Unsafe.zeta1 (Std.eval_cbv beta_flag c)).
End Ltac1.
