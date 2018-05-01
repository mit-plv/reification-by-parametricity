(** * Reification by Ltac2, using unsafe low-level primitives *)
Require Import Reify.ReifyCommon.
Require Import Reify.Ltac2Common.
Import Ltac2.Init.
Import Ltac2.Notations.

Ltac2 if_doing_trans (tac : unit -> 'a) (default : 'a) :=
  let do_trans := '(do_transitivity) in
  (lazy_match! do_trans with
  | true => tac ()
  | false => default
  end).

(** This function is parameterized over the constants which we are
    reifying ([gO], [gS], [gNatMul], [gLetIn]) and over Ltac2
    functions that build applications of the reified versions of these
    functions to reified arguments. *)
Ltac2 rec unsafe_reify_helper
      (mkVar : constr -> 'a)
      (mkO : 'a)
      (mkS : 'a -> 'a)
      (mkNatMul : 'a -> 'a -> 'a)
      (mkLetIn : 'a -> ident option -> constr -> 'a -> 'a)
      (gO : constr)
      (gS : constr)
      (gNatMul : constr)
      (gLetIn : constr)
      (unrecognized : constr -> 'a)
      (term : constr)
  :=
    let reify_rec term :=
        unsafe_reify_helper
          mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn unrecognized term in
    let kterm := Constr.Unsafe.kind term in
    match Constr.equal term gO with
    | true
      => mkO
    | false
      =>
      match kterm with
      | Constr.Unsafe.Rel _ => mkVar term
      | Constr.Unsafe.Var _ => mkVar term
      | Constr.Unsafe.Cast term _ _ => reify_rec term
      | Constr.Unsafe.App f args
        =>
        match Constr.equal f gS with
        | true
          => let x := Array.get args 0 in
             let rx := reify_rec x in
             mkS rx
        | false
          =>
          match Constr.equal f gNatMul with
          | true
            => let x := Array.get args 0 in
               let y := Array.get args 1 in
               let rx := reify_rec x in
               let ry := reify_rec y in
               mkNatMul rx ry
          | false
            =>
            match Constr.equal f gLetIn with
            | true
              => let x := Array.get args 2 (* assume the first two args are type params *) in
                 let f := Array.get args 3 in
                 match Constr.Unsafe.kind f with
                 | Constr.Unsafe.Lambda idx ty body
                   => let rx := reify_rec x in
                      let rf := reify_rec body in
                      mkLetIn rx idx ty rf
                 | _ => unrecognized term
                 end
            | false
              => unrecognized term
            end
          end
        end
      | _
        => unrecognized term
      end
    end.

Ltac2 unsafe_reify (var : constr) (term : constr) :=
  let cVar := '@Var in
  let cO := '@NatO in
  let cS := '@NatS in
  let cNatMul := '@NatMul in
  let cLetIn := '@LetIn in
  let gO := 'O in
  let gS := 'S in
  let gNatMul := '@Nat.mul in
  let gLetIn := '@Let_In in
  let mk0VarArgs :=
      let args := Array.make 1 var in
      args in
  let mk1VarArgs (x : constr) :=
      let args := Array.make 2 var in
      let () := Array.set args 1 x in
      args in
  let mk2VarArgs (x : constr) (y : constr) :=
      let args := Array.make 3 var in
      let () := Array.set args 1 x in
      let () := Array.set args 2 y in
      args in
  let mkApp0 (f : constr) :=
      Constr.Unsafe.make (Constr.Unsafe.App f mk0VarArgs) in
  let mkApp1 (f : constr) (x : constr) :=
      Constr.Unsafe.make (Constr.Unsafe.App f (mk1VarArgs x)) in
  let mkApp2 (f : constr) (x : constr) (y : constr) :=
      Constr.Unsafe.make (Constr.Unsafe.App f (mk2VarArgs x y)) in
  let mkVar (v : constr) := mkApp1 cVar v in
  let mkO := mkApp0 cO in
  let mkS (v : constr) := mkApp1 cS v in
  let mkNatMul (x : constr) (y : constr) := mkApp2 cNatMul x y in
  let mkcLetIn (x : constr) (y : constr) := mkApp2 cLetIn x y in
  let mkLetIn (x : constr) (idx : ident option) (ty : constr) (fbody : constr)
      := mkcLetIn x (Constr.Unsafe.make (Constr.Unsafe.Lambda idx var fbody)) in
  let ret := unsafe_reify_helper
               mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn
               (fun term => term)
               term in
  ret.
Ltac2 check_result (ret : constr) :=
  match Constr.Unsafe.check ret with
  | Val rterm => rterm
  | Err exn => Control.zero exn
  end.
Ltac2 reify (var : constr) (term : constr) :=
  check_result (unsafe_reify var term).

Ltac2 unsafe_Reify (term : constr) :=
  let fresh_set := Fresh.Free.of_constr term in
  let idvar := Fresh.fresh fresh_set @var in
  let var := Constr.Unsafe.make (Constr.Unsafe.Var idvar) in
  let rterm := unsafe_reify var term in
  let rterm := Constr.Unsafe.closenl [idvar] 1 rterm in
  Constr.Unsafe.make (Constr.Unsafe.Lambda (Some idvar) 'Type rterm).

Ltac2 do_Reify (term : constr) :=
  check_result (unsafe_Reify term).

Ltac2 unsafe_mkApp1 (f : constr) (x : constr) :=
  let args := Array.make 1 x in
  Constr.Unsafe.make (Constr.Unsafe.App f args).
Ltac2 mkApp1 (f : constr) (x : constr) :=
  check_result (unsafe_mkApp1 f x).

Ltac2 all_flags :=
  {
    Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
    Std.rZeta := true; Std.rDelta := true; Std.rConst := [];
  }.
Ltac2 betaiota_flags :=
  {
    Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
    Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
  }.
Ltac2 in_goal :=
  { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.

Ltac2 do_Reify_rhs_fast () :=
  let g := Control.goal () in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App f args (* App eq [ty; lhs; rhs] *)
    => let v := Array.get args 2 in
       let rv := Control.time (Some "actual reif")
                              (fun _ => unsafe_Reify v) in
       let rv := Control.time (Some "eval lazy")
                              (fun _ => Std.eval_lazy all_flags rv) in
       Control.time (Some "lazy beta iota")
                    (fun _ => Std.lazy betaiota_flags in_goal);
         if_doing_trans
           (fun _ => Control.time
                       (Some "transitivity (Denote rv)")
                       (fun _ => Std.transitivity (unsafe_mkApp1 'Denote rv))) ()
  | _
    => Control.zero
         (Tactic_failure
            (Some (Message.concat
                     (Message.of_string
                        "Invalid goal in Ltac2Unsafe.do_Reify_rhs_fast: ")
                     (Message.of_constr g))))
  end.

Ltac2 do_Reify_rhs () :=
  (lazy_match! goal with
  | [ |- _ = ?v ]
    => let rv := do_Reify v in
       let rv := Std.eval_lazy all_flags rv in
       if_doing_trans (fun _ => Std.transitivity (mkApp1 'Denote rv)) ()
  | [ |- ?g ] => Control.zero
                   (Tactic_failure
                      (Some (Message.concat
                               (Message.of_string
                                  "Invalid goal in Ltac2Unsafe.do_Reify_rhs: ")
                               (Message.of_constr g))))
   end).

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
(*Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().*)
Ltac do_Reify_rhs _ := ltac2:(do_Reify_rhs_fast ()).
Ltac post_Reify_rhs := ReifyCommon.post_Reify_rhs.
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
