(** * Ltac-based reification, using uncurrying to reucurse under binders *)
Require Import Reify.ReifyCommon.
Require Import Reify.PrimPair.

(** Points of note:

    - We use primitive projections for pairing to speed up typing.

    - Because we track variables by pairing [nat] binders with fresh
      [var] nodes, we use a [phantom] axiom of type [nat] to fill in
      the now-unused [nat] binder after reification.

    - We make sure to fill in all implicit arguments explicitly, to
      minimize the number of evars generated; evars are one of the
      main bottlenecks.

    - We make use of a trick from "%[coqdev]% beta1 and zeta1
      reduction"%\footnote{\url{https://sympa.inria.fr/sympa/arc/coqdev/2016-01/msg00060.html}}%
      to bind names with a single-branch [match] statement without
      incurring extra β or ζ reductions.

    - We give the [return] clause on the [match] statement explicitly
      to work around
      %\url{https://github.com/coq/coq/issues/6252\#issuecomment-347041995}%
      and prevent extra backtracking, as well as preventing extra evar
      allocation. *)

Axiom phantom : nat.

Ltac reify var term :=
  let reify_rec term := reify var term in
  lazymatch term with
  | (fun args : ?T => O)
    => constr:(fun args : T => @NatO var)
  | (fun args : ?T => S (@?x args))
    => let rx := reify_rec x in
       constr:(fun args : T => @NatS var (rx args))
  | fun args : ?T => @?x args * @?y args
    => let rx := reify_rec x in
       let ry := reify_rec y in
       constr:(fun args : T => @NatMul var (rx args) (ry args))
  | (fun args : ?T => dlet x := @?v args in ?f)
    => let rv := reify_rec v in
       let args2 := fresh (*args *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
       let rf :=
           reify_rec
             (fun args2 : (nat * var) * T
              => match @snd (nat * var) T args2,
                       @fst nat var (@fst (nat * var) T args2)
                       return nat
                 with
                 | args, x => f
                 end) in
       constr:(fun args : T
               => @LetIn
                    var
                    (rv args)
                    (fun x : var
                     => rf (@pair (nat * var) T (@pair nat var phantom x) args)))
  | (fun args : ?T => @fst ?A ?B (@fst ?C ?D ?args'))
    => constr:(fun args : T => @Var var (@snd A B (@fst C D args')))
  | (fun args : ?T => _) (* error case *)
    => error_bad_term term
  | ?v
    => let rv := reify_rec (fun dummy : unit => v) in
       (eval lazy beta iota delta [fst snd] in (rv tt))
  end.

Ltac Reify x := Reify_of reify x.
Ltac do_Reify_rhs _ := do_Reify_rhs_of Reify ().
Ltac post_Reify_rhs _ := ReifyCommon.post_Reify_rhs ().
Ltac Reify_rhs _ := Reify_rhs_of Reify ().
