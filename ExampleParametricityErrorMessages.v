(** * Reading Error Messages from [pattern] in reification by parametricity *)

(** Coq's error messages can sometimes be opaque, so we describe here
    how to make sense of them.

    The rule of thumb for reification by parametricity is that for any
    given type, either all constants and identifiers that touch that
    type must be reified, or else the type must not be reified at all.

    For example, when reifying the expression [1 + 2], either [O],
    [S], and [Nat.add] must all be reified, or you cannot reify [nat]
    at all.

    Coq reports violations of this rule as "application errors".  If
    you reified the arguments of a function but not the function
    itself, then you will get an error saying that you cannot apply
    the unreified function to reified arguments; the solution is to
    also reify that function.  If you reified a function but forgot to
    reify its arguments, coq will tell you that the reified function
    cannot be applied to the unreified arguments.  These two sorts of
    errors look slightly different, so we give examples of both of
    them here.

    Suppose we are reifying [nat] expressions.  We might write: *)

Inductive NatExpr :=
| NatO
| NatS (x : NatExpr)
| NatAdd (x y : NatExpr)
| NatMul (x y : NatExpr).

Ltac reify x :=
  let r := lazymatch (eval pattern nat, Nat.add in x) with
           | ?r _ _ => r end in
  constr:(r NatExpr NatAdd).

Goal True.
  Fail let c := reify (1 + 2) in
       pose c.

  (** We see the error message:
<<
The command has indeed failed with message:
Ltac call to "reify" failed.
Illegal application:
The term "n" of type "P -> P -> P"
cannot be applied to the terms
 "1" : "nat"
 "2" : "nat"
The 1st term has type "nat" which should be coercible to "P".
>>

   *)

  (** Coq is telling us that some reified constant (called [n]) was
      applied to the unreified arguments [1 : nat] and [2 : nat].  We
      forgot to reify successor!  We might redefine [reify] as
      follows: *)

  Ltac reify x ::=
    let r := lazymatch (eval pattern nat, Nat.add, S, O in x) with
             | ?r _ _ _ _ => r end in
    constr:(r NatExpr NatAdd NatS NatO).

  let c := reify (1 + 2) in
  pose c.

  (** This works!  If we try to reify a multiplication, though, we get
      an error: *)

  Fail let c := reify (1 + 2 * 3) in
       pose c.

  (** This time, we see the error message:
<<
The command has indeed failed with message:
Ltac call to "reify" failed.
Illegal application:
The term "Nat.mul" of type "nat -> nat -> nat"
cannot be applied to the terms
 "n1 (n1 n2)" : "P"
 "n1 (n1 (n1 n2))" : "P"
The 1st term has type "P" which should be coercible to "nat".
>> *)

  (** Coq is telling us that the unreified function [Nat.mul] cannot
      be applied to reified arguments (which are [n1 (n1 n2)] and [n1
      (n1 (n1 n2))] (apparently [S] got reified as [n1] and [O] got
      reified as [n2])).  The solution is to also reify [Nat.mul];
      this works: *)

  Ltac reify x ::=
    let r := lazymatch (eval pattern nat, Nat.add, S, O, Nat.mul in x) with
             | ?r _ _ _ _ _ => r end in
    constr:(r NatExpr NatAdd NatS NatO NatMul).

  let c := reify (1 + 2 * 3) in
  pose c.

  (** You may also get other error messages which do not arise from
      [pattern]; if you have too many underscores, Coq will tell you
      that no branch matches.  If you plug in the reified constants in
      a different order than you patterned them in, you may get typing
      errors from the [constr].  If you don't [pattern] a constant
      before patterning the types you want to reify mentioned in that
      constant (e.g., if you write [pattern Nat.add, nat] rather than
      [pattern nat, Nat.add], reification of the constant will not
      work. *)
Abort.
