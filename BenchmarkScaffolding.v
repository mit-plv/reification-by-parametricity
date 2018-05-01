Require Import Coq.Lists.List.
Require Export Coq.Strings.String.
Require Import Reify.Sandbox.
Require Import Reify.ReifyCommon.
Require Import Reify.PHOASUtil.
Require Export Reify.BenchmarkUtil. (* don't qualify BenchmarkUtil.big when naming it *)
Require Reify.Parametricity.

Global Coercion count_of_nat : nat >-> count.

Ltac make_ref do_eval_cbv big ns :=
  let rv :=
      (eval cbv beta in
          (fun var : Type
           => ltac:(let v := do_eval_cbv
                               (List.map (fun n => (n, big n)) ns) in
                    let rv := Parametricity.reify var v in
                    exact rv))) in
  let rv :=
      lazymatch rv with
      | (fun var => List.map (fun n => (n, @?rx n var)) ns)
        => constr:(List.map (fun n => dlet rx' := rx n in (n, rx')) ns)
      end in
  let rv := (eval cbv beta in rv) in
  exact rv.

Definition big_refs' (ns : list count) : list (count * PHOAS.Expr).
Proof. make_ref ltac:(fun v => eval lazy delta [big] in v) (big 1) ns. Defined.
Definition big_flat_refs' (ns : list count) : list (count * PHOAS.Expr).
Proof. make_ref ltac:(fun v => eval lazy [big_flat] in v) (big_flat 1) ns. Defined.
Definition big_refs (ns : list nat) := big_refs' (@List.map nat count id ns).
Definition big_flat_refs (ns : list nat) := big_flat_refs' (@List.map nat count id ns).

(** To avoid running out of memory on the medium-size Ltac variants,
    which create many evars, we make sure to erase the new evars
    introduced. *)
Ltac do_test_with big do_cbv pre_reify do_reify post_reify n ref_PHOAS :=
  let H := fresh in
  sandbox
    ltac:(fun _
          => assert (H : exists v, v = big 1 n);
             [ eexists;
               once (do_cbv n);
               once (pre_reify n);
               once (do_reify n);
               once (post_reify n);
               if_doing_trans ltac:(fun _ => check_sane ref_PHOAS);
               reflexivity
             | clear H ]);
  idtac.

Global Open Scope string_scope.
Global Set Printing Width 100000.

Tactic Notation "do_test_with" constr(name) constr(big) tactic3(do_cbv) tactic3(pre_reify) tactic3(do_reify) tactic3(post_reify) constr(n) constr(ref_PHOAS) :=
  let n := (eval lazy in (nat_of_count n)) in
  idtac "Starting test (n=" n ") for" name;
  time "aggregate" once (
         do_test_with
           big
           ltac:(fun n' => idtac "Doing cbv  (n=" n ") for" name "with" big ":"; time "cbv" do_cbv)
           ltac:(fun n' => idtac "Doing pre  (n=" n ") for" name "with" big ":"; time "pre" pre_reify ())
           ltac:(fun n' => [ > idtac "Doing reif (n=" n ") for" name "with" big ":" | .. ]; time "reif" do_reify ())
           ltac:(fun n' => [ > idtac "Doing post (n=" n ") for" name "with" big ":" | .. ]; time "post" post_reify ())
                  n ref_PHOAS;
         idtac "Aggregate time (n=" n ") for" name "with" big ":").

Global Arguments Let_In : simpl never.
Global Arguments Nat.mul : simpl never.
Global Arguments PHOAS.denote / .
Global Arguments PHOAS.Denote / .

Ltac foreach tac ns :=
  lazymatch ns with
  | cons ?n ?ns => once (tac n); foreach tac ns
  | nil => idtac
  end.
Ltac foreach2 tac ns :=
  lazymatch ns with
  | cons (?n, ?x) ?ns => once (tac n x); foreach2 tac ns
  | nil => idtac
  end.
Ltac foreach3 tac ns :=
  lazymatch ns with
  | cons (?n, ?x, ?y) ?ns => once (tac n x y); foreach3 tac ns
  | nil => idtac
  end.
Ltac noop _ := idtac.

Global Open Scope nat_scope.

Ltac do_cbv_delta := lazy [big_flat count_of_nat]; lazy delta [big].
Ltac do_cbv := lazy [big_flat big big_flat_op count_of_nat].

Inductive speed_classifier : Set :=
| quick (* less than 1 s *)
| medium (* not more than around 1 m *)
| slow (* more than a minute *).
Inductive speed_or_test_classifier : Set :=
| test
| speed_of (_ : speed_classifier).
Coercion speed_of : speed_classifier >-> speed_or_test_classifier.

Definition min_n (max_n_from_flat_and_speed : bool -> speed_classifier -> nat)
           (is_flat : bool) (speed : speed_or_test_classifier)
  : nat
  := match speed with
     | test => 4
     | quick => 0
     | medium => max_n_from_flat_and_speed is_flat quick
     | slow => max_n_from_flat_and_speed is_flat medium
     end.

Definition max_n (max_n_from_flat_and_speed : bool -> speed_classifier -> nat)
           (is_flat : bool) (speed : speed_or_test_classifier)
  : nat
  := match speed with
     | test => S (min_n max_n_from_flat_and_speed is_flat speed)
     | speed_of speed => max_n_from_flat_and_speed is_flat speed
     end.

Definition sequence : list nat
  := (*Eval lazy in*)
    (List.seq 1 499)
      ++ (List.map (fun n => 500 + n * 5) (seq 0 100))
      ++ (List.map (fun n => 1000 + n * 10) (seq 0 100))
      ++ (List.map (fun n => 2 * 1000 + n * 50) (seq 0 160))
      ++ (List.map (fun n => 10 * 1000 + n * 100) (seq 0 100))
      ++ 200 * 100::nil.

Definition get_ns_with_refs
           (max_n_from_flat_and_speed : bool -> speed_classifier -> nat)
           (is_flat : bool) (speed : speed_or_test_classifier)
  := let max_n := max_n max_n_from_flat_and_speed is_flat speed in
     let min_n := min_n max_n_from_flat_and_speed is_flat speed in
     let ns := List.filter (fun n => Nat.ltb min_n n && Nat.leb n max_n)%bool
                           sequence in
     if is_flat then big_flat_refs ns else big_refs ns.

Ltac scaffold_test test_tac max_n_from_flat_and_speed is_flat speed :=
  let big := lazymatch is_flat with
             | true => big_flat
             | false => big
             end in
  let ns_with_refs
      := (eval lazy in (get_ns_with_refs max_n_from_flat_and_speed is_flat speed)) in
  foreach2 ltac:(test_tac big) ns_with_refs.
