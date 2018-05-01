Require Import Reify.Common.
Require Import Reify.BenchmarkUtil.
Require Import Reify.PHOAS.

Ltac print_stats big n ref_PHOAS :=
  let n := (eval lazy in (nat_of_count n)) in
  once (
      idtac "Stats (n=" n "):";
      time (idtac "Doing identity cbv (n=" n ") on PHOAS with" big ":"; let __ := (eval cbv in ref_PHOAS) in idtac);
      time (idtac "Doing identity lazy (n=" n ") on PHOAS with" big ":"; let __ := (eval lazy in ref_PHOAS) in idtac);
      time (idtac "Doing identity vm_compute (n=" n ") on PHOAS with" big ":"; let __ := (eval vm_compute in ref_PHOAS) in idtac);
      time (idtac "Doing identity simpl (n=" n ") on PHOAS with" big ":"; let __ := (eval simpl in ref_PHOAS) in idtac);
      time (idtac "Doing identity cbn (n=" n ") on PHOAS with" big ":"; let __ := (eval cbn in ref_PHOAS) in idtac);
      time (idtac "Doing refine let (n=" n ") on PHOAS with" big ":"; let p := fresh in refine (let p := ref_PHOAS in _); clear p);
      time (idtac "Doing cbv Denote (n=" n ") on PHOAS with" big ":"; let v := (eval cbv [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac);
      time (idtac "Doing lazy Denote (n=" n ") on PHOAS with" big ":"; let v := (eval lazy [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac);
      time (idtac "Doing cbn Denote (n=" n ") on PHOAS with" big ":"; let v := (eval cbn [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac);
      time (idtac "Doing simpl Denote (n=" n ") on PHOAS with" big ":"; let v := (eval simpl in (PHOAS.Denote ref_PHOAS)) in idtac);
      time (idtac "Doing transitivity (n=" n ") on PHOAS with" big ":";
            try (assert (p : 0 = 0);
                 [ transitivity (Denote ref_PHOAS); fail | ]));
      idtac
    ).

Ltac print_native_stats big n ref_PHOAS :=
  let n := (eval lazy in (nat_of_count n)) in
  once (
      idtac "Stats-native (n=" n "):";
      time (idtac "Doing identity native_compute (n=" n ") on PHOAS with" big ":"; let __ := (eval native_compute in ref_PHOAS) in idtac)
    ).
