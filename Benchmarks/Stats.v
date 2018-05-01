Require Export Reify.BenchmarkScaffolding.
Require Import Reify.BaselineStats.

Definition max_stats_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 125 * 100
     | medium, true => 30 * 1000
     | quick, false => 3 * 1000
     | medium, false => 10 * 1000
     | slow, _ => 30 * 1000
     end.

Definition max_native_n (is_flat : bool) (speed : speed_classifier) : nat
  := match speed, is_flat with
     | quick, true => 125 * 100
     | medium, true => 30 * 1000
     | slow, true => 30 * 1000
     | quick, false => 800
     | medium, false => 4000
     | slow, false => 5 * 1000
     end.

Ltac do_test_Stats is_flat speed :=
  scaffold_test ltac:(fun big n refP => print_stats big n refP) max_stats_n is_flat speed;
  scaffold_test ltac:(fun big n refP => print_native_stats big n refP) max_native_n is_flat speed;
  idtac.

Goal True. (* test *)
  Redirect "/tmp/silence" do_test_Stats true test.
  Redirect "/tmp/silence" do_test_Stats false test.
Abort.
