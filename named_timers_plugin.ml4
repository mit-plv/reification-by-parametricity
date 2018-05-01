(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp

module M = CString.Map

let timer_data = ref M.empty

let timer_name = function
  | Some v -> v
  | None -> ""

let restart_timer name =
  timer_data := M.add (timer_name name) (System.get_time ()) !timer_data

let get_timer name =
  try M.find (timer_name name) !timer_data
  with Not_found -> System.get_time ()

let finish_timing ~prefix name =
  let tend = System.get_time () in
  let tstart = get_timer name in
  Feedback.msg_info(str prefix ++ pr_opt str name ++ str " ran for " ++
		      System.fmt_time_difference tstart tend)

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "named_timers"

let tclRESTART_TIMER s =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> restart_timer s))

let tclFINISH_TIMING ?(prefix="Timer") (s : string option) =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> finish_timing ~prefix s))

TACTIC EXTEND restart_timer
| [ "restart_timer" string_opt(s) ] -> [ tclRESTART_TIMER s ]
END

TACTIC EXTEND finish_timing
| [ "finish_timing" string_opt(s) ] -> [ tclFINISH_TIMING ~prefix:"Timer" s ]
| [ "finish_timing" "(" string(prefix) ")" string_opt(s) ] -> [ tclFINISH_TIMING ~prefix s ]
END
