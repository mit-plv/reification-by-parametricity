(*i camlp4deps: "parsing/grammar.cma" i*)

open Ltac_plugin

exception TacticSuccess

let tclRAISE_SUCCESS =
    Proofview.tclZERO TacticSuccess

let tclCATCH_SUCCESS t =
    Proofview.tclORELSE
	t
	(function
	| (TacticSuccess, _) -> Proofview.tclUNIT ()
	| (e, info) -> Proofview.tclZERO ~info e)

DECLARE PLUGIN "sandbox"

open Stdarg
open Tacarg

TACTIC EXTEND raise_success
| [ "raise_success" ] -> [ tclRAISE_SUCCESS ]
END;;

TACTIC EXTEND catch_success
| [ "catch_success" tactic3(tac) ] -> [ tclCATCH_SUCCESS (Tacinterp.tactic_of_value ist tac) ]
END;;
