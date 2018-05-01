Declare ML Module "sandbox".

Ltac sandbox tac :=
  catch_success (once tac (); raise_success).
