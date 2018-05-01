(** * Define a primitive pairing type *)
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Add Printing Let prod.

Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
