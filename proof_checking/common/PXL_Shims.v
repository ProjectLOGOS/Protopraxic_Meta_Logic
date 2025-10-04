Require Import PXLs.proof_checking.pxl_foundation_proof_v1.coq.PXLv3.

Set Implicit Arguments.
(* constructors *)
Notation Var  := Atom.
Notation And  := Conj.
Notation Or   := Disj.
(* types *)
Notation fDisjm := form.  (* undo accidental rename *)