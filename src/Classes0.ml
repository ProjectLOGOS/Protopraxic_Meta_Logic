
type __ = Obj.t

type 'a coq_NoConfusionPackage =
| Build_NoConfusionPackage

type 'a dec_eq = bool

type 'a coq_EqDec = 'a -> 'a -> bool

(** val eq_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let eq_dec eqDec =
  eqDec

type 'a coq_EqDecPoint = 'a -> bool

(** val eq_dec_point : 'a1 -> 'a1 coq_EqDecPoint -> 'a1 -> bool **)

let eq_dec_point _ eqDecPoint =
  eqDecPoint

(** val coq_EqDec_EqDecPoint : 'a1 coq_EqDec -> 'a1 -> 'a1 coq_EqDecPoint **)

let coq_EqDec_EqDecPoint =
  eq_dec

type 'a coq_FunctionalInduction =
  __
  (* singleton inductive, whose constructor was Build_FunctionalInduction *)
