open Classes0
open Datatypes

val nat_eqdec : nat -> nat -> nat dec_eq

val nat_EqDec : nat coq_EqDec

val prod_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) coq_EqDec
