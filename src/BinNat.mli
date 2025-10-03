open BinNums
open BinPos
open Datatypes

module N :
 sig
  val add : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N

  val compare : coq_N -> coq_N -> comparison

  val eqb : coq_N -> coq_N -> bool
 end
