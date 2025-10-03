open Classes0
open Datatypes
open Orders

type __ = Obj.t

module ListOrderedType :
 functor (A:UsualOrderedType) ->
 sig
  type t = A.t list

  val compare : t -> t -> comparison

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val eqb : t -> t -> bool

  val eqb_dec : t -> t -> bool

  val eq_dec : t coq_EqDec
 end
