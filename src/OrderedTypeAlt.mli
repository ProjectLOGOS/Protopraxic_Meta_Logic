open Datatypes
open OrderedType0

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OrderedType_from_Alt :
 functor (O:OrderedTypeAlt) ->
 sig
  type t = O.t

  val compare : O.t -> O.t -> O.t coq_Compare

  val eq_dec : O.t -> O.t -> bool
 end
