open Datatypes
open OrderedType0

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OrderedType_from_Alt =
 functor (O:OrderedTypeAlt) ->
 struct
  type t = O.t

  (** val compare : O.t -> O.t -> O.t coq_Compare **)

  let compare x y =
    match O.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false
 end
