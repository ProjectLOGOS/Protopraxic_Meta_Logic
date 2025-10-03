open Byte
open ByteCompare
open Classes0
open Datatypes
open ReflectEq

module String :
 sig
  type t =
  | EmptyString
  | String of byte * t

  val append : t -> t -> t

  val eqb : t -> t -> bool

  val compare : t -> t -> comparison

  val concat : t -> t list -> t
 end

module StringOT :
 sig
  type t = String.t

  val compare : String.t -> String.t -> comparison

  val reflect_eq_string : t coq_ReflectEq

  val eq_dec : t -> t -> bool
 end

module Tree :
 sig
  type t =
  | Coq_string of String.t
  | Coq_append of t * t

  val to_rev_list_aux : t -> String.t list -> String.t list

  val to_string_acc : String.t -> String.t list -> String.t

  val to_string : t -> String.t

  val string_of_list_aux : ('a1 -> t) -> t -> 'a1 list -> t

  val string_of_list : ('a1 -> t) -> 'a1 list -> t

  val print_list : ('a1 -> t) -> t -> 'a1 list -> t

  val parens : bool -> t -> t
 end
