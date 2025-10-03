open Datatypes
open String0

(** val map_fst : ('a1 -> 'a2) -> ('a1 * 'a3) -> 'a2 * 'a3 **)

let map_fst f p =
  ((f (fst p)), (snd p))

(** val timed : string -> (unit -> 'a1) -> 'a1 **)

let timed _ f =
  f ()
