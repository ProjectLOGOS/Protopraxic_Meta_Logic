open Datatypes
open String0

val map_fst : ('a1 -> 'a2) -> ('a1 * 'a3) -> 'a2 * 'a3

val timed : string -> (unit -> 'a1) -> 'a1
