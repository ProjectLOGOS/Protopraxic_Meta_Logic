open Datatypes

type __ = Obj.t

val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list

val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val rev : 'a1 list -> 'a1 list

val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val chop : nat -> 'a1 list -> 'a1 list * 'a1 list

val unfold : nat -> (nat -> 'a1) -> 'a1 list

val map_In : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list

val map_InP : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list
