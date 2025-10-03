open Datatypes

val on_snd : ('a2 -> 'a3) -> ('a1 * 'a2) -> 'a1 * 'a3

val test_snd : ('a2 -> bool) -> ('a1 * 'a2) -> bool

type ('p1, 'p2, 'p3) and3 =
| Times3 of 'p1 * 'p2 * 'p3
