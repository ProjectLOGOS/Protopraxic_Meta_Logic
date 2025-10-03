open Datatypes

type t =
| F1 of nat
| FS of nat * t

val of_nat_lt : nat -> nat -> t
