open BinInt
open BinNums
open Datatypes
open PrimInt63

val size : nat

val is_zero : Uint63.t -> bool

val is_even : Uint63.t -> bool

val opp : Uint63.t -> Uint63.t

val to_Z_rec : nat -> Uint63.t -> coq_Z

val to_Z : Uint63.t -> coq_Z

val of_pos_rec : nat -> positive -> Uint63.t

val of_pos : positive -> Uint63.t

val of_Z : coq_Z -> Uint63.t
