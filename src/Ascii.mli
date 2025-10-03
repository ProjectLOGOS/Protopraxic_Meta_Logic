open BinNat
open BinNums
open Bool
open Byte
open Datatypes

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> bool

val eqb : ascii -> ascii -> bool

val eqb_spec : ascii -> ascii -> reflect

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : ascii -> coq_N

val compare : ascii -> ascii -> comparison

val ascii_of_byte : byte -> ascii

val byte_of_ascii : ascii -> byte
