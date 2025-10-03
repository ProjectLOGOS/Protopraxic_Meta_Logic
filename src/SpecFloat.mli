open BinInt
open BinNums
open BinPos
open Datatypes

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * coq_Z

val emin : coq_Z -> coq_Z -> coq_Z

val fexp : coq_Z -> coq_Z -> coq_Z -> coq_Z

val digits2_pos : positive -> positive

val coq_Zdigits2 : coq_Z -> coq_Z

val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

val shr_1 : shr_record -> shr_record

val shr_record_of_loc : coq_Z -> location -> shr_record

val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z

val shr_fexp :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z
