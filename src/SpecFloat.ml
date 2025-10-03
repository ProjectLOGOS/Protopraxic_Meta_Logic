open BinInt
open BinNums
open BinPos
open Datatypes

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * coq_Z

(** val emin : coq_Z -> coq_Z -> coq_Z **)

let emin prec emax =
  Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec

(** val fexp : coq_Z -> coq_Z -> coq_Z -> coq_Z **)

let fexp prec emax e =
  Z.max (Z.sub e prec) (emin prec emax)

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| Coq_xI p -> Pos.succ (digits2_pos p)
| Coq_xO p -> Pos.succ (digits2_pos p)
| Coq_xH -> Coq_xH

(** val coq_Zdigits2 : coq_Z -> coq_Z **)

let coq_Zdigits2 n = match n with
| Z0 -> n
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  match n with
  | Coq_xI n' -> iter_pos f n' (iter_pos f n' (f x))
  | Coq_xO n' -> iter_pos f n' (iter_pos f n' x)
  | Coq_xH -> f x

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val shr_record_of_loc : coq_Z -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z **)

let shr mrs e n = match n with
| Zpos p -> ((iter_pos shr_1 p mrs), (Z.add e n))
| _ -> (mrs, e)

(** val shr_fexp :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z **)

let shr_fexp prec emax m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec emax (Z.add (coq_Zdigits2 m) e)) e)
