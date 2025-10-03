open BinInt
open BinNums
open PrimFloat
open SpecFloat
open Uint0

(** val prec : coq_Z **)

let prec =
  Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))

(** val emax : coq_Z **)

let emax =
  Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH))))))))))

(** val shift : coq_Z **)

let shift =
  Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))))

module Z =
 struct
  (** val frexp : Float64.t -> Float64.t * coq_Z **)

  let frexp f =
    let (m, se) = frshiftexp f in (m, (Z.sub (to_Z se) shift))
 end

(** val coq_Prim2SF : Float64.t -> spec_float **)

let coq_Prim2SF f =
  if is_nan f
  then S754_nan
  else if PrimFloat.is_zero f
       then S754_zero (get_sign f)
       else if is_infinity f
            then S754_infinity (get_sign f)
            else let (r, exp) = Z.frexp f in
                 let e = BinInt.Z.sub exp prec in
                 let (shr, e') =
                   shr_fexp prec emax (to_Z (normfr_mantissa r)) e
                     Coq_loc_Exact
                 in
                 (match shr.shr_m with
                  | Zpos p -> S754_finite ((get_sign f), p, e')
                  | _ -> S754_zero false)
