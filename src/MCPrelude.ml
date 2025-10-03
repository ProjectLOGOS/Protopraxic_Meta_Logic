open BinNums
open Classes0

(** val positive_eqdec : positive -> positive -> positive dec_eq **)

let rec positive_eqdec p y =
  match p with
  | Coq_xI p0 -> (match y with
                  | Coq_xI p1 -> positive_eqdec p0 p1
                  | _ -> false)
  | Coq_xO p0 -> (match y with
                  | Coq_xO p1 -> positive_eqdec p0 p1
                  | _ -> false)
  | Coq_xH -> (match y with
               | Coq_xH -> true
               | _ -> false)

(** val positive_EqDec : positive coq_EqDec **)

let positive_EqDec =
  positive_eqdec

(** val coq_Z_eqdec : coq_Z -> coq_Z -> coq_Z dec_eq **)

let coq_Z_eqdec x y =
  match x with
  | Z0 -> (match y with
           | Z0 -> true
           | _ -> false)
  | Zpos p ->
    (match y with
     | Zpos p0 -> eq_dec_point p (coq_EqDec_EqDecPoint positive_EqDec p) p0
     | _ -> false)
  | Zneg p ->
    (match y with
     | Zneg p0 -> eq_dec_point p (coq_EqDec_EqDecPoint positive_EqDec p) p0
     | _ -> false)

(** val coq_Z_EqDec : coq_Z coq_EqDec **)

let coq_Z_EqDec =
  coq_Z_eqdec
