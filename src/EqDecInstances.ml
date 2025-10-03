open Classes0
open Datatypes

(** val nat_eqdec : nat -> nat -> nat dec_eq **)

let rec nat_eqdec n y =
  match n with
  | O -> (match y with
          | O -> true
          | S _ -> false)
  | S n0 -> (match y with
             | O -> false
             | S n1 -> nat_eqdec n0 n1)

(** val nat_EqDec : nat coq_EqDec **)

let nat_EqDec =
  nat_eqdec

(** val prod_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) coq_EqDec **)

let prod_eqdec h h0 x y =
  let (a, b) = x in
  let (a0, b0) = y in
  if eq_dec_point a (coq_EqDec_EqDecPoint h a) a0
  then eq_dec_point b (coq_EqDec_EqDecPoint h0 b) b0
  else false
