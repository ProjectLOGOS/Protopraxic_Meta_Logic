open BinInt
open BinNums
open Datatypes
open PrimInt63

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_zero : Uint63.t -> bool **)

let is_zero i =
  eqb i (Uint63.of_int (0))

(** val is_even : Uint63.t -> bool **)

let is_even i =
  is_zero (coq_land i (Uint63.of_int (1)))

(** val opp : Uint63.t -> Uint63.t **)

let opp i =
  sub (Uint63.of_int (0)) i

(** val to_Z_rec : nat -> Uint63.t -> coq_Z **)

let rec to_Z_rec n i =
  match n with
  | O -> Z0
  | S n0 ->
    if is_even i
    then Z.double (to_Z_rec n0 (coq_lsr i (Uint63.of_int (1))))
    else Z.succ_double (to_Z_rec n0 (coq_lsr i (Uint63.of_int (1))))

(** val to_Z : Uint63.t -> coq_Z **)

let to_Z =
  to_Z_rec size

(** val of_pos_rec : nat -> positive -> Uint63.t **)

let rec of_pos_rec n p =
  match n with
  | O -> (Uint63.of_int (0))
  | S n0 ->
    (match p with
     | Coq_xI p0 ->
       coq_lor (coq_lsl (of_pos_rec n0 p0) (Uint63.of_int (1)))
         (Uint63.of_int (1))
     | Coq_xO p0 -> coq_lsl (of_pos_rec n0 p0) (Uint63.of_int (1))
     | Coq_xH -> (Uint63.of_int (1)))

(** val of_pos : positive -> Uint63.t **)

let of_pos =
  of_pos_rec size

(** val of_Z : coq_Z -> Uint63.t **)

let of_Z = function
| Z0 -> (Uint63.of_int (0))
| Zpos p -> of_pos p
| Zneg p -> opp (of_pos p)
