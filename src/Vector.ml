open Datatypes
open Fin
open Nat0
open VectorDef

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t

(** val nth : nat -> 'a1 t -> Fin.t -> 'a1 **)

let rec nth _ v p =
  match v with
  | Coq_nil -> assert false (* absurd case *)
  | Coq_cons (x, _, v') ->
    (match p with
     | F1 _ -> x
     | FS (n0, p') -> nth (pred (S n0)) v' p')

(** val nth_order : nat -> 'a1 t -> nat -> 'a1 **)

let nth_order n v p =
  nth n v (of_nat_lt p n)
