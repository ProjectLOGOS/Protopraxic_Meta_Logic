open Datatypes

type t =
| F1 of nat
| FS of nat * t

(** val of_nat_lt : nat -> nat -> t **)

let rec of_nat_lt p = function
| O -> assert false (* absurd case *)
| S n' -> (match p with
           | O -> F1 n'
           | S p' -> FS (n', (of_nat_lt p' n')))
