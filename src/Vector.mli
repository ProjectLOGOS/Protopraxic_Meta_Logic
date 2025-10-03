open Datatypes
open Fin
open Nat0
open VectorDef

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t

val nth : nat -> 'a1 t -> Fin.t -> 'a1

val nth_order : nat -> 'a1 t -> nat -> 'a1
