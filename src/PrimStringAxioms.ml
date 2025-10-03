open BinInt
open Datatypes
open List0
open PrimString
open Uint0

(** val to_list : string -> char63 list **)

let to_list s =
  map (fun i -> get s (of_Z (Z.of_nat i)))
    (seq O (Z.to_nat (to_Z (length s))))
