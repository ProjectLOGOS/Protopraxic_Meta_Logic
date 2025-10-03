open CRelationClasses
open Datatypes
open List0

type __ = Obj.t

type ('a, 'p) coq_All =
| All_nil
| All_cons of 'a * 'a list * 'p * ('a, 'p) coq_All

type ('a, 'p) coq_Alli =
| Alli_nil
| Alli_cons of 'a * 'a list * 'p * ('a, 'p) coq_Alli

type ('a, 'b, 'r) coq_All2 =
| All2_nil
| All2_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2

val alli : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val coq_Forall_All : 'a1 list -> ('a1, __) coq_All

val forallb_All : ('a1 -> bool) -> 'a1 list -> ('a1, __) coq_All

val coq_All2_impl :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
  'a4) -> ('a1, 'a2, 'a4) coq_All2

val coq_All_impl :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All

val coq_Alli_impl :
  'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_Alli

val coq_All_map :
  ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a3) coq_All -> ('a2, 'a3) coq_All

val coq_All_map_inv :
  ('a1 -> 'a2) -> 'a1 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All

val coq_Alli_app :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2)
  coq_Alli * ('a1, 'a2) coq_Alli

val coq_Alli_nth_error :
  nat -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2

val forall_nth_error_Alli :
  nat -> 'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_Alli

val coq_Alli_app_inv :
  'a1 list -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli
  -> ('a1, 'a2) coq_Alli

val coq_Alli_rev_nth_error :
  'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2

type size = nat

val coq_All2_from_nth_error :
  'a1 list -> 'a2 list -> (nat -> 'a1 -> 'a2 -> __ -> __ -> __ -> 'a3) ->
  ('a1, 'a2, 'a3) coq_All2

val coq_All2_prod :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
  coq_All2 -> ('a1, 'a2, 'a3 * 'a4) coq_All2

val coq_All_prod_inv :
  'a1 list -> ('a1, 'a2 * 'a3) coq_All -> ('a1, 'a2) coq_All * ('a1, 'a3)
  coq_All

val coq_All_prod :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, 'a2 * 'a3)
  coq_All

type ('a, 'p) coq_All2_fold =
| All2_fold_nil
| All2_fold_cons of 'a * 'a * 'a list * 'a list * ('a, 'p) coq_All2_fold * 'p

type ('a, 'b, 'p) coq_All_over = 'p

val coq_All2_fold_impl :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
  -> 'a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold

val coq_All2_fold_prod :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3)
  coq_All2_fold -> ('a1, 'a2 * 'a3) coq_All2_fold

val coq_All_eta3 :
  (('a1 * 'a2) * 'a3) list -> ((('a1 * 'a2) * 'a3, __) coq_All,
  (('a1 * 'a2) * 'a3, 'a4) coq_All) iffT

val coq_All_All2_swap_sum :
  'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All
  -> (__, ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2) sum

val coq_All_All2_swap :
  'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All
  -> ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2

val coq_All_All2_fold_swap_sum :
  'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold) coq_All
  -> (__, ('a1, ('a2, 'a3) coq_All) coq_All2_fold) sum
