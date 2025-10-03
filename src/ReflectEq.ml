open Bool
open Classes0
open Datatypes
open PeanoNat

(** val reflectProp_reflect : bool -> reflect **)

let reflectProp_reflect = function
| true -> ReflectT
| false -> ReflectF

type 'a coq_ReflectEq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_ReflectEq *)

(** val eqb_specT : 'a1 coq_ReflectEq -> 'a1 -> 'a1 -> reflect **)

let eqb_specT hR x y =
  reflectProp_reflect (hR x y)

(** val coq_ReflectEq_EqDec : 'a1 coq_ReflectEq -> 'a1 coq_EqDec **)

let coq_ReflectEq_EqDec r x y =
  let filtered_var = r x y in if filtered_var then true else false

(** val eq_option :
    ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool **)

let eq_option eqA u v =
  match u with
  | Some u0 -> (match v with
                | Some v0 -> eqA u0 v0
                | None -> false)
  | None -> (match v with
             | Some _ -> false
             | None -> true)

(** val reflect_option : 'a1 coq_ReflectEq -> 'a1 option coq_ReflectEq **)

let reflect_option =
  eq_option

(** val eqb_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec eqb_list eqA l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | a :: l0 ->
    (match l' with
     | [] -> false
     | a' :: l'0 -> if eqA a a' then eqb_list eqA l0 l'0 else false)

(** val reflect_list : 'a1 coq_ReflectEq -> 'a1 list coq_ReflectEq **)

let reflect_list =
  eqb_list

(** val reflect_nat : nat coq_ReflectEq **)

let reflect_nat =
  Nat.eqb

(** val eq_bool : bool -> bool -> bool **)

let eq_bool b1 b2 =
  if b1 then b2 else negb b2

(** val reflect_bool : bool coq_ReflectEq **)

let reflect_bool =
  eq_bool

(** val eq_prod :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) ->
    ('a1 * 'a2) -> bool **)

let eq_prod eqA eqB x y =
  let (a1, b1) = x in
  let (a2, b2) = y in if eqA a1 a2 then eqB b1 b2 else false

(** val reflect_prod :
    'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) coq_ReflectEq **)

let reflect_prod =
  eq_prod
