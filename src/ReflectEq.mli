open Bool
open Classes0
open Datatypes
open PeanoNat

val reflectProp_reflect : bool -> reflect

type 'a coq_ReflectEq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_ReflectEq *)

val eqb_specT : 'a1 coq_ReflectEq -> 'a1 -> 'a1 -> reflect

val coq_ReflectEq_EqDec : 'a1 coq_ReflectEq -> 'a1 coq_EqDec

val eq_option : ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool

val reflect_option : 'a1 coq_ReflectEq -> 'a1 option coq_ReflectEq

val eqb_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val reflect_list : 'a1 coq_ReflectEq -> 'a1 list coq_ReflectEq

val reflect_nat : nat coq_ReflectEq

val eq_bool : bool -> bool -> bool

val reflect_bool : bool coq_ReflectEq

val eq_prod :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) -> ('a1 * 'a2)
  -> bool

val reflect_prod :
  'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) coq_ReflectEq
