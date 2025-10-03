open List0
open PrimString
open Primitive
open Specif
open Universes0

type __ = Obj.t

type 'term array_model = { array_level : Level.t; array_type : 'term;
                           array_default : 'term; array_value : 'term list }

type 'term prim_model =
| Coq_primIntModel of Uint63.t
| Coq_primFloatModel of Float64.t
| Coq_primStringModel of string
| Coq_primArrayModel of 'term array_model

type 'term prim_val = (prim_tag, 'term prim_model) sigT

type ('term, 'p) tPrimProp = __

val mapu_array_model :
  (Level.t -> Level.t) -> ('a1 -> 'a2) -> 'a1 array_model -> 'a2 array_model

val mapu_prim :
  (Level.t -> Level.t) -> ('a1 -> 'a2) -> 'a1 prim_val -> 'a2 prim_val

val test_prim : ('a1 -> bool) -> 'a1 prim_val -> bool

val test_primu : (Level.t -> bool) -> ('a1 -> bool) -> 'a1 prim_val -> bool
