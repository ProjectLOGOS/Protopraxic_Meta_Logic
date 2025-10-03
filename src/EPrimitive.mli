open Byte
open List0
open MCList
open MCString
open PrimString
open Primitive
open Show
open Specif
open Bytestring

type __ = Obj.t

type 'term array_model = { array_default : 'term; array_value : 'term list }

type 'term prim_model =
| Coq_primIntModel of Uint63.t
| Coq_primFloatModel of Float64.t
| Coq_primStringModel of string
| Coq_primArrayModel of 'term array_model

type 'term prim_val = (prim_tag, 'term prim_model) sigT

val string_of_prim : ('a1 -> String.t) -> 'a1 prim_val -> String.t

val test_array_model : ('a1 -> bool) -> 'a1 array_model -> bool

val test_prim : ('a1 -> bool) -> 'a1 prim_val -> bool

val fold_prim : ('a2 -> 'a1 -> 'a2) -> 'a1 prim_val -> 'a2 -> 'a2

val map_array_model : ('a1 -> 'a2) -> 'a1 array_model -> 'a2 array_model

val map_prim : ('a1 -> 'a2) -> 'a1 prim_val -> 'a2 prim_val

val map_primIn : 'a1 prim_val -> ('a1 -> __ -> 'a1) -> 'a1 prim_val
