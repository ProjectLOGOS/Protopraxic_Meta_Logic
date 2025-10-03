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

(** val mapu_array_model :
    (Level.t -> Level.t) -> ('a1 -> 'a2) -> 'a1 array_model -> 'a2 array_model **)

let mapu_array_model fl f ar =
  { array_level = (fl ar.array_level); array_type = (f ar.array_type);
    array_default = (f ar.array_default); array_value =
    (map f ar.array_value) }

(** val mapu_prim :
    (Level.t -> Level.t) -> ('a1 -> 'a2) -> 'a1 prim_val -> 'a2 prim_val **)

let mapu_prim f g = function
| Coq_existT (x, p0) ->
  (match x with
   | Coq_primInt ->
     (match p0 with
      | Coq_primIntModel i -> Coq_existT (Coq_primInt, (Coq_primIntModel i))
      | _ -> assert false (* absurd case *))
   | Coq_primFloat ->
     (match p0 with
      | Coq_primFloatModel f0 ->
        Coq_existT (Coq_primFloat, (Coq_primFloatModel f0))
      | _ -> assert false (* absurd case *))
   | Coq_primString ->
     (match p0 with
      | Coq_primStringModel s ->
        Coq_existT (Coq_primString, (Coq_primStringModel s))
      | _ -> assert false (* absurd case *))
   | Coq_primArray ->
     (match p0 with
      | Coq_primArrayModel a ->
        Coq_existT (Coq_primArray, (Coq_primArrayModel
          (mapu_array_model f g a)))
      | _ -> assert false (* absurd case *)))

(** val test_prim : ('a1 -> bool) -> 'a1 prim_val -> bool **)

let test_prim p = function
| Coq_existT (x, p1) ->
  (match x with
   | Coq_primArray ->
     (match p1 with
      | Coq_primArrayModel a ->
        (&&) ((&&) (forallb p a.array_value) (p a.array_default))
          (p a.array_type)
      | _ -> assert false (* absurd case *))
   | _ -> true)

(** val test_primu :
    (Level.t -> bool) -> ('a1 -> bool) -> 'a1 prim_val -> bool **)

let test_primu p t0 = function
| Coq_existT (x, p1) ->
  (match x with
   | Coq_primArray ->
     (match p1 with
      | Coq_primArrayModel a ->
        (&&)
          ((&&) ((&&) (p a.array_level) (forallb t0 a.array_value))
            (t0 a.array_default)) (t0 a.array_type)
      | _ -> assert false (* absurd case *))
   | _ -> true)
