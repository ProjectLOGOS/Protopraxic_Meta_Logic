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
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'term array_model = { array_default : 'term; array_value : 'term list }

type 'term prim_model =
| Coq_primIntModel of Uint63.t
| Coq_primFloatModel of Float64.t
| Coq_primStringModel of string
| Coq_primArrayModel of 'term array_model

type 'term prim_val = (prim_tag, 'term prim_model) sigT

(** val string_of_prim : ('a1 -> String.t) -> 'a1 prim_val -> String.t **)

let string_of_prim soft p =
  match projT2 p with
  | Coq_primIntModel f ->
    String.append (String.String (Coq_x28, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
      (Coq_x3a, (String.String (Coq_x20, String.EmptyString))))))))))))
      (String.append (string_of_prim_int f) (String.String (Coq_x29,
        String.EmptyString)))
  | Coq_primFloatModel f ->
    String.append (String.String (Coq_x28, (String.String (Coq_x66,
      (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
      (Coq_x61, (String.String (Coq_x74, (String.String (Coq_x3a,
      (String.String (Coq_x20, String.EmptyString))))))))))))))))
      (String.append (string_of_float f) (String.String (Coq_x29,
        String.EmptyString)))
  | Coq_primStringModel s ->
    String.append (String.String (Coq_x28, (String.String (Coq_x73,
      (String.String (Coq_x74, (String.String (Coq_x72, (String.String
      (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x67,
      (String.String (Coq_x3a, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))
      (String.append (string_of_pstring s) (String.String (Coq_x29,
        String.EmptyString)))
  | Coq_primArrayModel a ->
    String.append (String.String (Coq_x28, (String.String (Coq_x61,
      (String.String (Coq_x72, (String.String (Coq_x72, (String.String
      (Coq_x61, (String.String (Coq_x79, (String.String (Coq_x3a,
      String.EmptyString))))))))))))))
      (String.append (soft a.array_default)
        (String.append (String.String (Coq_x20, (String.String (Coq_x2c,
          (String.String (Coq_x20, String.EmptyString))))))
          (String.append (string_of_list soft a.array_value) (String.String
            (Coq_x29, String.EmptyString)))))

(** val test_array_model : ('a1 -> bool) -> 'a1 array_model -> bool **)

let test_array_model f a =
  (&&) (f a.array_default) (forallb f a.array_value)

(** val test_prim : ('a1 -> bool) -> 'a1 prim_val -> bool **)

let test_prim f p =
  match projT2 p with
  | Coq_primArrayModel a -> test_array_model f a
  | _ -> true

(** val fold_prim : ('a2 -> 'a1 -> 'a2) -> 'a1 prim_val -> 'a2 -> 'a2 **)

let fold_prim f p acc =
  match projT2 p with
  | Coq_primArrayModel a -> fold_left f a.array_value (f acc a.array_default)
  | _ -> acc

(** val map_array_model :
    ('a1 -> 'a2) -> 'a1 array_model -> 'a2 array_model **)

let map_array_model f a =
  { array_default = (f a.array_default); array_value = (map f a.array_value) }

(** val map_prim : ('a1 -> 'a2) -> 'a1 prim_val -> 'a2 prim_val **)

let map_prim f p =
  match projT2 p with
  | Coq_primIntModel f0 -> Coq_existT (Coq_primInt, (Coq_primIntModel f0))
  | Coq_primFloatModel f0 ->
    Coq_existT (Coq_primFloat, (Coq_primFloatModel f0))
  | Coq_primStringModel f0 ->
    Coq_existT (Coq_primString, (Coq_primStringModel f0))
  | Coq_primArrayModel a ->
    Coq_existT (Coq_primArray, (Coq_primArrayModel (map_array_model f a)))

(** val map_primIn : 'a1 prim_val -> ('a1 -> __ -> 'a1) -> 'a1 prim_val **)

let map_primIn p f =
  let Coq_existT (x, p0) = p in
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
        Coq_existT (Coq_primArray, (Coq_primArrayModel { array_default =
          (f a.array_default __); array_value =
          (map_InP a.array_value (fun x0 _ -> f x0 __)) }))
      | _ -> assert false (* absurd case *)))
