open BinInt
open Byte
open Byte0
open FloatOps
open MCString
open PrimString
open PrimStringAxioms
open SpecFloat
open Uint0
open Bytestring

type 'a coq_Show = 'a -> String.t

(** val show : 'a1 coq_Show -> 'a1 -> String.t **)

let show show0 =
  show0

(** val string_of_specfloat : spec_float -> String.t **)

let string_of_specfloat = function
| S754_zero sign ->
  if sign
  then String.String (Coq_x2d, (String.String (Coq_x30, String.EmptyString)))
  else String.String (Coq_x30, String.EmptyString)
| S754_infinity sign ->
  if sign
  then String.String (Coq_x2d, (String.String (Coq_x69, (String.String
         (Coq_x6e, (String.String (Coq_x66, (String.String (Coq_x69,
         (String.String (Coq_x6e, (String.String (Coq_x69, (String.String
         (Coq_x74, (String.String (Coq_x79,
         String.EmptyString)))))))))))))))))
  else String.String (Coq_x69, (String.String (Coq_x6e, (String.String
         (Coq_x66, (String.String (Coq_x69, (String.String (Coq_x6e,
         (String.String (Coq_x69, (String.String (Coq_x74, (String.String
         (Coq_x79, String.EmptyString)))))))))))))))
| S754_nan ->
  String.String (Coq_x6e, (String.String (Coq_x61, (String.String (Coq_x6e,
    String.EmptyString)))))
| S754_finite (sign, p, z) ->
  let num =
    String.append (string_of_positive p)
      (String.append (String.String (Coq_x70, String.EmptyString))
        (string_of_Z z))
  in
  if sign
  then String.append (String.String (Coq_x2d, String.EmptyString)) num
  else num

(** val string_of_prim_int : Uint63.t -> String.t **)

let string_of_prim_int i =
  string_of_Z (to_Z i)

(** val string_of_float : Float64.t -> String.t **)

let string_of_float f =
  string_of_specfloat (coq_Prim2SF f)

(** val char63_to_string : char63 -> String.t **)

let char63_to_string c =
  let b =
    match of_N (BinInt.Z.to_N (to_Z c)) with
    | Some b -> b
    | None -> Coq_x00
  in
  String.String (b, String.EmptyString)

(** val string_of_pstring : string -> String.t **)

let string_of_pstring s =
  string_of_list char63_to_string (to_list s)

(** val show_uint : Uint63.t coq_Show **)

let show_uint =
  string_of_prim_int

(** val show_float : Float64.t coq_Show **)

let show_float =
  string_of_float

(** val show_pstring : string coq_Show **)

let show_pstring =
  string_of_pstring
