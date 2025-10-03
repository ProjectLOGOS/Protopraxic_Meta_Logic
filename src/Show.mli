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

val show : 'a1 coq_Show -> 'a1 -> String.t

val string_of_specfloat : spec_float -> String.t

val string_of_prim_int : Uint63.t -> String.t

val string_of_float : Float64.t -> String.t

val char63_to_string : char63 -> String.t

val string_of_pstring : string -> String.t

val show_uint : Uint63.t coq_Show

val show_float : Float64.t coq_Show

val show_pstring : string coq_Show
