open BinInt
open BinNums
open PrimFloat
open SpecFloat
open Uint0

val prec : coq_Z

val emax : coq_Z

val shift : coq_Z

module Z :
 sig
  val frexp : Float64.t -> Float64.t * coq_Z
 end

val coq_Prim2SF : Float64.t -> spec_float
