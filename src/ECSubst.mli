open Datatypes
open EAst
open EPrimitive
open List0
open Nat0
open PeanoNat

val csubst : term -> nat -> term -> term

val substl : term list -> term -> term
