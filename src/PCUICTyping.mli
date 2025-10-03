open Datatypes
open Kernames
open PCUICAst
open PCUICPrimitive
open Primitive
open Specif
open Universes0

val type_of_constructor :
  PCUICEnvironment.mutual_inductive_body -> PCUICEnvironment.constructor_body
  -> (inductive * nat) -> Level.t list -> term

type coq_FixCoFix =
| Fix
| CoFix

val prim_type : term prim_val -> kername -> term
