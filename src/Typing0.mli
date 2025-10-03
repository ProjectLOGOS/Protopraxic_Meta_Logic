open Ast0
open Datatypes
open Kernames
open Universes0

val type_of_constructor :
  Env.mutual_inductive_body -> Env.constructor_body -> (inductive * nat) ->
  Level.t list -> term
