open Datatypes
open EAst
open ECSubst
open EEnvMap
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCProd

val isprop_ind : GlobalContextMap.t -> (inductive * nat) -> bool

val remove_match_on_box : GlobalContextMap.t -> term -> term

val remove_match_on_box_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val remove_match_on_box_decl :
  GlobalContextMap.t -> global_decl -> global_decl

val remove_match_on_box_env :
  GlobalContextMap.t -> (kername * global_decl) list

val remove_match_on_box_program :
  eprogram_env -> (kername * global_decl) list * term
