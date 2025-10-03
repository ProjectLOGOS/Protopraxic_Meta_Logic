open BasicAst
open Datatypes
open EAst
open EEnvMap
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCProd

val trans : GlobalContextMap.t -> term -> term

val trans_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val trans_decl : GlobalContextMap.t -> global_decl -> global_decl

val trans_env : GlobalContextMap.t -> (kername * global_decl) list

val trans_program : eprogram_env -> (kername * global_decl) list * term
