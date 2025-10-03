open BasicAst
open Datatypes
open EAst
open EEnvMap
open EPrimitive
open EProgram
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd
open Nat0

val disable_projections_term_flags : coq_ETermFlags -> coq_ETermFlags

val disable_projections_env_flag : coq_EEnvFlags -> coq_EEnvFlags

val optimize : GlobalContextMap.t -> term -> term

val optimize_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val optimize_decl : GlobalContextMap.t -> global_decl -> global_decl

val optimize_env : GlobalContextMap.t -> (kername * global_decl) list

val optimize_program : eprogram_env -> (kername * global_decl) list * term
