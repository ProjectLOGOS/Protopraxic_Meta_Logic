open Datatypes
open EAst
open EEnvMap
open EEtaExpanded
open EPrimitive
open EProgram
open ESpineView
open EWcbvEval
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd

val transform_blocks : GlobalContextMap.t -> term -> term

val transform_blocks_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val transform_blocks_decl : GlobalContextMap.t -> global_decl -> global_decl

val transform_blocks_env : GlobalContextMap.t -> (kername * global_decl) list

val transform_blocks_program :
  eprogram_env -> (kername * global_decl) list * term

val switch_cstr_as_blocks : coq_EEnvFlags -> coq_EEnvFlags

val block_wcbv_flags : coq_WcbvFlags
