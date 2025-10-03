open Datatypes
open EAst
open EEnvMap
open EEtaExpanded
open EPrimitive
open EProgram
open ESpineView
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd

val strip : GlobalContextMap.t -> term -> term

val strip_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val strip_inductive_decl : mutual_inductive_body -> E.mutual_inductive_body

val strip_decl : GlobalContextMap.t -> global_decl -> global_decl

val strip_env : GlobalContextMap.t -> (kername * global_decl) list

val strip_program : eprogram_env -> eprogram

val switch_no_params : coq_EEnvFlags -> coq_EEnvFlags
