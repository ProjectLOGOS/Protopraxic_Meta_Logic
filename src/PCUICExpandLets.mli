open BasicAst
open Datatypes
open List0
open MCList
open MCProd
open Nat0
open PCUICAst
open PCUICPrimitive
open PCUICProgram
open Universes0

val trans_branch : term predicate -> term branch -> term branch

val trans : term -> term

val trans_local : term context_decl list -> term context_decl list

val trans_cstr_concl_head :
  PCUICEnvironment.mutual_inductive_body -> nat -> PCUICEnvironment.context
  -> term

val trans_cstr_concl :
  PCUICEnvironment.mutual_inductive_body -> nat -> PCUICEnvironment.context
  -> term list -> term

val trans_constructor_body :
  nat -> PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.constructor_body -> PCUICEnvironment.constructor_body

val trans_projection_body :
  PCUICEnvironment.projection_body -> PCUICEnvironment.projection_body

val trans_one_ind_body :
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.one_inductive_body

val trans_minductive_body :
  PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.mutual_inductive_body

val trans_constant_body :
  PCUICEnvironment.constant_body -> PCUICEnvironment.constant_body

val trans_global_decl :
  PCUICEnvironment.global_decl -> PCUICEnvironment.global_decl

val trans_global_decls :
  PCUICEnvironment.global_declarations -> PCUICEnvironment.global_declarations

val trans_global_env :
  PCUICEnvironment.global_env -> PCUICEnvironment.global_env

val trans_global :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext

val expand_lets_program : pcuic_program -> pcuic_program
