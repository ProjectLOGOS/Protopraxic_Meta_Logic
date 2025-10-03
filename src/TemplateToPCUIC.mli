open Ast0
open BasicAst
open Datatypes
open Kernames
open List0
open MCList
open MCProd
open PCUICAst
open PCUICCases
open PCUICPrimitive
open PCUICProgram
open Primitive
open Specif
open TemplateProgram
open Universes0

val map2_bias_left :
  ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 list

val dummy_decl : term context_decl

val trans_predicate :
  inductive -> PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.one_inductive_body -> term list -> Instance.t -> aname
  list -> term -> term predicate

val trans_branch :
  inductive -> PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.constructor_body -> aname list -> term -> term branch

val trans : global_env_map -> Ast0.term -> term

val trans_decl : global_env_map -> Ast0.term context_decl -> term context_decl

val trans_local :
  global_env_map -> Ast0.term context_decl list -> term context_decl list

val trans_constructor_body :
  global_env_map -> Env.constructor_body -> PCUICEnvironment.constructor_body

val trans_projection_body :
  global_env_map -> Env.projection_body -> PCUICEnvironment.projection_body

val trans_one_ind_body :
  global_env_map -> Env.one_inductive_body ->
  PCUICEnvironment.one_inductive_body

val trans_constant_body :
  global_env_map -> Env.constant_body -> PCUICEnvironment.constant_body

val trans_minductive_body :
  global_env_map -> Env.mutual_inductive_body ->
  PCUICEnvironment.mutual_inductive_body

val trans_global_decl :
  global_env_map -> Env.global_decl -> PCUICEnvironment.global_decl

val add_global_decl :
  global_env_map -> (kername * PCUICEnvironment.global_decl) -> global_env_map

val trans_global_decls :
  global_env_map -> Env.global_declarations -> global_env_map

val empty_trans_env :
  ContextSet.t -> Environment.Retroknowledge.t -> global_env_map

val trans_global_env : Env.global_env -> global_env_map

val trans_global : Env.global_env_ext -> global_env_ext_map

val trans_template_program : template_program -> pcuic_program
