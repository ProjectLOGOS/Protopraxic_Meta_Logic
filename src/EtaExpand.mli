open Ast0
open AstUtils
open BasicAst
open Byte
open Datatypes
open Kernames
open List0
open MCList
open MCProd
open Nat0
open TemplateEnvMap
open TemplateProgram
open Typing0
open Universes0
open Bytestring

val eta_single : term -> term list -> term -> nat -> term

val eta_constructor :
  GlobalEnvMap.t -> inductive -> nat -> Level.t list -> term list -> term
  option

val eta_fixpoint : term mfixpoint -> nat -> term def -> term list -> term

val up : (nat * term) option list -> (nat * term) option list

val eta_expand : GlobalEnvMap.t -> (nat * term) option list -> term -> term

val eta_global_decl : GlobalEnvMap.t -> Env.constant_body -> Env.constant_body

val map_decl_body : ('a1 -> 'a1) -> 'a1 context_decl -> 'a1 context_decl

val fold_context_k_defs :
  (nat -> 'a1 -> 'a1) -> 'a1 context_decl list -> 'a1 context_decl list

val eta_context :
  GlobalEnvMap.t -> nat -> term context_decl list -> term context_decl list

val eta_constructor_decl :
  GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.constructor_body ->
  Env.constructor_body

val eta_inductive_decl :
  GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.one_inductive_body ->
  Env.one_inductive_body

val eta_minductive_decl :
  GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.mutual_inductive_body

val eta_global_declaration :
  GlobalEnvMap.t -> Env.global_decl -> Env.global_decl

val eta_global_declarations :
  GlobalEnvMap.t -> Env.global_declarations -> (kername * Env.global_decl)
  list

val eta_expand_global_env : GlobalEnvMap.t -> Env.global_env

val eta_expand_program : template_program_env -> Env.program
