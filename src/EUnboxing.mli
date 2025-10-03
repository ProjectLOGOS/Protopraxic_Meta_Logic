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
open ReflectEq

val inspect : 'a1 -> 'a1

val unboxable : one_inductive_body -> constructor_body -> bool

val is_unboxable : GlobalContextMap.t -> inductive -> nat -> bool

val get_unboxable_case_branch :
  inductive -> (name list * term) list -> (name * term) option

val unbox : GlobalContextMap.t -> term -> term

val unbox_constant_decl :
  GlobalContextMap.t -> constant_body -> E.constant_body

val unbox_inductive_decl : mutual_inductive_body -> E.mutual_inductive_body

val unbox_decl : GlobalContextMap.t -> global_decl -> global_decl

val unbox_env : GlobalContextMap.t -> (kername * global_decl) list

val unbox_program : eprogram_env -> eprogram
