open Byte
open Datatypes
open EAst
open ELiftSubst
open EPrimitive
open EWcbvEval
open EWellformed
open List0
open MCProd
open Bytestring

val map_subterms : (term -> term) -> term -> term

val beta_body : term -> term list -> term

val betared_aux : term list -> term -> term

val betared : term -> term

val betared_in_constant_body : constant_body -> constant_body

val betared_in_decl : global_decl -> global_decl

val betared_env : global_declarations -> global_declarations

val betared_program : program -> program

val betared_transformation :
  coq_EEnvFlags -> coq_WcbvFlags -> (global_declarations,
  global_declarations, term, term, term, term) Transform.Transform.t
