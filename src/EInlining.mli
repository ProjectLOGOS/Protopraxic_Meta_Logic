open Byte
open Datatypes
open EAst
open EPrimitive
open EWcbvEval
open EWellformed
open Kernames
open List0
open MCList
open MCProd
open Bytestring

type inlining = KernameSet.t

type constants_inlining = term KernameMap.t

val inline : constants_inlining -> term -> term

val inline_constant_decl :
  constants_inlining -> constant_body -> constant_body

val inline_decl :
  constants_inlining -> (kername * global_decl) -> kername * global_decl

val inline_add :
  inlining -> (global_declarations * constants_inlining) ->
  (KernameSet.elt * global_decl) -> term KernameMap.t

val inline_env :
  KernameSet.t -> (kername * global_decl) list ->
  global_declarations * constants_inlining

type inlined_program = (global_declarations * constants_inlining) * term

val inline_program : KernameSet.t -> program -> inlined_program

val inline_transformation :
  coq_EEnvFlags -> coq_WcbvFlags -> KernameSet.t -> (global_declarations,
  global_declarations * constants_inlining, term, term, term, term)
  Transform.Transform.t

val forget_inlining_info_transformation :
  coq_EEnvFlags -> coq_WcbvFlags ->
  (global_declarations * constants_inlining, global_declarations, term, term,
  term, term) Transform.Transform.t
