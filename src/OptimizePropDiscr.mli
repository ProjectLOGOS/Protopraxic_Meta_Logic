open Datatypes
open EEnvMap
open EOptimizePropDiscr
open ExAst

val remove_match_on_box_constant_body :
  GlobalContextMap.t -> constant_body -> constant_body

val remove_match_on_box_decl :
  GlobalContextMap.t -> global_decl -> global_decl
