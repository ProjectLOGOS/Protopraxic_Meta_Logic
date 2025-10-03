open Datatypes
open EEnvMap
open EOptimizePropDiscr
open ExAst

(** val remove_match_on_box_constant_body :
    GlobalContextMap.t -> constant_body -> constant_body **)

let remove_match_on_box_constant_body _UU03a3_ cst =
  { cst_type = cst.cst_type; cst_body =
    (option_map (remove_match_on_box _UU03a3_) cst.cst_body) }

(** val remove_match_on_box_decl :
    GlobalContextMap.t -> global_decl -> global_decl **)

let remove_match_on_box_decl _UU03a3_ d = match d with
| ConstantDecl cst ->
  ConstantDecl (remove_match_on_box_constant_body _UU03a3_ cst)
| _ -> d
