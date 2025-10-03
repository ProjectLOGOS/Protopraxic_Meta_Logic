open EAst
open ExAst
open Optimize

(** val dearg_env : dearg_set -> global_env -> global_env **)

let dearg_env masks _UU03a3_ =
  debox_env_types (dearg_env masks.ind_masks masks.const_masks _UU03a3_)

(** val dearg_term : dearg_set -> term -> term **)

let dearg_term masks t =
  dearg masks.ind_masks masks.const_masks t
