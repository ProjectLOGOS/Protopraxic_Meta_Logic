open EAst
open ExAst
open Optimize

val dearg_env : dearg_set -> global_env -> global_env

val dearg_term : dearg_set -> term -> term
