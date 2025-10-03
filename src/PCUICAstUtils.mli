open BasicAst
open Datatypes
open Kernames
open PCUICAst
open Universes0

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

val fst_ctx : PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env

type view_sort =
| Coq_view_sort_sort of Sort.t
| Coq_view_sort_other of term

val view_sortc : term -> view_sort

type view_prod =
| Coq_view_prod_prod of aname * term * term
| Coq_view_prod_other of term

val view_prodc : term -> view_prod

type view_ind =
| Coq_view_ind_tInd of inductive * Instance.t
| Coq_view_ind_other of term

val view_indc : term -> view_ind
