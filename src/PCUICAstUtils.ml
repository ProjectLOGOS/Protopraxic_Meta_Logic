open BasicAst
open Datatypes
open Kernames
open PCUICAst
open Universes0

(** val decompose_app_rec : term -> term list -> term * term list **)

let rec decompose_app_rec t0 l =
  match t0 with
  | Coq_tApp (f, a) -> decompose_app_rec f (a :: l)
  | _ -> (t0, l)

(** val decompose_app : term -> term * term list **)

let decompose_app t0 =
  decompose_app_rec t0 []

(** val fst_ctx :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env **)

let fst_ctx =
  fst

type view_sort =
| Coq_view_sort_sort of Sort.t
| Coq_view_sort_other of term

(** val view_sortc : term -> view_sort **)

let view_sortc = function
| Coq_tSort u -> Coq_view_sort_sort u
| x -> Coq_view_sort_other x

type view_prod =
| Coq_view_prod_prod of aname * term * term
| Coq_view_prod_other of term

(** val view_prodc : term -> view_prod **)

let view_prodc = function
| Coq_tProd (na, a, b) -> Coq_view_prod_prod (na, a, b)
| x -> Coq_view_prod_other x

type view_ind =
| Coq_view_ind_tInd of inductive * Instance.t
| Coq_view_ind_other of term

(** val view_indc : term -> view_ind **)

let view_indc = function
| Coq_tInd (ind, ui) -> Coq_view_ind_tInd (ind, ui)
| x -> Coq_view_ind_other x
