open Datatypes
open EAst
open Kernames

type construct_view =
| Coq_view_construct of inductive * nat * term list
| Coq_view_other of term

(** val construct_viewc : term -> construct_view **)

let construct_viewc = function
| Coq_tConstruct (ind, n, args) -> Coq_view_construct (ind, n, args)
| x -> Coq_view_other x
