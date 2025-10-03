open Datatypes
open EAst
open Kernames

type construct_view =
| Coq_view_construct of inductive * nat * term list
| Coq_view_other of term

val construct_viewc : term -> construct_view
