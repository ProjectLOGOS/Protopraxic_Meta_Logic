open BasicAst
open Kernames
open ReflectEq

(** val eq_name : name -> name -> bool **)

let eq_name na nb =
  match na with
  | Coq_nAnon -> (match nb with
                  | Coq_nAnon -> true
                  | Coq_nNamed _ -> false)
  | Coq_nNamed a ->
    (match nb with
     | Coq_nAnon -> false
     | Coq_nNamed b -> IdentOT.reflect_eq_string a b)

(** val reflect_name : name coq_ReflectEq **)

let reflect_name =
  eq_name

(** val eq_relevance : relevance -> relevance -> bool **)

let eq_relevance r r' =
  match r with
  | Relevant -> (match r' with
                 | Relevant -> true
                 | Irrelevant -> false)
  | Irrelevant -> (match r' with
                   | Relevant -> false
                   | Irrelevant -> true)

(** val reflect_relevance : relevance coq_ReflectEq **)

let reflect_relevance =
  eq_relevance

(** val eq_aname : name binder_annot -> name binder_annot -> bool **)

let eq_aname na nb =
  (&&) (reflect_name na.binder_name nb.binder_name)
    (reflect_relevance na.binder_relevance nb.binder_relevance)

(** val reflect_aname : aname coq_ReflectEq **)

let reflect_aname =
  eq_aname

(** val eqb_context_decl :
    ('a1 -> 'a1 -> bool) -> 'a1 context_decl -> 'a1 context_decl -> bool **)

let eqb_context_decl eqterm x y =
  let { decl_name = na; decl_body = b; decl_type = ty } = x in
  let { decl_name = na'; decl_body = b'; decl_type = ty' } = y in
  (&&) ((&&) (reflect_aname na na') (eq_option eqterm b b')) (eqterm ty ty')

(** val eq_decl_reflect :
    'a1 coq_ReflectEq -> 'a1 context_decl coq_ReflectEq **)

let eq_decl_reflect =
  eqb_context_decl
