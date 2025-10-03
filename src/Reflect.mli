open BasicAst
open Kernames
open ReflectEq

val eq_name : name -> name -> bool

val reflect_name : name coq_ReflectEq

val eq_relevance : relevance -> relevance -> bool

val reflect_relevance : relevance coq_ReflectEq

val eq_aname : name binder_annot -> name binder_annot -> bool

val reflect_aname : aname coq_ReflectEq

val eqb_context_decl :
  ('a1 -> 'a1 -> bool) -> 'a1 context_decl -> 'a1 context_decl -> bool

val eq_decl_reflect : 'a1 coq_ReflectEq -> 'a1 context_decl coq_ReflectEq
