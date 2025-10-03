open Ast0
open BasicAst

(** val decompose_prod_assum : Env.context -> term -> Env.context * term **)

let rec decompose_prod_assum _UU0393_ t = match t with
| Coq_tProd (n, a, b) -> decompose_prod_assum (snoc _UU0393_ (Env.vass n a)) b
| Coq_tLetIn (na, b, bty, b') ->
  decompose_prod_assum (snoc _UU0393_ (Env.vdef na b bty)) b'
| _ -> (_UU0393_, t)
