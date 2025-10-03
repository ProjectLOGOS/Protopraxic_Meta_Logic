open Byte
open Datatypes
open EAst
open ELiftSubst
open EPrimitive
open EWcbvEval
open EWellformed
open List0
open MCProd
open Bytestring

(** val map_subterms : (term -> term) -> term -> term **)

let map_subterms f = function
| Coq_tEvar (n, ts) -> Coq_tEvar (n, (map f ts))
| Coq_tLambda (na, body) -> Coq_tLambda (na, (f body))
| Coq_tLetIn (na, val0, body) -> Coq_tLetIn (na, (f val0), (f body))
| Coq_tApp (hd, arg) -> Coq_tApp ((f hd), (f arg))
| Coq_tConstruct (ind, n, args) -> Coq_tConstruct (ind, n, (map f args))
| Coq_tCase (p, disc, brs) -> Coq_tCase (p, (f disc), (map (on_snd f) brs))
| Coq_tProj (p, t1) -> Coq_tProj (p, (f t1))
| Coq_tFix (def, i) -> Coq_tFix ((map (map_def f) def), i)
| Coq_tCoFix (def, i) -> Coq_tCoFix ((map (map_def f) def), i)
| Coq_tPrim p -> Coq_tPrim (map_prim f p)
| Coq_tLazy t1 -> Coq_tLazy (f t1)
| Coq_tForce t1 -> Coq_tForce (f t1)
| x -> x

(** val beta_body : term -> term list -> term **)

let rec beta_body body = function
| [] -> body
| a :: args0 ->
  (match body with
   | Coq_tLambda (_, body0) -> beta_body (subst1 a O body0) args0
   | _ -> mkApps body (a :: args0))

(** val betared_aux : term list -> term -> term **)

let rec betared_aux args t0 = match t0 with
| Coq_tLambda (na, body) ->
  let b = betared_aux [] body in beta_body (Coq_tLambda (na, b)) args
| Coq_tApp (hd, arg) -> betared_aux ((betared_aux [] arg) :: args) hd
| _ -> mkApps (map_subterms (betared_aux []) t0) args

(** val betared : term -> term **)

let betared =
  betared_aux []

(** val betared_in_constant_body : constant_body -> constant_body **)

let betared_in_constant_body cst =
  option_map betared cst

(** val betared_in_decl : global_decl -> global_decl **)

let betared_in_decl d = match d with
| ConstantDecl cst -> ConstantDecl (betared_in_constant_body cst)
| InductiveDecl _ -> d

(** val betared_env : global_declarations -> global_declarations **)

let betared_env _UU03a3_ =
  map (fun pat -> let (kn, decl) = pat in (kn, (betared_in_decl decl)))
    _UU03a3_

(** val betared_program : program -> program **)

let betared_program p =
  ((betared_env (fst p)), (betared (snd p)))

(** val betared_transformation :
    coq_EEnvFlags -> coq_WcbvFlags -> (global_declarations,
    global_declarations, term, term, term, term) Transform.Transform.t **)

let betared_transformation _ _ =
  { Transform.Transform.name = (String.String (Coq_x62, (String.String
    (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, String.EmptyString))))))))))))))));
    Transform.Transform.transform = (fun p _ -> betared_program p) }
