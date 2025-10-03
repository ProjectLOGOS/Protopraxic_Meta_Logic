open Datatypes
open EAst
open ECSubst
open EEnvMap
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCProd

(** val isprop_ind : GlobalContextMap.t -> (inductive * nat) -> bool **)

let isprop_ind _UU03a3_ ind =
  match GlobalContextMap.inductive_isprop_and_pars _UU03a3_ (fst ind) with
  | Some p -> let (b, _) = p in b
  | None -> false

(** val remove_match_on_box : GlobalContextMap.t -> term -> term **)

let rec remove_match_on_box _UU03a3_ t0 = match t0 with
| Coq_tRel i -> Coq_tRel i
| Coq_tEvar (ev, args) ->
  Coq_tEvar (ev, (map (remove_match_on_box _UU03a3_) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (remove_match_on_box _UU03a3_ m))
| Coq_tLetIn (na, b, b') ->
  Coq_tLetIn (na, (remove_match_on_box _UU03a3_ b),
    (remove_match_on_box _UU03a3_ b'))
| Coq_tApp (u, v) ->
  Coq_tApp ((remove_match_on_box _UU03a3_ u),
    (remove_match_on_box _UU03a3_ v))
| Coq_tConstruct (ind, i, args) ->
  Coq_tConstruct (ind, i, (map (remove_match_on_box _UU03a3_) args))
| Coq_tCase (ind, c, brs) ->
  let brs' = map (on_snd (remove_match_on_box _UU03a3_)) brs in
  if isprop_ind _UU03a3_ ind
  then (match brs' with
        | [] -> Coq_tCase (ind, (remove_match_on_box _UU03a3_ c), brs')
        | p :: l ->
          let (a, b) = p in
          (match l with
           | [] -> substl (repeat Coq_tBox (length a)) b
           | _ :: _ -> Coq_tCase (ind, (remove_match_on_box _UU03a3_ c), brs')))
  else Coq_tCase (ind, (remove_match_on_box _UU03a3_ c), brs')
| Coq_tProj (p, c) ->
  (match GlobalContextMap.inductive_isprop_and_pars _UU03a3_ p.proj_ind with
   | Some p0 ->
     let (b, _) = p0 in
     if b then Coq_tBox else Coq_tProj (p, (remove_match_on_box _UU03a3_ c))
   | None -> Coq_tProj (p, (remove_match_on_box _UU03a3_ c)))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (remove_match_on_box _UU03a3_)) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (remove_match_on_box _UU03a3_)) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (remove_match_on_box _UU03a3_) p)
| Coq_tLazy t1 -> Coq_tLazy (remove_match_on_box _UU03a3_ t1)
| Coq_tForce t1 -> Coq_tForce (remove_match_on_box _UU03a3_ t1)
| _ -> t0

(** val remove_match_on_box_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let remove_match_on_box_constant_decl _UU03a3_ cb =
  option_map (remove_match_on_box _UU03a3_) cb

(** val remove_match_on_box_decl :
    GlobalContextMap.t -> global_decl -> global_decl **)

let remove_match_on_box_decl _UU03a3_ = function
| ConstantDecl cb ->
  ConstantDecl (remove_match_on_box_constant_decl _UU03a3_ cb)
| InductiveDecl idecl -> InductiveDecl idecl

(** val remove_match_on_box_env :
    GlobalContextMap.t -> (kername * global_decl) list **)

let remove_match_on_box_env _UU03a3_ =
  map (on_snd (remove_match_on_box_decl _UU03a3_))
    _UU03a3_.GlobalContextMap.global_decls

(** val remove_match_on_box_program :
    eprogram_env -> (kername * global_decl) list * term **)

let remove_match_on_box_program p =
  ((remove_match_on_box_env (fst p)), (remove_match_on_box (fst p) (snd p)))
