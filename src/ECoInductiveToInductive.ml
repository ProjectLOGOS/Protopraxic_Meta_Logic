open BasicAst
open Datatypes
open EAst
open EEnvMap
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCProd

(** val trans : GlobalContextMap.t -> term -> term **)

let rec trans _UU03a3_ t0 = match t0 with
| Coq_tRel i -> Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (trans _UU03a3_) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (trans _UU03a3_ m))
| Coq_tLetIn (na, b, b') ->
  Coq_tLetIn (na, (trans _UU03a3_ b), (trans _UU03a3_ b'))
| Coq_tApp (u, v) -> Coq_tApp ((trans _UU03a3_ u), (trans _UU03a3_ v))
| Coq_tConstruct (ind, i, args) ->
  (match GlobalContextMap.lookup_inductive_kind _UU03a3_ ind.inductive_mind with
   | Some r ->
     (match r with
      | CoFinite ->
        Coq_tLazy (Coq_tConstruct (ind, i, (map (trans _UU03a3_) args)))
      | _ -> Coq_tConstruct (ind, i, (map (trans _UU03a3_) args)))
   | None -> Coq_tConstruct (ind, i, (map (trans _UU03a3_) args)))
| Coq_tCase (ind, c, brs) ->
  let brs' = map (on_snd (trans _UU03a3_)) brs in
  (match GlobalContextMap.lookup_inductive_kind _UU03a3_
           (fst ind).inductive_mind with
   | Some r ->
     (match r with
      | CoFinite -> Coq_tCase (ind, (Coq_tForce (trans _UU03a3_ c)), brs')
      | _ -> Coq_tCase (ind, (trans _UU03a3_ c), brs'))
   | None -> Coq_tCase (ind, (trans _UU03a3_ c), brs'))
| Coq_tProj (p, c) ->
  (match GlobalContextMap.lookup_inductive_kind _UU03a3_
           p.proj_ind.inductive_mind with
   | Some r ->
     (match r with
      | CoFinite -> Coq_tProj (p, (Coq_tForce (trans _UU03a3_ c)))
      | _ -> Coq_tProj (p, (trans _UU03a3_ c)))
   | None -> Coq_tProj (p, (trans _UU03a3_ c)))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (trans _UU03a3_)) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (trans _UU03a3_)) mfix in Coq_tFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (trans _UU03a3_) p)
| Coq_tLazy t1 -> Coq_tLazy (trans _UU03a3_ t1)
| Coq_tForce t1 -> Coq_tForce (trans _UU03a3_ t1)
| _ -> t0

(** val trans_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let trans_constant_decl _UU03a3_ cb =
  option_map (trans _UU03a3_) cb

(** val trans_decl : GlobalContextMap.t -> global_decl -> global_decl **)

let trans_decl _UU03a3_ d = match d with
| ConstantDecl cb -> ConstantDecl (trans_constant_decl _UU03a3_ cb)
| InductiveDecl _ -> d

(** val trans_env : GlobalContextMap.t -> (kername * global_decl) list **)

let trans_env _UU03a3_ =
  map (on_snd (trans_decl _UU03a3_)) _UU03a3_.GlobalContextMap.global_decls

(** val trans_program :
    eprogram_env -> (kername * global_decl) list * term **)

let trans_program p =
  ((trans_env (fst p)), (trans (fst p) (snd p)))
