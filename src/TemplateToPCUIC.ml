open Ast0
open BasicAst
open Datatypes
open Kernames
open List0
open MCList
open MCProd
open PCUICAst
open PCUICCases
open PCUICPrimitive
open PCUICProgram
open Primitive
open Specif
open TemplateProgram
open Universes0

(** val map2_bias_left :
    ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2_bias_left f default l l' =
  match l with
  | [] -> []
  | a :: as_ ->
    (match l' with
     | [] -> (f a default) :: (map2_bias_left f default as_ [])
     | b :: bs -> (f a b) :: (map2_bias_left f default as_ bs))

(** val dummy_decl : term context_decl **)

let dummy_decl =
  PCUICEnvironment.vass { binder_name = Coq_nAnon; binder_relevance =
    Relevant } (Coq_tSort Sort.type0)

(** val trans_predicate :
    inductive -> PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.one_inductive_body -> term list -> Instance.t -> aname
    list -> term -> term predicate **)

let trans_predicate ind mdecl idecl pparams0 puinst0 pcontext0 preturn0 =
  let pctx =
    map2_bias_left PCUICEnvironment.set_binder_name dummy_decl pcontext0
      (ind_predicate_context ind mdecl idecl)
  in
  { pparams = pparams0; puinst = puinst0; pcontext = pctx; preturn =
  preturn0 }

(** val trans_branch :
    inductive -> PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.constructor_body -> aname list -> term -> term branch **)

let trans_branch ind mdecl cdecl bcontext0 bbody0 =
  let bctx =
    map2_bias_left PCUICEnvironment.set_binder_name dummy_decl bcontext0
      (cstr_branch_context ind mdecl cdecl)
  in
  { bcontext = bctx; bbody = bbody0 }

(** val trans : global_env_map -> Ast0.term -> term **)

let rec trans _UU03a3_ = function
| Ast0.Coq_tRel n -> Coq_tRel n
| Ast0.Coq_tVar n -> Coq_tVar n
| Ast0.Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (trans _UU03a3_) args))
| Ast0.Coq_tSort u -> Coq_tSort u
| Coq_tCast (c, _, t1) ->
  Coq_tApp ((Coq_tLambda ({ binder_name = Coq_nAnon; binder_relevance =
    Relevant }, (trans _UU03a3_ t1), (Coq_tRel O))), (trans _UU03a3_ c))
| Ast0.Coq_tProd (na, a, b) ->
  Coq_tProd (na, (trans _UU03a3_ a), (trans _UU03a3_ b))
| Ast0.Coq_tLambda (na, t1, m) ->
  Coq_tLambda (na, (trans _UU03a3_ t1), (trans _UU03a3_ m))
| Ast0.Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (trans _UU03a3_ b), (trans _UU03a3_ t1),
    (trans _UU03a3_ b'))
| Ast0.Coq_tApp (u, v) -> mkApps (trans _UU03a3_ u) (map (trans _UU03a3_) v)
| Ast0.Coq_tConst (c, u) -> Coq_tConst (c, u)
| Ast0.Coq_tInd (c, u) -> Coq_tInd (c, u)
| Ast0.Coq_tConstruct (c, k, u) -> Coq_tConstruct (c, k, u)
| Ast0.Coq_tCase (ci, p, c, brs) ->
  let p' =
    Ast0.map_predicate (Obj.magic id) (trans _UU03a3_) (trans _UU03a3_) p
  in
  let brs' = map (Ast0.map_branch (trans _UU03a3_)) brs in
  (match TransLookup.lookup_inductive _UU03a3_ ci.ci_ind with
   | Some p0 ->
     let (mdecl, idecl) = p0 in
     let tp =
       trans_predicate ci.ci_ind mdecl idecl p'.Ast0.pparams p'.Ast0.puinst
         p'.Ast0.pcontext p'.Ast0.preturn
     in
     let tbrs =
       map2 (fun cdecl br ->
         trans_branch ci.ci_ind mdecl cdecl br.Ast0.bcontext br.Ast0.bbody)
         (PCUICEnvironment.ind_ctors idecl) brs'
     in
     Coq_tCase (ci, tp, (trans _UU03a3_ c), tbrs)
   | None ->
     Coq_tCase (ci, { pparams = p'.Ast0.pparams; puinst = p'.Ast0.puinst;
       pcontext =
       (map (fun na -> PCUICEnvironment.vass na (Coq_tSort Sort.type0))
         p'.Ast0.pcontext); preturn = p'.Ast0.preturn }, (trans _UU03a3_ c),
       []))
| Ast0.Coq_tProj (p, c) -> Coq_tProj (p, (trans _UU03a3_ c))
| Ast0.Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (trans _UU03a3_) (trans _UU03a3_)) mfix in
  Coq_tFix (mfix', idx)
| Ast0.Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (trans _UU03a3_) (trans _UU03a3_)) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tInt n -> Coq_tPrim (Coq_existT (Coq_primInt, (Coq_primIntModel n)))
| Coq_tFloat n ->
  Coq_tPrim (Coq_existT (Coq_primFloat, (Coq_primFloatModel n)))
| Coq_tString n ->
  Coq_tPrim (Coq_existT (Coq_primString, (Coq_primStringModel n)))
| Coq_tArray (l, v, d, ty) ->
  Coq_tPrim (Coq_existT (Coq_primArray, (Coq_primArrayModel { array_level =
    l; array_type = (trans _UU03a3_ ty); array_default = (trans _UU03a3_ d);
    array_value = (map (trans _UU03a3_) v) })))

(** val trans_decl :
    global_env_map -> Ast0.term context_decl -> term context_decl **)

let trans_decl _UU03a3_ d =
  { decl_name = d.decl_name; decl_body =
    (option_map (trans _UU03a3_) d.decl_body); decl_type =
    (trans _UU03a3_ d.decl_type) }

(** val trans_local :
    global_env_map -> Ast0.term context_decl list -> term context_decl list **)

let trans_local _UU03a3_ _UU0393_ =
  map (trans_decl _UU03a3_) _UU0393_

(** val trans_constructor_body :
    global_env_map -> Env.constructor_body ->
    PCUICEnvironment.constructor_body **)

let trans_constructor_body _UU03a3_ d =
  { PCUICEnvironment.cstr_name = (Env.cstr_name d);
    PCUICEnvironment.cstr_args = (trans_local _UU03a3_ (Env.cstr_args d));
    PCUICEnvironment.cstr_indices =
    (map (trans _UU03a3_) (Env.cstr_indices d)); PCUICEnvironment.cstr_type =
    (trans _UU03a3_ (Env.cstr_type d)); PCUICEnvironment.cstr_arity =
    (Env.cstr_arity d) }

(** val trans_projection_body :
    global_env_map -> Env.projection_body -> PCUICEnvironment.projection_body **)

let trans_projection_body _UU03a3_ d =
  { PCUICEnvironment.proj_name = (Env.proj_name d);
    PCUICEnvironment.proj_relevance = (Env.proj_relevance d);
    PCUICEnvironment.proj_type = (trans _UU03a3_ (Env.proj_type d)) }

(** val trans_one_ind_body :
    global_env_map -> Env.one_inductive_body ->
    PCUICEnvironment.one_inductive_body **)

let trans_one_ind_body _UU03a3_ d =
  { PCUICEnvironment.ind_name = (Env.ind_name d);
    PCUICEnvironment.ind_indices =
    (trans_local _UU03a3_ (Env.ind_indices d)); PCUICEnvironment.ind_sort =
    (Env.ind_sort d); PCUICEnvironment.ind_type =
    (trans _UU03a3_ (Env.ind_type d)); PCUICEnvironment.ind_kelim =
    (Env.ind_kelim d); PCUICEnvironment.ind_ctors =
    (map (trans_constructor_body _UU03a3_) (Env.ind_ctors d));
    PCUICEnvironment.ind_projs =
    (map (trans_projection_body _UU03a3_) (Env.ind_projs d));
    PCUICEnvironment.ind_relevance = (Env.ind_relevance d) }

(** val trans_constant_body :
    global_env_map -> Env.constant_body -> PCUICEnvironment.constant_body **)

let trans_constant_body _UU03a3_ bd =
  { PCUICEnvironment.cst_type = (trans _UU03a3_ (Env.cst_type bd));
    PCUICEnvironment.cst_body =
    (option_map (trans _UU03a3_) (Env.cst_body bd));
    PCUICEnvironment.cst_universes = (Env.cst_universes bd);
    PCUICEnvironment.cst_relevance = (Env.cst_relevance bd) }

(** val trans_minductive_body :
    global_env_map -> Env.mutual_inductive_body ->
    PCUICEnvironment.mutual_inductive_body **)

let trans_minductive_body _UU03a3_ md =
  { PCUICEnvironment.ind_finite = (Env.ind_finite md);
    PCUICEnvironment.ind_npars = (Env.ind_npars md);
    PCUICEnvironment.ind_params = (trans_local _UU03a3_ (Env.ind_params md));
    PCUICEnvironment.ind_bodies =
    (map (trans_one_ind_body _UU03a3_) (Env.ind_bodies md));
    PCUICEnvironment.ind_universes = (Env.ind_universes md);
    PCUICEnvironment.ind_variance = (Env.ind_variance md) }

(** val trans_global_decl :
    global_env_map -> Env.global_decl -> PCUICEnvironment.global_decl **)

let trans_global_decl _UU03a3_ = function
| Env.ConstantDecl bd ->
  PCUICEnvironment.ConstantDecl (trans_constant_body _UU03a3_ bd)
| Env.InductiveDecl bd ->
  PCUICEnvironment.InductiveDecl (trans_minductive_body _UU03a3_ bd)

(** val add_global_decl :
    global_env_map -> (kername * PCUICEnvironment.global_decl) ->
    global_env_map **)

let add_global_decl env d =
  { trans_env_env = (PCUICEnvironment.add_global_decl env.trans_env_env d);
    trans_env_map = (EnvMap.EnvMap.add (fst d) (snd d) env.trans_env_map) }

(** val trans_global_decls :
    global_env_map -> Env.global_declarations -> global_env_map **)

let trans_global_decls env d =
  fold_right (fun decl _UU03a3_' ->
    let decl' = on_snd (trans_global_decl _UU03a3_') decl in
    add_global_decl _UU03a3_' decl') env d

(** val empty_trans_env :
    ContextSet.t -> Environment.Retroknowledge.t -> global_env_map **)

let empty_trans_env univs retro =
  let init_global_env = { PCUICEnvironment.universes = univs;
    PCUICEnvironment.declarations = []; PCUICEnvironment.retroknowledge =
    retro }
  in
  { trans_env_env = init_global_env; trans_env_map = EnvMap.EnvMap.empty }

(** val trans_global_env : Env.global_env -> global_env_map **)

let trans_global_env d =
  let init = empty_trans_env (Env.universes d) (Env.retroknowledge d) in
  trans_global_decls init (Env.declarations d)

(** val trans_global : Env.global_env_ext -> global_env_ext_map **)

let trans_global _UU03a3_ =
  ((trans_global_env (fst _UU03a3_)), (snd _UU03a3_))

(** val trans_template_program : template_program -> pcuic_program **)

let trans_template_program p =
  let _UU03a3_' = trans_global (Env.empty_ext (fst p)) in
  (_UU03a3_', (trans (global_env_ext_map_global_env_map _UU03a3_') (snd p)))
