open BasicAst
open Datatypes
open List0
open MCList
open MCProd
open Nat0
open PCUICAst
open PCUICPrimitive
open PCUICProgram
open Universes0

(** val trans_branch : term predicate -> term branch -> term branch **)

let trans_branch p br =
  if PCUICEnvironment.is_assumption_context br.bcontext
  then br
  else { bcontext = (PCUICEnvironment.smash_context [] br.bcontext); bbody =
         (PCUICEnvironment.expand_lets
           (PCUICEnvironment.subst_context (List0.rev p.pparams) O
             (subst_instance PCUICEnvironment.subst_instance_context p.puinst
               br.bcontext)) br.bbody) }

(** val trans : term -> term **)

let rec trans = function
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map trans args))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (trans a), (trans b))
| Coq_tLambda (na, t0, m) -> Coq_tLambda (na, (trans t0), (trans m))
| Coq_tLetIn (na, b, t0, b') ->
  Coq_tLetIn (na, (trans b), (trans t0), (trans b'))
| Coq_tApp (u, v) -> Coq_tApp ((trans u), (trans v))
| Coq_tCase (ind, p, c, brs) ->
  let p' = map_predicate (Obj.magic id) trans trans (map_context trans) p in
  let brs' = map (map_branch trans (map_context trans)) brs in
  Coq_tCase (ind, p', (trans c), (map (trans_branch p') brs'))
| Coq_tProj (p, c) -> Coq_tProj (p, (trans c))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tCoFix (mfix', idx)
| Coq_tPrim i -> Coq_tPrim (mapu_prim (Obj.magic id) trans i)
| x -> x

(** val trans_local : term context_decl list -> term context_decl list **)

let trans_local _UU0393_ =
  map (map_decl trans) _UU0393_

(** val trans_cstr_concl_head :
    PCUICEnvironment.mutual_inductive_body -> nat -> PCUICEnvironment.context
    -> term **)

let trans_cstr_concl_head mdecl i args =
  Coq_tRel
    (add
      (add (sub (length (PCUICEnvironment.ind_bodies mdecl)) (S i))
        (length (PCUICEnvironment.ind_params mdecl))) (length args))

(** val trans_cstr_concl :
    PCUICEnvironment.mutual_inductive_body -> nat -> PCUICEnvironment.context
    -> term list -> term **)

let trans_cstr_concl mdecl i args indices =
  mkApps (trans_cstr_concl_head mdecl i args)
    (app
      (PCUICEnvironment.to_extended_list_k
        (trans_local (PCUICEnvironment.ind_params mdecl)) (length args))
      indices)

(** val trans_constructor_body :
    nat -> PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.constructor_body -> PCUICEnvironment.constructor_body **)

let trans_constructor_body i mdecl d =
  let args' = trans_local (PCUICEnvironment.cstr_args d) in
  let args = PCUICEnvironment.smash_context [] args' in
  let indices =
    map (PCUICEnvironment.expand_lets args')
      (map trans (PCUICEnvironment.cstr_indices d))
  in
  { PCUICEnvironment.cstr_name = (PCUICEnvironment.cstr_name d);
  PCUICEnvironment.cstr_args = args; PCUICEnvironment.cstr_indices = indices;
  PCUICEnvironment.cstr_type =
  (PCUICEnvironment.it_mkProd_or_LetIn
    (trans_local (PCUICEnvironment.ind_params mdecl))
    (PCUICEnvironment.it_mkProd_or_LetIn args
      (trans_cstr_concl mdecl i args indices)));
  PCUICEnvironment.cstr_arity = (PCUICEnvironment.cstr_arity d) }

(** val trans_projection_body :
    PCUICEnvironment.projection_body -> PCUICEnvironment.projection_body **)

let trans_projection_body d =
  { PCUICEnvironment.proj_name = (PCUICEnvironment.proj_name d);
    PCUICEnvironment.proj_relevance = (PCUICEnvironment.proj_relevance d);
    PCUICEnvironment.proj_type = (trans (PCUICEnvironment.proj_type d)) }

(** val trans_one_ind_body :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.one_inductive_body **)

let trans_one_ind_body mdecl i d =
  { PCUICEnvironment.ind_name = (PCUICEnvironment.ind_name d);
    PCUICEnvironment.ind_indices =
    (trans_local (PCUICEnvironment.ind_indices d));
    PCUICEnvironment.ind_sort = (PCUICEnvironment.ind_sort d);
    PCUICEnvironment.ind_type = (trans (PCUICEnvironment.ind_type d));
    PCUICEnvironment.ind_kelim = (PCUICEnvironment.ind_kelim d);
    PCUICEnvironment.ind_ctors =
    (map (trans_constructor_body i mdecl) (PCUICEnvironment.ind_ctors d));
    PCUICEnvironment.ind_projs =
    (map trans_projection_body (PCUICEnvironment.ind_projs d));
    PCUICEnvironment.ind_relevance = (PCUICEnvironment.ind_relevance d) }

(** val trans_minductive_body :
    PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.mutual_inductive_body **)

let trans_minductive_body md =
  { PCUICEnvironment.ind_finite = (PCUICEnvironment.ind_finite md);
    PCUICEnvironment.ind_npars = (PCUICEnvironment.ind_npars md);
    PCUICEnvironment.ind_params =
    (trans_local (PCUICEnvironment.ind_params md));
    PCUICEnvironment.ind_bodies =
    (mapi (trans_one_ind_body md) (PCUICEnvironment.ind_bodies md));
    PCUICEnvironment.ind_universes = (PCUICEnvironment.ind_universes md);
    PCUICEnvironment.ind_variance = (PCUICEnvironment.ind_variance md) }

(** val trans_constant_body :
    PCUICEnvironment.constant_body -> PCUICEnvironment.constant_body **)

let trans_constant_body bd =
  { PCUICEnvironment.cst_type = (trans (PCUICEnvironment.cst_type bd));
    PCUICEnvironment.cst_body =
    (option_map trans (PCUICEnvironment.cst_body bd));
    PCUICEnvironment.cst_universes = (PCUICEnvironment.cst_universes bd);
    PCUICEnvironment.cst_relevance = (PCUICEnvironment.cst_relevance bd) }

(** val trans_global_decl :
    PCUICEnvironment.global_decl -> PCUICEnvironment.global_decl **)

let trans_global_decl = function
| PCUICEnvironment.ConstantDecl bd ->
  PCUICEnvironment.ConstantDecl (trans_constant_body bd)
| PCUICEnvironment.InductiveDecl bd ->
  PCUICEnvironment.InductiveDecl (trans_minductive_body bd)

(** val trans_global_decls :
    PCUICEnvironment.global_declarations ->
    PCUICEnvironment.global_declarations **)

let trans_global_decls d =
  map (on_snd trans_global_decl) d

(** val trans_global_env :
    PCUICEnvironment.global_env -> PCUICEnvironment.global_env **)

let trans_global_env d =
  { PCUICEnvironment.universes = (PCUICEnvironment.universes d);
    PCUICEnvironment.declarations =
    (trans_global_decls (PCUICEnvironment.declarations d));
    PCUICEnvironment.retroknowledge = (PCUICEnvironment.retroknowledge d) }

(** val trans_global :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext **)

let trans_global _UU03a3_ =
  ((trans_global_env (fst _UU03a3_)), (snd _UU03a3_))

(** val expand_lets_program : pcuic_program -> pcuic_program **)

let expand_lets_program p =
  let _UU03a3_' = trans_global (global_env_ext_map_global_env_ext (fst p)) in
  (((build_global_env_map (PCUICEnvironment.fst_ctx _UU03a3_')),
  (snd (fst p))), (trans (snd p)))
