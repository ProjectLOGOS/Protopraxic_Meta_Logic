open BasicAst
open PCUICAst
open PCUICEqualityDec
open PCUICTyping
open PCUICWfEnv
open Specif
open Universes0
open Config0
open UGraph0

let __ = let rec f _ = Obj.repr f in Obj.repr f

type abstract_guard_impl =
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term mfixpoint -> bool
  (* singleton inductive, whose constructor was Build_abstract_guard_impl *)

(** val fake_guard_impl :
    coq_FixCoFix -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> term mfixpoint -> bool **)

let fake_guard_impl _ _ _ _ =
  true

type reference_impl_ext =
  PCUICEnvironment.global_env_ext
  (* singleton inductive, whose constructor was Build_reference_impl_ext *)

(** val reference_impl_ext_graph :
    checker_flags -> abstract_guard_impl -> reference_impl_ext ->
    universes_graph **)

let reference_impl_ext_graph cf _ r =
  projT1 (graph_of_wf_ext cf r)

type reference_impl =
  PCUICEnvironment.global_env
  (* singleton inductive, whose constructor was Build_reference_impl *)

(** val reference_impl_graph :
    checker_flags -> reference_impl -> universes_graph **)

let reference_impl_graph cf r =
  projT1 (graph_of_wf cf r)

(** val reference_pop : checker_flags -> reference_impl -> reference_impl **)

let reference_pop _ _UU03a3_ =
  let filtered_var = PCUICEnvironment.declarations _UU03a3_ in
  (match filtered_var with
   | [] -> _UU03a3_
   | _ :: decls ->
     { PCUICEnvironment.universes = (PCUICEnvironment.universes _UU03a3_);
       PCUICEnvironment.declarations = decls;
       PCUICEnvironment.retroknowledge =
       (PCUICEnvironment.retroknowledge _UU03a3_) })

(** val canonical_abstract_env_struct :
    checker_flags -> abstract_guard_impl -> (reference_impl,
    reference_impl_ext) abstract_env_struct **)

let canonical_abstract_env_struct cf guard =
  { abstract_env_init = (fun cs retro _ -> { PCUICEnvironment.universes = cs;
    PCUICEnvironment.declarations = []; PCUICEnvironment.retroknowledge =
    retro }); abstract_env_add_decl = (fun x kn d _ ->
    PCUICEnvironment.add_global_decl x (kn, d)); abstract_env_add_udecl =
    (fun x udecl _ -> (x, udecl)); abstract_pop_decls = (reference_pop cf);
    abstract_env_lookup = (fun _UU03a3_ ->
    PCUICEnvironment.lookup_env (PCUICEnvironment.fst_ctx _UU03a3_));
    abstract_primitive_constant = (fun x tag ->
    PCUICEnvironment.primitive_constant (PCUICEnvironment.fst_ctx x) tag);
    abstract_env_level_mem = (fun _UU03a3_ l ->
    LevelSet.mem l (global_ext_levels _UU03a3_)); abstract_env_leqb_level_n =
    (fun _UU03a3_ ->
    leqb_level_n (reference_impl_ext_graph cf guard _UU03a3_));
    abstract_env_guard = (fun _UU03a3_ fix_cofix ->
    guard fix_cofix _UU03a3_); abstract_env_is_consistent = (fun x uctx ->
    let g = reference_impl_graph cf x in
    let g' = add_uctx uctx g in
    (&&) (Coq_wGraph.is_acyclic g')
      (Coq_wGraph.IsFullSubgraph.is_full_extension g g')) }

type wf_env = { wf_env_reference : reference_impl;
                wf_env_map : PCUICEnvironment.global_decl EnvMap.EnvMap.t }

type wf_env_ext = { wf_env_ext_reference : reference_impl_ext;
                    wf_env_ext_map : PCUICEnvironment.global_decl
                                     EnvMap.EnvMap.t }

(** val wf_env_init :
    checker_flags -> abstract_guard_impl -> ContextSet.t ->
    Environment.Retroknowledge.t -> wf_env **)

let wf_env_init cf guard cs retro =
  { wf_env_reference =
    (abstract_env_init cf (canonical_abstract_env_struct cf guard) cs retro);
    wf_env_map = EnvMap.EnvMap.empty }

(** val optim_pop : checker_flags -> wf_env -> wf_env **)

let optim_pop cf _UU03a3_ =
  let filtered_var = PCUICEnvironment.declarations _UU03a3_.wf_env_reference
  in
  (match filtered_var with
   | [] -> _UU03a3_
   | p :: _ ->
     let (kn, _) = p in
     { wf_env_reference = (reference_pop cf _UU03a3_.wf_env_reference);
     wf_env_map = (EnvMap.EnvMap.remove kn _UU03a3_.wf_env_map) })

(** val optimized_abstract_env_struct :
    checker_flags -> abstract_guard_impl -> (wf_env, wf_env_ext)
    abstract_env_struct **)

let optimized_abstract_env_struct cf guard =
  { abstract_env_init = (fun x x0 _ -> wf_env_init cf guard x x0);
    abstract_env_add_decl = (fun x kn d _ -> { wf_env_reference =
    (abstract_env_add_decl cf (canonical_abstract_env_struct cf guard)
      x.wf_env_reference kn d); wf_env_map =
    (EnvMap.EnvMap.add kn d x.wf_env_map) }); abstract_env_add_udecl =
    (fun x udecl _ -> { wf_env_ext_reference =
    (abstract_env_add_udecl cf (canonical_abstract_env_struct cf guard)
      x.wf_env_reference udecl); wf_env_ext_map = x.wf_env_map });
    abstract_pop_decls = (optim_pop cf); abstract_env_lookup =
    (fun _UU03a3_ k -> EnvMap.EnvMap.lookup k _UU03a3_.wf_env_ext_map);
    abstract_primitive_constant = (fun x ->
    (canonical_abstract_env_struct cf guard).abstract_primitive_constant
      x.wf_env_ext_reference); abstract_env_level_mem = (fun x ->
    (canonical_abstract_env_struct cf guard).abstract_env_level_mem
      x.wf_env_ext_reference); abstract_env_leqb_level_n = (fun x ->
    (canonical_abstract_env_struct cf guard).abstract_env_leqb_level_n
      x.wf_env_ext_reference); abstract_env_guard =
    (fun _UU03a3_ fix_cofix ->
    guard fix_cofix _UU03a3_.wf_env_ext_reference);
    abstract_env_is_consistent = (fun x uctx ->
    (canonical_abstract_env_struct cf guard).abstract_env_is_consistent
      x.wf_env_reference uctx) }

(** val optimized_abstract_env_impl :
    checker_flags -> abstract_guard_impl -> abstract_env_impl **)

let optimized_abstract_env_impl cf guard =
  Coq_existT (__, (Coq_existT (__, (Coq_existT
    ((Obj.magic optimized_abstract_env_struct cf guard), __)))))

(** val build_wf_env_from_env :
    checker_flags -> PCUICEnvironment.global_env -> wf_env **)

let build_wf_env_from_env _ _UU03a3_ =
  let _UU03a3_m =
    EnvMap.EnvMap.of_global_env (PCUICEnvironment.declarations _UU03a3_)
  in
  { wf_env_reference = _UU03a3_; wf_env_map = _UU03a3_m }
