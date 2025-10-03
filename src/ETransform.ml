open Byte
open Datatypes
open EAst
open EAstUtils
open ECoInductiveToInductive
open EConstructorsAsBlocks
open EEnvMap
open EGlobalEnv
open EInlineProjections
open EOptimizePropDiscr
open EProgram
open ERemoveParams
open EReorderCstrs
open EUnboxing
open EWcbvEval
open EWellformed
open Erasure
open ErasureFunction
open ErasureFunctionProperties
open ExAst
open ExtractionCorrectness
open Kernames
open List0
open MCProd
open Optimize
open OptimizeCorrectness
open OptimizePropDiscr
open PCUICAst
open PCUICProgram
open PCUICWfEnv
open PCUICWfEnvImpl
open ResultMonad
open Bytestring
open Config0

(** val build_wf_env_from_env : checker_flags -> global_env_map -> wf_env **)

let build_wf_env_from_env _ _UU03a3_ =
  { wf_env_reference = _UU03a3_.trans_env_env; wf_env_map =
    _UU03a3_.trans_env_map }

(** val erase_pcuic_program :
    abstract_guard_impl -> pcuic_program -> eprogram_env **)

let erase_pcuic_program guard p =
  let wfe = build_wf_env_from_env extraction_checker_flags (fst (fst p)) in
  let wfext =
    abstract_make_wf_env_ext extraction_checker_flags
      (optimized_abstract_env_impl extraction_checker_flags guard)
      (Obj.magic wfe) (snd (fst p))
  in
  let t0 =
    erase (optimized_abstract_env_impl extraction_checker_flags guard) wfext
      [] (snd p)
  in
  let _UU03a3_' =
    erase_global_fast
      (optimized_abstract_env_impl extraction_checker_flags guard)
      (term_global_deps t0) (Obj.magic wfe)
      (PCUICEnvironment.declarations
        (global_env_ext_map_global_env_map (fst p)).trans_env_env)
  in
  ((GlobalContextMap.make (fst _UU03a3_')), t0)

(** val erase_program :
    abstract_guard_impl -> pcuic_program -> eprogram_env **)

let erase_program =
  erase_pcuic_program

(** val erase_transform :
    abstract_guard_impl -> (global_env_ext_map, GlobalContextMap.t, term,
    EAst.term, term, EAst.term) Transform.Transform.t **)

let erase_transform guard =
  { Transform.Transform.name = (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x73,
    (String.String (Coq_x75, (String.String (Coq_x72, (String.String
    (Coq_x65, String.EmptyString))))))))))))));
    Transform.Transform.transform = (fun p _ -> erase_program guard p) }

(** val erase_program_typed :
    abstract_guard_impl -> pcuic_program -> global_env * EAst.term **)

let erase_program_typed guard p =
  let x =
    PCUICWfEnvImpl.build_wf_env_from_env extraction_checker_flags
      (global_env_ext_map_global_env_map (fst p)).trans_env_env
  in
  let t' = erase_term (global_env_ext_map_global_env_ext (fst p)) (snd p) in
  ((erase_global_decls_deps_recursive
     (optimized_abstract_env_impl extraction_checker_flags guard)
     (Obj.magic x)
     (PEnv.declarations
       (global_env_ext_map_global_env_map (fst p)).trans_env_env)
     (PEnv.universes
       (global_env_ext_map_global_env_map (fst p)).trans_env_env)
     (PEnv.retroknowledge
       (global_env_ext_map_global_env_map (fst p)).trans_env_env)
     (term_global_deps t') (fun _ -> false)), t')

(** val typed_erase_transform :
    (global_env_ext_map, global_env, term, EAst.term, term, EAst.term)
    Transform.Transform.t **)

let typed_erase_transform =
  { Transform.Transform.name = (String.String (Coq_x74, (String.String
    (Coq_x79, (String.String (Coq_x70, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x20, (String.String
    (Coq_x65, (String.String (Coq_x72, (String.String (Coq_x61,
    (String.String (Coq_x73, (String.String (Coq_x75, (String.String
    (Coq_x72, (String.String (Coq_x65,
    String.EmptyString))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ ->
    erase_program_typed fake_guard_impl_instance p) }

(** val remove_match_on_box_typed_env :
    GlobalContextMap.t -> global_env -> ((kername * bool) * global_decl) list **)

let remove_match_on_box_typed_env m _UU03a3_ =
  map (on_snd (remove_match_on_box_decl m)) _UU03a3_

(** val map_of_typed_global_env : global_env -> GlobalContextMap.t **)

let map_of_typed_global_env p =
  GlobalContextMap.make (trans_env p)

(** val remove_match_on_box_program_typed :
    coq_EEnvFlags -> (global_env * EAst.term) -> global_env * EAst.term **)

let remove_match_on_box_program_typed _ p =
  let m = map_of_typed_global_env (fst p) in
  ((remove_match_on_box_typed_env m (fst p)), (remove_match_on_box m (snd p)))

(** val remove_match_on_box_typed_transform :
    coq_WcbvFlags -> coq_EEnvFlags -> (global_env, global_env, EAst.term,
    EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let remove_match_on_box_typed_transform _ efl =
  { Transform.Transform.name = (String.String (Coq_x6f, (String.String
    (Coq_x70, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x6d, (String.String (Coq_x69, (String.String
    (Coq_x7a, (String.String (Coq_x65, (String.String (Coq_x5f,
    (String.String (Coq_x70, (String.String (Coq_x72, (String.String
    (Coq_x6f, (String.String (Coq_x70, (String.String (Coq_x5f,
    (String.String (Coq_x64, (String.String (Coq_x69, (String.String
    (Coq_x73, (String.String (Coq_x63, (String.String (Coq_x72,
    String.EmptyString))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ ->
    remove_match_on_box_program_typed efl p) }

type dearging_config = { overridden_masks : (kername -> bitmask option);
                         do_trim_const_masks : bool; do_trim_ctor_masks : 
                         bool }

(** val check_dearging_precond :
    dearging_config -> global_env -> EAst.term -> dearg_set option **)

let check_dearging_precond cf _UU03a3_ t0 =
  if closed_env (trans_env _UU03a3_)
  then (match compute_masks cf.overridden_masks cf.do_trim_const_masks
                cf.do_trim_ctor_masks _UU03a3_ with
        | Ok masks ->
          if (&&) (valid_cases masks.ind_masks t0)
               (is_expanded masks.ind_masks masks.const_masks t0)
          then Some masks
          else None
        | Err _ -> None)
  else None

(** val check_dearging_trans :
    dearging_config -> (global_env * EAst.term) -> (dearg_set
    option * global_env) * EAst.term **)

let check_dearging_trans cf p =
  (((check_dearging_precond cf (fst p) (snd p)), (fst p)), (snd p))

(** val dearging_checks_transform :
    coq_EEnvFlags -> dearging_config -> (global_env, dearg_set
    option * global_env, EAst.term, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let dearging_checks_transform _ cf =
  { Transform.Transform.name = (String.String (Coq_x64, (String.String
    (Coq_x65, (String.String (Coq_x61, (String.String (Coq_x72,
    (String.String (Coq_x67, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x67, String.EmptyString))))))))))))))));
    Transform.Transform.transform = (fun p _ -> check_dearging_trans cf p) }

(** val dearg :
    ((dearg_set option * global_env) * EAst.term) ->
    global_declarations * EAst.term **)

let dearg p =
  match fst (fst p) with
  | Some masks ->
    ((trans_env (dearg_env masks (snd (fst p)))), (dearg_term masks (snd p)))
  | None -> ((trans_env (snd (fst p))), (snd p))

(** val dearging_transform :
    dearging_config -> (dearg_set option * global_env, global_declarations,
    EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let dearging_transform _ =
  { Transform.Transform.name = (String.String (Coq_x64, (String.String
    (Coq_x65, (String.String (Coq_x61, (String.String (Coq_x72,
    (String.String (Coq_x67, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x67, String.EmptyString))))))))))))))));
    Transform.Transform.transform = (fun p _ -> dearg p) }

(** val guarded_to_unguarded_fix :
    coq_WcbvFlags -> coq_EEnvFlags -> (GlobalContextMap.t,
    GlobalContextMap.t, EAst.term, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let guarded_to_unguarded_fix _ _ =
  { Transform.Transform.name = (String.String (Coq_x73, (String.String
    (Coq_x77, (String.String (Coq_x69, (String.String (Coq_x74,
    (String.String (Coq_x63, (String.String (Coq_x68, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x67,
    (String.String (Coq_x20, (String.String (Coq_x74, (String.String
    (Coq_x6f, (String.String (Coq_x20, (String.String (Coq_x75,
    (String.String (Coq_x6e, (String.String (Coq_x67, (String.String
    (Coq_x75, (String.String (Coq_x61, (String.String (Coq_x72,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x66,
    (String.String (Coq_x69, (String.String (Coq_x78, (String.String
    (Coq_x70, (String.String (Coq_x6f, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
    (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> p) }

(** val rebuild_wf_env : coq_EEnvFlags -> eprogram -> eprogram_env **)

let rebuild_wf_env _ p =
  ((GlobalContextMap.make (fst p)), (snd p))

(** val rebuild_wf_env_transform :
    coq_WcbvFlags -> coq_EEnvFlags -> bool -> bool -> (global_declarations,
    GlobalContextMap.t, EAst.term, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let rebuild_wf_env_transform _ efl _ _ =
  { Transform.Transform.name = (String.String (Coq_x72, (String.String
    (Coq_x65, (String.String (Coq_x62, (String.String (Coq_x75,
    (String.String (Coq_x69, (String.String (Coq_x6c, (String.String
    (Coq_x64, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x67, (String.String (Coq_x20, (String.String
    (Coq_x65, (String.String (Coq_x6e, (String.String (Coq_x76,
    (String.String (Coq_x69, (String.String (Coq_x72, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x6d,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x74, (String.String (Coq_x20, (String.String (Coq_x6c,
    (String.String (Coq_x6f, (String.String (Coq_x6f, (String.String
    (Coq_x6b, (String.String (Coq_x75, (String.String (Coq_x70,
    (String.String (Coq_x20, (String.String (Coq_x74, (String.String
    (Coq_x61, (String.String (Coq_x62, (String.String (Coq_x6c,
    (String.String (Coq_x65,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> rebuild_wf_env efl p) }

(** val remove_params_optimization :
    coq_WcbvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
    EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let remove_params_optimization _ =
  { Transform.Transform.name = (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x70, (String.String (Coq_x70, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x67,
    (String.String (Coq_x20, (String.String (Coq_x63, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
    (String.String (Coq_x74, (String.String (Coq_x72, (String.String
    (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
    (String.String (Coq_x6f, (String.String (Coq_x72, (String.String
    (Coq_x20, (String.String (Coq_x70, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x61, (String.String
    (Coq_x6d, (String.String (Coq_x65, (String.String (Coq_x74,
    (String.String (Coq_x65, (String.String (Coq_x72, (String.String
    (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x28,
    (String.String (Coq_x75, (String.String (Coq_x73, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x67,
    (String.String (Coq_x20, (String.String (Coq_x61, (String.String
    (Coq_x20, (String.String (Coq_x76, (String.String (Coq_x69,
    (String.String (Coq_x65, (String.String (Coq_x77, (String.String
    (Coq_x29,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> strip_program p) }

(** val remove_match_on_box_trans :
    coq_WcbvFlags -> coq_EEnvFlags -> (GlobalContextMap.t,
    global_declarations, EAst.term, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let remove_match_on_box_trans _ _ =
  { Transform.Transform.name = (String.String (Coq_x6f, (String.String
    (Coq_x70, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x6d, (String.String (Coq_x69, (String.String
    (Coq_x7a, (String.String (Coq_x65, (String.String (Coq_x5f,
    (String.String (Coq_x70, (String.String (Coq_x72, (String.String
    (Coq_x6f, (String.String (Coq_x70, (String.String (Coq_x5f,
    (String.String (Coq_x64, (String.String (Coq_x69, (String.String
    (Coq_x73, (String.String (Coq_x63, (String.String (Coq_x72,
    String.EmptyString))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ ->
    remove_match_on_box_program p) }

(** val inline_projections_optimization :
    coq_WcbvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
    EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let inline_projections_optimization _ =
  { Transform.Transform.name = (String.String (Coq_x70, (String.String
    (Coq_x72, (String.String (Coq_x69, (String.String (Coq_x6d,
    (String.String (Coq_x69, (String.String (Coq_x74, (String.String
    (Coq_x69, (String.String (Coq_x76, (String.String (Coq_x65,
    (String.String (Coq_x20, (String.String (Coq_x70, (String.String
    (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x6a,
    (String.String (Coq_x65, (String.String (Coq_x63, (String.String
    (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x20, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x6c,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x67,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> optimize_program p) }

(** val constructors_as_blocks_transformation :
    coq_EEnvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
    EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let constructors_as_blocks_transformation _ =
  { Transform.Transform.name = (String.String (Coq_x74, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x66, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x6d,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x67, (String.String (Coq_x20, (String.String (Coq_x74,
    (String.String (Coq_x6f, (String.String (Coq_x20, (String.String
    (Coq_x63, (String.String (Coq_x6f, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x74, (String.String
    (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
    (String.String (Coq_x6f, (String.String (Coq_x72, (String.String
    (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x61,
    (String.String (Coq_x73, (String.String (Coq_x20, (String.String
    (Coq_x62, (String.String (Coq_x6c, (String.String (Coq_x6f,
    (String.String (Coq_x63, (String.String (Coq_x6b, (String.String
    (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> transform_blocks_program p) }

(** val coinductive_to_inductive_transformation :
    coq_EEnvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
    EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let coinductive_to_inductive_transformation _ =
  { Transform.Transform.name = (String.String (Coq_x74, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x66, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x6d,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x67, (String.String (Coq_x20, (String.String (Coq_x63,
    (String.String (Coq_x6f, (String.String (Coq_x2d, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x64,
    (String.String (Coq_x75, (String.String (Coq_x63, (String.String
    (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x76,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x6f, (String.String (Coq_x20,
    (String.String (Coq_x6c, (String.String (Coq_x61, (String.String
    (Coq_x7a, (String.String (Coq_x79, (String.String (Coq_x20,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x74, (String.String (Coq_x69, (String.String
    (Coq_x76, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x74, (String.String (Coq_x79, (String.String
    (Coq_x70, (String.String (Coq_x65, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> trans_program p) }

(** val to_program : eprogram_env -> eprogram **)

let to_program e =
  ((fst e).GlobalContextMap.global_decls, (snd e))

(** val reorder_cstrs_transformation :
    coq_EEnvFlags -> coq_WcbvFlags -> (inductives_mapping,
    global_declarations, eprogram_env, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let reorder_cstrs_transformation _ _ =
  { Transform.Transform.name = (String.String (Coq_x72, (String.String
    (Coq_x65, (String.String (Coq_x6f, (String.String (Coq_x72,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x20, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
    (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x76, (String.String
    (Coq_x65, (String.String (Coq_x20, (String.String (Coq_x63,
    (String.String (Coq_x6f, (String.String (Coq_x6e, (String.String
    (Coq_x73, (String.String (Coq_x74, (String.String (Coq_x72,
    (String.String (Coq_x75, (String.String (Coq_x63, (String.String
    (Coq_x74, (String.String (Coq_x6f, (String.String (Coq_x72,
    (String.String (Coq_x73, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ ->
    reorder_program (fst p) (to_program (snd p))) }

(** val unbox_transformation :
    coq_EEnvFlags -> coq_WcbvFlags -> (GlobalContextMap.t,
    global_declarations, EAst.term, EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let unbox_transformation _ _ =
  { Transform.Transform.name = (String.String (Coq_x75, (String.String
    (Coq_x6e, (String.String (Coq_x62, (String.String (Coq_x6f,
    (String.String (Coq_x78, (String.String (Coq_x20, (String.String
    (Coq_x73, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x67, (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x20, (String.String
    (Coq_x63, (String.String (Coq_x6f, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x74, (String.String
    (Coq_x72, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x74, (String.String (Coq_x6f, (String.String
    (Coq_x72, (String.String (Coq_x73, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> unbox_program p) }

(** val optional_self_transform :
    bool -> ('a1, 'a2) Transform.Transform.self_transform -> ('a1, 'a2)
    Transform.Transform.self_transform **)

let optional_self_transform activate tr =
  if activate
  then tr
  else { Transform.Transform.name =
         (String.append (String.String (Coq_x73, (String.String (Coq_x6b,
           (String.String (Coq_x69, (String.String (Coq_x70, (String.String
           (Coq_x70, (String.String (Coq_x65, (String.String (Coq_x64,
           (String.String (Coq_x20, String.EmptyString))))))))))))))))
           tr.Transform.Transform.name); Transform.Transform.transform =
         (fun p _ -> p) }
