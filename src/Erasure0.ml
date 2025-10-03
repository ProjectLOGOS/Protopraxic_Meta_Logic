open Ast0
open Byte
open Datatypes
open EAst
open EBeta
open EConstructorsAsBlocks
open EEnvMap
open EInlineProjections
open EInlining
open EPretty
open EProgram
open ERemoveParams
open EReorderCstrs
open ETransform
open EWcbvEval
open EWellformed
open EtaExpand
open ExAst
open Kernames
open List0
open Optimize
open PCUICAst
open PCUICProgram
open PCUICTransform
open PCUICWfEnvImpl
open TemplateEnvMap
open TemplateProgram
open Bytestring
open Config0

type unsafe_passes = { cofix_to_lazy : bool; inlining : bool;
                       unboxing : bool; betared : bool }

(** val cofix_to_lazy : unsafe_passes -> bool **)

let cofix_to_lazy u =
  u.cofix_to_lazy

(** val inlining : unsafe_passes -> bool **)

let inlining u =
  u.inlining

(** val unboxing : unsafe_passes -> bool **)

let unboxing u =
  u.unboxing

(** val betared : unsafe_passes -> bool **)

let betared u =
  u.betared

type erasure_configuration = { enable_unsafe : unsafe_passes;
                               enable_typed_erasure : bool;
                               dearging_config : dearging_config;
                               inlined_constants : KernameSet.t }

(** val enable_unsafe : erasure_configuration -> unsafe_passes **)

let enable_unsafe e =
  e.enable_unsafe

(** val enable_typed_erasure : erasure_configuration -> bool **)

let enable_typed_erasure e =
  e.enable_typed_erasure

(** val dearging_config : erasure_configuration -> dearging_config **)

let dearging_config e =
  e.dearging_config

(** val inlined_constants : erasure_configuration -> KernameSet.t **)

let inlined_constants e =
  e.inlined_constants

(** val default_dearging_config : dearging_config **)

let default_dearging_config =
  { overridden_masks = (fun _ -> None); do_trim_const_masks = true;
    do_trim_ctor_masks = false }

(** val make_unsafe_passes : bool -> unsafe_passes **)

let make_unsafe_passes b =
  { cofix_to_lazy = b; inlining = b; unboxing = b; betared = b }

(** val no_unsafe_passes : unsafe_passes **)

let no_unsafe_passes =
  make_unsafe_passes false

(** val all_unsafe_passes : unsafe_passes **)

let all_unsafe_passes =
  make_unsafe_passes true

(** val default_unsafe_passes : unsafe_passes **)

let default_unsafe_passes =
  { cofix_to_lazy = true; inlining = true; unboxing = false; betared = true }

(** val default_erasure_config : erasure_configuration **)

let default_erasure_config =
  { enable_unsafe = default_unsafe_passes; enable_typed_erasure = true;
    dearging_config = default_dearging_config; inlined_constants =
    KernameSet.empty }

(** val safe_erasure_config : erasure_configuration **)

let safe_erasure_config =
  { enable_unsafe = no_unsafe_passes; enable_typed_erasure = false;
    dearging_config = default_dearging_config; inlined_constants =
    KernameSet.empty }

(** val eta_expand :
    (GlobalEnvMap.t, Env.global_env, Ast0.term, Ast0.term, Ast0.term,
    Ast0.term) Transform.Transform.t **)

let eta_expand =
  { Transform.Transform.name = (String.String (Coq_x65, (String.String
    (Coq_x74, (String.String (Coq_x61, (String.String (Coq_x20,
    (String.String (Coq_x65, (String.String (Coq_x78, (String.String
    (Coq_x70, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x20, (String.String
    (Coq_x63, (String.String (Coq_x73, (String.String (Coq_x74,
    (String.String (Coq_x72, (String.String (Coq_x73, (String.String
    (Coq_x20, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x20, (String.String
    (Coq_x66, (String.String (Coq_x69, (String.String (Coq_x78,
    (String.String (Coq_x70, (String.String (Coq_x6f, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
    (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> eta_expand_program p) }

(** val final_wcbv_flags : coq_WcbvFlags **)

let final_wcbv_flags =
  { with_prop_case = false; with_guarded_fix = false;
    with_constructor_as_block = true }

(** val optional_unsafe_transforms :
    erasure_configuration -> (global_declarations, global_declarations,
    EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let optional_unsafe_transforms econf =
  let passes = econf.enable_unsafe in
  let efl =
    switch_cstr_as_blocks
      (disable_projections_env_flag (switch_no_params all_env_flags))
  in
  Transform.Transform.compose
    (Transform.Transform.compose
      (Transform.Transform.compose
        (optional_self_transform passes.cofix_to_lazy
          (Transform.Transform.compose
            (rebuild_wf_env_transform block_wcbv_flags efl false false)
            (coinductive_to_inductive_transformation efl)))
        (optional_self_transform passes.unboxing
          (Transform.Transform.compose
            (rebuild_wf_env_transform final_wcbv_flags efl false false)
            (unbox_transformation efl final_wcbv_flags))))
      (optional_self_transform passes.inlining
        (Transform.Transform.compose
          (inline_transformation efl final_wcbv_flags econf.inlined_constants)
          (forget_inlining_info_transformation efl final_wcbv_flags))))
    (optional_self_transform passes.betared
      (Transform.Transform.compose
        (betared_transformation efl final_wcbv_flags)
        (betared_transformation efl final_wcbv_flags)))

(** val verified_lambdabox_pipeline :
    abstract_guard_impl -> (GlobalContextMap.t, global_declarations,
    EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let verified_lambdabox_pipeline _ =
  Transform.Transform.compose
    (Transform.Transform.compose
      (Transform.Transform.compose
        (Transform.Transform.compose
          (Transform.Transform.compose
            (Transform.Transform.compose
              (Transform.Transform.compose
                (guarded_to_unguarded_fix default_wcbv_flags all_env_flags)
                (remove_params_optimization
                  (switch_unguarded_fix default_wcbv_flags)))
              (rebuild_wf_env_transform
                (switch_unguarded_fix default_wcbv_flags)
                (switch_no_params all_env_flags) true false))
            (remove_match_on_box_trans
              (switch_unguarded_fix default_wcbv_flags)
              (switch_no_params all_env_flags)))
          (rebuild_wf_env_transform
            (disable_prop_cases (switch_unguarded_fix default_wcbv_flags))
            (switch_no_params all_env_flags) true false))
        (inline_projections_optimization target_wcbv_flags))
      (rebuild_wf_env_transform target_wcbv_flags
        (disable_projections_env_flag (switch_no_params all_env_flags)) true
        false))
    (constructors_as_blocks_transformation
      (disable_projections_env_flag (switch_no_params all_env_flags)))

(** val verified_lambdabox_pipeline_mapping :
    abstract_guard_impl -> (inductives_mapping, global_declarations,
    eprogram_env, EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let verified_lambdabox_pipeline_mapping guard =
  Transform.Transform.compose
    (Transform.Transform.compose
      (reorder_cstrs_transformation all_env_flags default_wcbv_flags)
      (rebuild_wf_env_transform default_wcbv_flags all_env_flags true true))
    (verified_lambdabox_pipeline guard)

(** val wf_pcuic_inductive_mapping :
    PCUICEnvironment.global_env -> inductive_mapping -> bool **)

let wf_pcuic_inductive_mapping _UU03a3_ = function
| (ind, p) ->
  let (_, cstrs) = p in
  (match PCUICLookup.lookup_inductive _UU03a3_ ind with
   | Some p0 ->
     let (_, oib) = p0 in
     wf_tags_list cstrs (length (PCUICEnvironment.ind_ctors oib))
   | None -> true)

(** val wf_pcuic_inductives_mapping :
    PCUICEnvironment.global_env -> inductive_mapping list -> bool **)

let wf_pcuic_inductives_mapping _UU03a3_ m =
  forallb (wf_pcuic_inductive_mapping _UU03a3_) m

(** val erase_transform_mapping :
    abstract_guard_impl -> (inductives_mapping, inductives_mapping,
    pcuic_program, eprogram_env, term, EAst.term) Transform.Transform.t **)

let erase_transform_mapping guard =
  { Transform.Transform.name = (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x73,
    (String.String (Coq_x75, (String.String (Coq_x72, (String.String
    (Coq_x65, String.EmptyString))))))))))))));
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform (erase_transform guard) (snd p)))) }

(** val pcuic_expand_lets_transform_mapping :
    checker_flags -> (inductives_mapping, inductives_mapping, pcuic_program,
    pcuic_program, term, term) Transform.Transform.t **)

let pcuic_expand_lets_transform_mapping cf =
  { Transform.Transform.name = (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x20,
    (String.String (Coq_x65, (String.String (Coq_x78, (String.String
    (Coq_x70, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x69, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x20,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
    (String.String (Coq_x63, (String.String (Coq_x74, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform (pcuic_expand_lets_transform cf) (snd p)))) }

(** val verified_erasure_pipeline :
    abstract_guard_impl -> (global_env_ext_map, global_declarations, term,
    EAst.term, term, EAst.term) Transform.Transform.t **)

let verified_erasure_pipeline guard =
  Transform.Transform.compose
    (Transform.Transform.compose
      (pcuic_expand_lets_transform extraction_checker_flags)
      (erase_transform guard)) (verified_lambdabox_pipeline guard)

(** val verified_erasure_pipeline_mapping :
    abstract_guard_impl -> (inductives_mapping, global_declarations,
    pcuic_program, EAst.term, term, EAst.term) Transform.Transform.t **)

let verified_erasure_pipeline_mapping guard =
  Transform.Transform.compose
    (Transform.Transform.compose
      (pcuic_expand_lets_transform_mapping extraction_checker_flags)
      (erase_transform_mapping guard))
    (verified_lambdabox_pipeline_mapping guard)

(** val wf_template_inductive_mapping :
    Env.global_env -> inductive_mapping -> bool **)

let wf_template_inductive_mapping _UU03a3_ = function
| (ind, p) ->
  let (_, cstrs) = p in
  (match Ast0.lookup_inductive _UU03a3_ ind with
   | Some p0 ->
     let (_, oib) = p0 in wf_tags_list cstrs (length (Env.ind_ctors oib))
   | None -> true)

(** val wf_template_inductives_mapping :
    Env.global_env -> inductive_mapping list -> bool **)

let wf_template_inductives_mapping _UU03a3_ m =
  forallb (wf_template_inductive_mapping _UU03a3_) m

(** val build_template_program_env_mapping :
    checker_flags -> (inductives_mapping, inductives_mapping,
    template_program, template_program_env, Ast0.term, Ast0.term)
    Transform.Transform.t **)

let build_template_program_env_mapping cf =
  { Transform.Transform.name =
    (build_template_program_env cf).Transform.Transform.name;
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform (build_template_program_env cf) (snd p)))) }

(** val eta_expand_mapping :
    (inductives_mapping, inductives_mapping, template_program_env,
    template_program, Ast0.term, Ast0.term) Transform.Transform.t **)

let eta_expand_mapping =
  { Transform.Transform.name = eta_expand.Transform.Transform.name;
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform eta_expand (snd p)))) }

(** val template_to_pcuic_mapping :
    (inductives_mapping, inductives_mapping, template_program, pcuic_program,
    Ast0.term, term) Transform.Transform.t **)

let template_to_pcuic_mapping =
  { Transform.Transform.name =
    (template_to_pcuic_transform extraction_checker_flags).Transform.Transform.name;
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform
      (template_to_pcuic_transform extraction_checker_flags) (snd p)))) }

(** val pre_erasure_pipeline :
    (Env.global_env, global_env_ext_map, Ast0.term, term, Ast0.term, term)
    Transform.Transform.t **)

let pre_erasure_pipeline =
  Transform.Transform.compose
    (Transform.Transform.compose
      (build_template_program_env extraction_checker_flags) eta_expand)
    (template_to_pcuic_transform extraction_checker_flags)

(** val pre_erasure_pipeline_mapping :
    (inductives_mapping, inductives_mapping, template_program, pcuic_program,
    Ast0.term, term) Transform.Transform.t **)

let pre_erasure_pipeline_mapping =
  Transform.Transform.compose
    (Transform.Transform.compose
      (build_template_program_env_mapping extraction_checker_flags)
      eta_expand_mapping) template_to_pcuic_mapping

(** val erasure_pipeline :
    abstract_guard_impl -> (Env.global_env, global_declarations, Ast0.term,
    EAst.term, Ast0.term, EAst.term) Transform.Transform.t **)

let erasure_pipeline guard =
  Transform.Transform.compose pre_erasure_pipeline
    (verified_erasure_pipeline guard)

(** val erasure_pipeline_mapping :
    abstract_guard_impl -> (inductives_mapping, global_declarations,
    template_program, EAst.term, Ast0.term, EAst.term) Transform.Transform.t **)

let erasure_pipeline_mapping guard =
  Transform.Transform.compose pre_erasure_pipeline_mapping
    (verified_erasure_pipeline_mapping guard)

(** val verified_lambdabox_typed_pipeline :
    erasure_configuration -> (inductives_mapping, global_declarations,
    eprogram_env, EAst.term, EAst.term, EAst.term) Transform.Transform.t **)

let verified_lambdabox_typed_pipeline =
  let wfl = { with_prop_case = false; with_guarded_fix = true;
    with_constructor_as_block = false }
  in
  (fun econf ->
  Transform.Transform.compose
    (Transform.Transform.compose
      (Transform.Transform.compose
        (Transform.Transform.compose
          (Transform.Transform.compose
            (Transform.Transform.compose
              (Transform.Transform.compose
                (Transform.Transform.compose
                  (reorder_cstrs_transformation all_env_flags wfl)
                  (rebuild_wf_env_transform wfl all_env_flags true true))
                (guarded_to_unguarded_fix { with_prop_case = false;
                  with_guarded_fix = true; with_constructor_as_block =
                  false } all_env_flags))
              (remove_params_optimization
                (switch_unguarded_fix { with_prop_case = false;
                  with_guarded_fix = true; with_constructor_as_block =
                  false })))
            (rebuild_wf_env_transform
              (switch_unguarded_fix { with_prop_case = false;
                with_guarded_fix = true; with_constructor_as_block = false })
              (switch_no_params all_env_flags) true false))
          (inline_projections_optimization target_wcbv_flags))
        (rebuild_wf_env_transform target_wcbv_flags
          (disable_projections_env_flag (switch_no_params all_env_flags))
          true false))
      (constructors_as_blocks_transformation
        (disable_projections_env_flag (switch_no_params all_env_flags))))
    (optional_unsafe_transforms econf))

(** val typed_erase_transform_mapping :
    (inductives_mapping, inductives_mapping, pcuic_program,
    global_env * EAst.term, term, EAst.term) Transform.Transform.t **)

let typed_erase_transform_mapping =
  { Transform.Transform.name =
    typed_erase_transform.Transform.Transform.name;
    Transform.Transform.transform = (fun p _ -> ((fst p),
    (Transform.Transform.transform typed_erase_transform (snd p)))) }

(** val remove_match_on_box_typed_transform_mapping :
    coq_WcbvFlags -> coq_EEnvFlags -> (inductives_mapping,
    inductives_mapping, global_env * EAst.term, global_env * EAst.term,
    EAst.term, EAst.term) Transform.Transform.t **)

let remove_match_on_box_typed_transform_mapping fl efl =
  let tr = remove_match_on_box_typed_transform fl efl in
  { Transform.Transform.name = tr.Transform.Transform.name;
  Transform.Transform.transform = (fun p _ -> ((fst p),
  (Transform.Transform.transform tr (snd p)))) }

(** val dearging_checks_transform_mapping :
    coq_EEnvFlags -> dearging_config -> (inductives_mapping,
    inductives_mapping, global_env * EAst.term, (dearg_set
    option * global_env) * EAst.term, EAst.term, EAst.term)
    Transform.Transform.t **)

let dearging_checks_transform_mapping efl cf =
  let tr = dearging_checks_transform efl cf in
  { Transform.Transform.name = tr.Transform.Transform.name;
  Transform.Transform.transform = (fun p _ -> ((fst p),
  (Transform.Transform.transform tr (snd p)))) }

(** val dearging_transform_mapping :
    dearging_config -> (inductives_mapping, inductives_mapping, (dearg_set
    option * global_env) * EAst.term, eprogram, EAst.term, EAst.term)
    Transform.Transform.t **)

let dearging_transform_mapping cf =
  let tr = dearging_transform cf in
  { Transform.Transform.name = tr.Transform.Transform.name;
  Transform.Transform.transform = (fun p _ -> ((fst p),
  (Transform.Transform.transform tr (snd p)))) }

(** val rebuild_wf_env_transform_mapping :
    coq_WcbvFlags -> coq_EEnvFlags -> bool -> bool -> (inductives_mapping,
    inductives_mapping, eprogram, eprogram_env, EAst.term, EAst.term)
    Transform.Transform.t **)

let rebuild_wf_env_transform_mapping fl efl with_exp with_fix =
  let tr = rebuild_wf_env_transform fl efl with_exp with_fix in
  { Transform.Transform.name = tr.Transform.Transform.name;
  Transform.Transform.transform = (fun p _ -> ((fst p),
  (Transform.Transform.transform tr (snd p)))) }

(** val verified_typed_erasure_pipeline :
    abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
    global_declarations, pcuic_program, EAst.term, term, EAst.term)
    Transform.Transform.t **)

let verified_typed_erasure_pipeline _ econf =
  Transform.Transform.compose
    (Transform.Transform.compose
      (Transform.Transform.compose
        (Transform.Transform.compose
          (Transform.Transform.compose
            (Transform.Transform.compose
              (pcuic_expand_lets_transform_mapping extraction_checker_flags)
              typed_erase_transform_mapping)
            (remove_match_on_box_typed_transform_mapping default_wcbv_flags
              all_env_flags))
          (dearging_checks_transform_mapping all_env_flags
            econf.dearging_config))
        (dearging_transform_mapping econf.dearging_config))
      (rebuild_wf_env_transform_mapping opt_wcbv_flags all_env_flags true
        true)) (verified_lambdabox_typed_pipeline econf)

(** val typed_erasure_pipeline :
    abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
    global_declarations, template_program, EAst.term, Ast0.term, EAst.term)
    Transform.Transform.t **)

let typed_erasure_pipeline guard econf =
  Transform.Transform.compose pre_erasure_pipeline_mapping
    (verified_typed_erasure_pipeline guard econf)

(** val fake_guard_impl : abstract_guard_impl **)

let fake_guard_impl =
  fake_guard_impl

(** val run_erase_program :
    abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
    template_program) Transform.Transform.program -> (global_declarations,
    EAst.term) Transform.Transform.program **)

let run_erase_program guard econf p =
  if econf.enable_typed_erasure
  then Transform.Transform.run (typed_erasure_pipeline guard econf) p
  else Transform.Transform.run
         (Transform.Transform.compose (erasure_pipeline_mapping guard)
           (optional_unsafe_transforms econf)) p

(** val erase_and_print_template_program :
    erasure_configuration -> inductives_mapping -> Env.program -> String.t **)

let erase_and_print_template_program econf m p =
  let p' = run_erase_program fake_guard_impl econf (m, p) in
  Transform.time (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x65, (String.String (Coq_x74, (String.String
    (Coq_x74, (String.String (Coq_x79, (String.String (Coq_x20,
    (String.String (Coq_x70, (String.String (Coq_x72, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x67, String.EmptyString)))))))))))))))))))))))))))))) print_program
    p'

(** val typed_erasure_config : erasure_configuration **)

let typed_erasure_config =
  { enable_unsafe = no_unsafe_passes; enable_typed_erasure = true;
    dearging_config = default_dearging_config; inlined_constants =
    KernameSet.empty }

(** val typed_erase_and_print_template_program : Env.program -> String.t **)

let typed_erase_and_print_template_program p =
  erase_and_print_template_program typed_erasure_config [] p
