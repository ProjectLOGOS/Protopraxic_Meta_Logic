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

val cofix_to_lazy : unsafe_passes -> bool

val inlining : unsafe_passes -> bool

val unboxing : unsafe_passes -> bool

val betared : unsafe_passes -> bool

type erasure_configuration = { enable_unsafe : unsafe_passes;
                               enable_typed_erasure : bool;
                               dearging_config : dearging_config;
                               inlined_constants : KernameSet.t }

val enable_unsafe : erasure_configuration -> unsafe_passes

val enable_typed_erasure : erasure_configuration -> bool

val dearging_config : erasure_configuration -> dearging_config

val inlined_constants : erasure_configuration -> KernameSet.t

val default_dearging_config : dearging_config

val make_unsafe_passes : bool -> unsafe_passes

val no_unsafe_passes : unsafe_passes

val all_unsafe_passes : unsafe_passes

val default_unsafe_passes : unsafe_passes

val default_erasure_config : erasure_configuration

val safe_erasure_config : erasure_configuration

val eta_expand :
  (GlobalEnvMap.t, Env.global_env, Ast0.term, Ast0.term, Ast0.term,
  Ast0.term) Transform.Transform.t

val final_wcbv_flags : coq_WcbvFlags

val optional_unsafe_transforms :
  erasure_configuration -> (global_declarations, global_declarations,
  EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val verified_lambdabox_pipeline :
  abstract_guard_impl -> (GlobalContextMap.t, global_declarations, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

val verified_lambdabox_pipeline_mapping :
  abstract_guard_impl -> (inductives_mapping, global_declarations,
  eprogram_env, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val wf_pcuic_inductive_mapping :
  PCUICEnvironment.global_env -> inductive_mapping -> bool

val wf_pcuic_inductives_mapping :
  PCUICEnvironment.global_env -> inductive_mapping list -> bool

val erase_transform_mapping :
  abstract_guard_impl -> (inductives_mapping, inductives_mapping,
  pcuic_program, eprogram_env, term, EAst.term) Transform.Transform.t

val pcuic_expand_lets_transform_mapping :
  checker_flags -> (inductives_mapping, inductives_mapping, pcuic_program,
  pcuic_program, term, term) Transform.Transform.t

val verified_erasure_pipeline :
  abstract_guard_impl -> (global_env_ext_map, global_declarations, term,
  EAst.term, term, EAst.term) Transform.Transform.t

val verified_erasure_pipeline_mapping :
  abstract_guard_impl -> (inductives_mapping, global_declarations,
  pcuic_program, EAst.term, term, EAst.term) Transform.Transform.t

val wf_template_inductive_mapping :
  Env.global_env -> inductive_mapping -> bool

val wf_template_inductives_mapping :
  Env.global_env -> inductive_mapping list -> bool

val build_template_program_env_mapping :
  checker_flags -> (inductives_mapping, inductives_mapping, template_program,
  template_program_env, Ast0.term, Ast0.term) Transform.Transform.t

val eta_expand_mapping :
  (inductives_mapping, inductives_mapping, template_program_env,
  template_program, Ast0.term, Ast0.term) Transform.Transform.t

val template_to_pcuic_mapping :
  (inductives_mapping, inductives_mapping, template_program, pcuic_program,
  Ast0.term, term) Transform.Transform.t

val pre_erasure_pipeline :
  (Env.global_env, global_env_ext_map, Ast0.term, term, Ast0.term, term)
  Transform.Transform.t

val pre_erasure_pipeline_mapping :
  (inductives_mapping, inductives_mapping, template_program, pcuic_program,
  Ast0.term, term) Transform.Transform.t

val erasure_pipeline :
  abstract_guard_impl -> (Env.global_env, global_declarations, Ast0.term,
  EAst.term, Ast0.term, EAst.term) Transform.Transform.t

val erasure_pipeline_mapping :
  abstract_guard_impl -> (inductives_mapping, global_declarations,
  template_program, EAst.term, Ast0.term, EAst.term) Transform.Transform.t

val verified_lambdabox_typed_pipeline :
  erasure_configuration -> (inductives_mapping, global_declarations,
  eprogram_env, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val typed_erase_transform_mapping :
  (inductives_mapping, inductives_mapping, pcuic_program,
  global_env * EAst.term, term, EAst.term) Transform.Transform.t

val remove_match_on_box_typed_transform_mapping :
  coq_WcbvFlags -> coq_EEnvFlags -> (inductives_mapping, inductives_mapping,
  global_env * EAst.term, global_env * EAst.term, EAst.term, EAst.term)
  Transform.Transform.t

val dearging_checks_transform_mapping :
  coq_EEnvFlags -> dearging_config -> (inductives_mapping,
  inductives_mapping, global_env * EAst.term, (dearg_set
  option * global_env) * EAst.term, EAst.term, EAst.term)
  Transform.Transform.t

val dearging_transform_mapping :
  dearging_config -> (inductives_mapping, inductives_mapping, (dearg_set
  option * global_env) * EAst.term, eprogram, EAst.term, EAst.term)
  Transform.Transform.t

val rebuild_wf_env_transform_mapping :
  coq_WcbvFlags -> coq_EEnvFlags -> bool -> bool -> (inductives_mapping,
  inductives_mapping, eprogram, eprogram_env, EAst.term, EAst.term)
  Transform.Transform.t

val verified_typed_erasure_pipeline :
  abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
  global_declarations, pcuic_program, EAst.term, term, EAst.term)
  Transform.Transform.t

val typed_erasure_pipeline :
  abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
  global_declarations, template_program, EAst.term, Ast0.term, EAst.term)
  Transform.Transform.t

val fake_guard_impl : abstract_guard_impl

val run_erase_program :
  abstract_guard_impl -> erasure_configuration -> (inductives_mapping,
  template_program) Transform.Transform.program -> (global_declarations,
  EAst.term) Transform.Transform.program

val erase_and_print_template_program :
  erasure_configuration -> inductives_mapping -> Env.program -> String.t

val typed_erasure_config : erasure_configuration

val typed_erase_and_print_template_program : Env.program -> String.t
