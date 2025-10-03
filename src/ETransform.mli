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

val build_wf_env_from_env : checker_flags -> global_env_map -> wf_env

val erase_pcuic_program : abstract_guard_impl -> pcuic_program -> eprogram_env

val erase_program : abstract_guard_impl -> pcuic_program -> eprogram_env

val erase_transform :
  abstract_guard_impl -> (global_env_ext_map, GlobalContextMap.t, term,
  EAst.term, term, EAst.term) Transform.Transform.t

val erase_program_typed :
  abstract_guard_impl -> pcuic_program -> global_env * EAst.term

val typed_erase_transform :
  (global_env_ext_map, global_env, term, EAst.term, term, EAst.term)
  Transform.Transform.t

val remove_match_on_box_typed_env :
  GlobalContextMap.t -> global_env -> ((kername * bool) * global_decl) list

val map_of_typed_global_env : global_env -> GlobalContextMap.t

val remove_match_on_box_program_typed :
  coq_EEnvFlags -> (global_env * EAst.term) -> global_env * EAst.term

val remove_match_on_box_typed_transform :
  coq_WcbvFlags -> coq_EEnvFlags -> (global_env, global_env, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

type dearging_config = { overridden_masks : (kername -> bitmask option);
                         do_trim_const_masks : bool; do_trim_ctor_masks : 
                         bool }

val check_dearging_precond :
  dearging_config -> global_env -> EAst.term -> dearg_set option

val check_dearging_trans :
  dearging_config -> (global_env * EAst.term) -> (dearg_set
  option * global_env) * EAst.term

val dearging_checks_transform :
  coq_EEnvFlags -> dearging_config -> (global_env, dearg_set
  option * global_env, EAst.term, EAst.term, EAst.term, EAst.term)
  Transform.Transform.t

val dearg :
  ((dearg_set option * global_env) * EAst.term) ->
  global_declarations * EAst.term

val dearging_transform :
  dearging_config -> (dearg_set option * global_env, global_declarations,
  EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val guarded_to_unguarded_fix :
  coq_WcbvFlags -> coq_EEnvFlags -> (GlobalContextMap.t, GlobalContextMap.t,
  EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val rebuild_wf_env : coq_EEnvFlags -> eprogram -> eprogram_env

val rebuild_wf_env_transform :
  coq_WcbvFlags -> coq_EEnvFlags -> bool -> bool -> (global_declarations,
  GlobalContextMap.t, EAst.term, EAst.term, EAst.term, EAst.term)
  Transform.Transform.t

val remove_params_optimization :
  coq_WcbvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

val remove_match_on_box_trans :
  coq_WcbvFlags -> coq_EEnvFlags -> (GlobalContextMap.t, global_declarations,
  EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val inline_projections_optimization :
  coq_WcbvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

val constructors_as_blocks_transformation :
  coq_EEnvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

val coinductive_to_inductive_transformation :
  coq_EEnvFlags -> (GlobalContextMap.t, global_declarations, EAst.term,
  EAst.term, EAst.term, EAst.term) Transform.Transform.t

val to_program : eprogram_env -> eprogram

val reorder_cstrs_transformation :
  coq_EEnvFlags -> coq_WcbvFlags -> (inductives_mapping, global_declarations,
  eprogram_env, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val unbox_transformation :
  coq_EEnvFlags -> coq_WcbvFlags -> (GlobalContextMap.t, global_declarations,
  EAst.term, EAst.term, EAst.term, EAst.term) Transform.Transform.t

val optional_self_transform :
  bool -> ('a1, 'a2) Transform.Transform.self_transform -> ('a1, 'a2)
  Transform.Transform.self_transform
