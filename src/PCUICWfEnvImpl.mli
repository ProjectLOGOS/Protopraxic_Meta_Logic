open BasicAst
open PCUICAst
open PCUICEqualityDec
open PCUICTyping
open PCUICWfEnv
open Specif
open Universes0
open Config0
open UGraph0

type abstract_guard_impl =
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term mfixpoint -> bool
  (* singleton inductive, whose constructor was Build_abstract_guard_impl *)

val fake_guard_impl :
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term mfixpoint -> bool

type reference_impl_ext =
  PCUICEnvironment.global_env_ext
  (* singleton inductive, whose constructor was Build_reference_impl_ext *)

val reference_impl_ext_graph :
  checker_flags -> abstract_guard_impl -> reference_impl_ext ->
  universes_graph

type reference_impl =
  PCUICEnvironment.global_env
  (* singleton inductive, whose constructor was Build_reference_impl *)

val reference_impl_graph : checker_flags -> reference_impl -> universes_graph

val reference_pop : checker_flags -> reference_impl -> reference_impl

val canonical_abstract_env_struct :
  checker_flags -> abstract_guard_impl -> (reference_impl,
  reference_impl_ext) abstract_env_struct

type wf_env = { wf_env_reference : reference_impl;
                wf_env_map : PCUICEnvironment.global_decl EnvMap.EnvMap.t }

type wf_env_ext = { wf_env_ext_reference : reference_impl_ext;
                    wf_env_ext_map : PCUICEnvironment.global_decl
                                     EnvMap.EnvMap.t }

val wf_env_init :
  checker_flags -> abstract_guard_impl -> ContextSet.t ->
  Environment.Retroknowledge.t -> wf_env

val optim_pop : checker_flags -> wf_env -> wf_env

val optimized_abstract_env_struct :
  checker_flags -> abstract_guard_impl -> (wf_env, wf_env_ext)
  abstract_env_struct

val optimized_abstract_env_impl :
  checker_flags -> abstract_guard_impl -> abstract_env_impl

val build_wf_env_from_env :
  checker_flags -> PCUICEnvironment.global_env -> wf_env
