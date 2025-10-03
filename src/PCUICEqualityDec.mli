open PCUICAst
open Specif
open Config0
open UGraph0

type __ = Obj.t

val wf_gc_of_uctx :
  checker_flags -> PCUICEnvironment.global_env ->
  (VSet.t * GoodConstraintSet.t, __) sigT

val graph_of_wf :
  checker_flags -> PCUICEnvironment.global_env -> (universes_graph, __) sigT

val wf_ext_gc_of_uctx :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  (VSet.t * GoodConstraintSet.t, __) sigT

val graph_of_wf_ext :
  checker_flags -> PCUICEnvironment.global_env_ext -> (universes_graph, __)
  sigT
