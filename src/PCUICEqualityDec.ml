open PCUICAst
open Specif
open Config0
open UGraph0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val wf_gc_of_uctx :
    checker_flags -> PCUICEnvironment.global_env ->
    (VSet.t * GoodConstraintSet.t, __) sigT **)

let wf_gc_of_uctx cf _UU03a3_ =
  let o = gc_of_constraints cf (global_constraints _UU03a3_) in
  (match o with
   | Some t0 ->
     Coq_existT (((global_levels (PCUICEnvironment.universes _UU03a3_)), t0),
       __)
   | None -> assert false (* absurd case *))

(** val graph_of_wf :
    checker_flags -> PCUICEnvironment.global_env -> (universes_graph, __) sigT **)

let graph_of_wf cf _UU03a3_ =
  let s = wf_gc_of_uctx cf _UU03a3_ in
  let Coq_existT (x, _) = s in Coq_existT ((make_graph x), __)

(** val wf_ext_gc_of_uctx :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    (VSet.t * GoodConstraintSet.t, __) sigT **)

let wf_ext_gc_of_uctx cf _UU03a3_ =
  let o = gc_of_constraints cf (global_ext_constraints _UU03a3_) in
  (match o with
   | Some t0 -> Coq_existT (((global_ext_levels _UU03a3_), t0), __)
   | None -> assert false (* absurd case *))

(** val graph_of_wf_ext :
    checker_flags -> PCUICEnvironment.global_env_ext -> (universes_graph, __)
    sigT **)

let graph_of_wf_ext cf _UU03a3_ =
  let s = wf_ext_gc_of_uctx cf _UU03a3_ in
  let Coq_existT (x, _) = s in Coq_existT ((make_graph x), __)
