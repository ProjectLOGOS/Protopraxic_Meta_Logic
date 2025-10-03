open BasicAst
open Classes0
open Datatypes
open EAst
open EPrimitive
open Kernames
open List0
open PCUICAst
open Universes0

type __ = Obj.t

module E = EAst

(** val erase_context : PCUICEnvironment.context -> name list **)

let erase_context _UU0393_ =
  map (fun d -> d.BasicAst.decl_name.binder_name) _UU0393_
