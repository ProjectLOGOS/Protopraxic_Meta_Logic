open BasicAst
open BinNums
open Kernames
open PCUICAst
open PCUICTyping
open Primitive
open Specif
open Universes0
open Config0
open UGraph0

type __ = Obj.t

type ('abstract_env_impl, 'abstract_env_ext_impl) abstract_env_struct = { 
abstract_env_init : (ContextSet.t -> Environment.Retroknowledge.t -> __ ->
                    'abstract_env_impl);
abstract_env_add_decl : ('abstract_env_impl -> kername ->
                        PCUICEnvironment.global_decl -> __ ->
                        'abstract_env_impl);
abstract_env_add_udecl : ('abstract_env_impl -> universes_decl -> __ ->
                         'abstract_env_ext_impl);
abstract_pop_decls : ('abstract_env_impl -> 'abstract_env_impl);
abstract_env_lookup : ('abstract_env_ext_impl -> kername ->
                      PCUICEnvironment.global_decl option);
abstract_primitive_constant : ('abstract_env_ext_impl -> prim_tag -> kername
                              option);
abstract_env_level_mem : ('abstract_env_ext_impl -> Level.t -> bool);
abstract_env_leqb_level_n : ('abstract_env_ext_impl -> coq_Z -> Level.t ->
                            Level.t -> bool);
abstract_env_guard : ('abstract_env_ext_impl -> coq_FixCoFix ->
                     PCUICEnvironment.context -> term mfixpoint -> bool);
abstract_env_is_consistent : ('abstract_env_impl ->
                             (LevelSet.t * GoodConstraintSet.t) -> bool) }

val abstract_env_init :
  checker_flags -> ('a1, 'a2) abstract_env_struct -> ContextSet.t ->
  Environment.Retroknowledge.t -> 'a1

val abstract_env_add_decl :
  checker_flags -> ('a1, 'a2) abstract_env_struct -> 'a1 -> kername ->
  PCUICEnvironment.global_decl -> 'a1

val abstract_env_add_udecl :
  checker_flags -> ('a1, 'a2) abstract_env_struct -> 'a1 -> universes_decl ->
  'a2

type abstract_env_impl =
  (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT) sigT

val abstract_env_impl_abstract_env_struct :
  checker_flags -> abstract_env_impl -> (__, __) abstract_env_struct

val abstract_make_wf_env_ext :
  checker_flags -> abstract_env_impl -> __ -> universes_decl -> __
