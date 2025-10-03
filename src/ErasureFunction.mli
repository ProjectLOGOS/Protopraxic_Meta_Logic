open BasicAst
open Datatypes
open EAst
open EAstUtils
open EPrimitive
open Extract
open Kernames
open List0
open PCUICAst
open PCUICCases
open PCUICErrors
open PCUICPrimitive
open PCUICSafeReduce
open PCUICSafeRetyping
open PCUICWfEnv
open Primitive
open Specif
open Universes0
open Config0

type __ = Obj.t

val is_arity :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> bool

val inspect : 'a1 -> 'a1

val inspect_bool : bool -> bool

val is_erasableb :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> bool

val erase :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> E.term

val erase_constant_body :
  abstract_env_impl -> __ -> PCUICEnvironment.constant_body ->
  E.constant_body * KernameSet.t

val erase_one_inductive_body :
  PCUICEnvironment.one_inductive_body -> E.one_inductive_body

val erase_mutual_inductive_body :
  PCUICEnvironment.mutual_inductive_body -> E.mutual_inductive_body
