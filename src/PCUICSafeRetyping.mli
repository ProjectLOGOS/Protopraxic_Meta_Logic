open BasicAst
open Datatypes
open Kernames
open List0
open PCUICAst
open PCUICCases
open PCUICErrors
open PCUICSafeReduce
open PCUICTyping
open PCUICWfEnv
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t

type principal_type = (term, __) sigT

type principal_sort = (Sort.t, __) sigT

val principal_type_type :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> principal_type -> term

val principal_sort_sort :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> principal_sort -> Sort.t

val infer_as_sort :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> principal_type -> principal_sort

val infer_as_prod :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (aname, (term, (term, __) sigT) sigT) sigT

val lookup_ind_decl :
  checker_flags -> abstract_env_impl -> __ -> inductive ->
  (PCUICEnvironment.mutual_inductive_body,
  (PCUICEnvironment.one_inductive_body, __) sigT) sigT typing_result

val infer :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> principal_type

val type_of_typing :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (term, __) sigT

val sort_of_type :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (Sort.t, __) sigT
