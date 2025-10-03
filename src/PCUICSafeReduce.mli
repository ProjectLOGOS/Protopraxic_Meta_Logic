open BasicAst
open Datatypes
open Kernames
open List0
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICCases
open PCUICErrors
open PCUICNormal
open PCUICPosition
open PCUICWfEnv
open Specif
open Universes0
open Config0

type __ = Obj.t

val inspect : 'a1 -> 'a1

type construct_view =
| Coq_view_construct of inductive * nat * Instance.t
| Coq_view_other of term

val construct_viewc : term -> construct_view

type red_view =
| Coq_red_view_Rel of nat * stack
| Coq_red_view_LetIn of aname * term * term * term * stack
| Coq_red_view_Const of kername * Instance.t * stack
| Coq_red_view_App of term * term * stack
| Coq_red_view_Lambda of aname * term * term * term * stack_entry list
| Coq_red_view_Fix of term mfixpoint * nat * stack
| Coq_red_view_Case of case_info * term predicate * term * term branch list
   * stack
| Coq_red_view_Proj of projection * term * stack
| Coq_red_view_other of term * stack

val red_viewc : term -> stack -> red_view

type construct_cofix_view =
| Coq_ccview_construct of inductive * nat * Instance.t
| Coq_ccview_cofix of term mfixpoint * nat
| Coq_ccview_other of term

val cc_viewc : term -> construct_cofix_view

type construct0_cofix_view =
| Coq_cc0view_construct of inductive * Instance.t
| Coq_cc0view_cofix of term mfixpoint * nat
| Coq_cc0view_other of term

val cc0_viewc : term -> construct0_cofix_view

val _reduce_stack :
  checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
  PCUICEnvironment.context -> term -> stack -> (term -> stack -> __ ->
  (term * stack)) -> (term * stack)

val reduce_stack_full :
  checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
  PCUICEnvironment.context -> term -> stack -> (term * stack)

val reduce_stack :
  checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
  PCUICEnvironment.context -> term -> stack -> term * stack

val reduce_term :
  checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
  PCUICEnvironment.context -> term -> term

val hnf :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> term

val reduce_to_sort :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (Sort.t, __) sigT typing_result_comp

val reduce_to_prod :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (aname, (term, (term, __) sigT) sigT) sigT typing_result_comp

val reduce_to_ind :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> (inductive, (Instance.t, (term list, __) sigT) sigT) sigT
  typing_result_comp
