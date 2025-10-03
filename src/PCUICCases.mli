open BasicAst
open Datatypes
open Kernames
open List0
open PCUICAst
open Universes0

val ind_predicate_context :
  inductive -> PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context

val inst_case_context :
  term list -> Instance.t -> PCUICEnvironment.context ->
  PCUICEnvironment.context

val inst_case_predicate_context : term predicate -> PCUICEnvironment.context

val inst_case_branch_context :
  term predicate -> term branch -> PCUICEnvironment.context

val iota_red : nat -> term predicate -> term list -> term branch -> term

val cstr_branch_context :
  inductive -> PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.constructor_body -> PCUICEnvironment.context

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat * term) option

val cofix_subst : term mfixpoint -> term list

val unfold_cofix : term mfixpoint -> nat -> (nat * term) option
