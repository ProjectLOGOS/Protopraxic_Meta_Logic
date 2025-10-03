open BasicAst
open Datatypes
open Kernames
open List0
open MCList
open PCUICAst
open PCUICCases
open PCUICPrimitive
open Primitive
open Specif
open Universes0
open Monad_utils

type def_hole =
| Coq_def_hole_type of aname * term * nat
| Coq_def_hole_body of aname * term * nat

type mfix_hole = (term mfixpoint * def_hole) * term mfixpoint

type predicate_hole =
| Coq_pred_hole_params of term list * term list * Instance.t
   * PCUICEnvironment.context * term
| Coq_pred_hole_return of term list * Instance.t * PCUICEnvironment.context

type branch_hole =
  PCUICEnvironment.context
  (* singleton inductive, whose constructor was branch_hole_body *)

type branches_hole = (term branch list * branch_hole) * term branch list

type stack_entry =
| App_l of term
| App_r of term
| Fix_app of term mfixpoint * nat * term list
| Fix of mfix_hole * nat
| CoFix_app of term mfixpoint * nat * term list
| CoFix of mfix_hole * nat
| Case_pred of case_info * predicate_hole * term * term branch list
| Case_discr of case_info * term predicate * term branch list
| Case_branch of case_info * term predicate * term * branches_hole
| Proj of projection
| Prod_l of aname * term
| Prod_r of aname * term
| Lambda_ty of aname * term
| Lambda_bd of aname * term
| LetIn_bd of aname * term * term
| LetIn_ty of aname * term * term
| LetIn_in of aname * term * term
| PrimArray_ty of Level.t * term list * term
| PrimArray_def of Level.t * term list * term
| PrimArray_val of Level.t * term list * term list * term * term

type stack = stack_entry list

val fill_mfix_hole : mfix_hole -> term -> term mfixpoint

val fill_predicate_hole : predicate_hole -> term -> term predicate

val fill_branches_hole : branches_hole -> term -> term branch list

val fill_hole : term -> stack_entry -> term

val zipc : term -> stack -> term

val zip : (term * stack) -> term

val decompose_stack : stack -> term list * stack

val appstack : term list -> stack -> stack

val decompose_stack_at :
  stack_entry list -> nat -> ((term list * term) * stack) option

val fix_context_alt : (aname * term) list -> PCUICEnvironment.context

val def_sig : term def -> aname * term

val mfix_hole_context : mfix_hole -> PCUICEnvironment.context

val predicate_hole_context : predicate_hole -> PCUICEnvironment.context

val branches_hole_context :
  term predicate -> branches_hole -> PCUICEnvironment.context

val stack_entry_context : stack_entry -> PCUICEnvironment.context

val stack_context : stack -> PCUICEnvironment.context
