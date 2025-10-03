open BasicAst
open Datatypes
open Kernames
open PCUICAst
open PCUICPrimitive
open Universes0
open Bytestring
open Monad_utils

type __ = Obj.t

type coq_ConversionError =
| NotFoundConstants of kername * kername
| NotFoundConstant of kername
| LambdaNotConvertibleTypes of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
   * coq_ConversionError
| LambdaNotConvertibleAnn of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
| ProdNotConvertibleDomains of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
   * coq_ConversionError
| ProdNotConvertibleAnn of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
| ContextNotConvertibleAnn of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleType of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleBody of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleLength
| CaseOnDifferentInd of PCUICEnvironment.context * case_info * term predicate
   * term * term branch list * PCUICEnvironment.context * case_info
   * term predicate * term * term branch list
| CasePredParamsUnequalLength of PCUICEnvironment.context * case_info
   * term predicate * term * term branch list * PCUICEnvironment.context
   * case_info * term predicate * term * term branch list
| CasePredUnequalUniverseInstances of PCUICEnvironment.context * case_info
   * term predicate * term * term branch list * PCUICEnvironment.context
   * case_info * term predicate * term * term branch list
| DistinctStuckProj of PCUICEnvironment.context * projection * term
   * PCUICEnvironment.context * projection * term
| CannotUnfoldFix of PCUICEnvironment.context * term mfixpoint * nat
   * PCUICEnvironment.context * term mfixpoint * nat
| FixRargMismatch of nat * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint
| FixMfixMismatch of nat * PCUICEnvironment.context * term mfixpoint
   * PCUICEnvironment.context * term mfixpoint
| DistinctCoFix of PCUICEnvironment.context * term mfixpoint * nat
   * PCUICEnvironment.context * term mfixpoint * nat
| CoFixRargMismatch of nat * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint
| CoFixMfixMismatch of nat * PCUICEnvironment.context * term mfixpoint
   * PCUICEnvironment.context * term mfixpoint
| DistinctPrimTags of PCUICEnvironment.context * term prim_val
   * PCUICEnvironment.context * term prim_val
| DistinctPrimValues of PCUICEnvironment.context * term prim_val
   * PCUICEnvironment.context * term prim_val
| ArrayNotConvertibleLevels of PCUICEnvironment.context * term array_model
   * PCUICEnvironment.context * term array_model
| ArrayValuesNotSameLength of PCUICEnvironment.context * term array_model
   * PCUICEnvironment.context * term array_model
| ArrayNotConvertibleValues of PCUICEnvironment.context * term array_model
   * PCUICEnvironment.context * term array_model * coq_ConversionError
| ArrayNotConvertibleDefault of PCUICEnvironment.context * term array_model
   * PCUICEnvironment.context * term array_model * coq_ConversionError
| ArrayNotConvertibleTypes of PCUICEnvironment.context * term array_model
   * PCUICEnvironment.context * term array_model * coq_ConversionError
| StackHeadError of conv_pb * PCUICEnvironment.context * term * term list
   * term * term list * PCUICEnvironment.context * term * term * term list
   * coq_ConversionError
| StackTailError of conv_pb * PCUICEnvironment.context * term * term list
   * term * term list * PCUICEnvironment.context * term * term * term list
   * coq_ConversionError
| StackMismatch of PCUICEnvironment.context * term * term list * term list
   * PCUICEnvironment.context * term * term list
| HeadMismatch of conv_pb * PCUICEnvironment.context * term
   * PCUICEnvironment.context * term

type type_error =
| UnboundRel of nat
| UnboundVar of String.t
| UnboundEvar of nat
| UndeclaredConstant of kername
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotCumulSmaller of bool * __ * PCUICEnvironment.context * term * term
   * term * term * coq_ConversionError
| NotConvertible of __ * PCUICEnvironment.context * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| NotAnArity of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| Msg of String.t

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

type 'a typing_result_comp =
| Checked_comp of 'a
| TypeError_comp of type_error

(** val monad_exc : (type_error, __ typing_result) coq_MonadExc **)

let monad_exc =
  { raise = (fun _ e -> TypeError e); catch = (fun _ m f ->
    match m with
    | Checked _ -> m
    | TypeError t0 -> f t0) }
