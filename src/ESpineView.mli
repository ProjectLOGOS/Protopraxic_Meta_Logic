open BasicAst
open Datatypes
open EAst
open EInduction
open EPrimitive
open Kernames

module TermSpineView :
 sig
  type t =
  | Coq_tBox
  | Coq_tRel of nat
  | Coq_tVar of ident
  | Coq_tEvar of nat * term list
  | Coq_tLambda of name * term
  | Coq_tLetIn of name * term * term
  | Coq_tApp of term * term list
  | Coq_tConst of kername
  | Coq_tConstruct of inductive * nat * term list
  | Coq_tCase of (inductive * nat) * term * (name list * term) list
  | Coq_tProj of projection * term
  | Coq_tFix of term mfixpoint * nat
  | Coq_tCoFix of term mfixpoint * nat
  | Coq_tPrim of term prim_val
  | Coq_tLazy of term
  | Coq_tForce of term

  val view : term -> t
 end
