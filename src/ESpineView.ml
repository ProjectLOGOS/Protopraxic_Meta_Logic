open BasicAst
open Datatypes
open EAst
open EInduction
open EPrimitive
open Kernames

module TermSpineView =
 struct
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

  (** val view : term -> t **)

  let view =
    MkAppsInd.case Coq_tBox (fun x -> Coq_tRel x) (fun x -> Coq_tVar x)
      (fun n l -> Coq_tEvar (n, l)) (fun n t0 -> Coq_tLambda (n, t0))
      (fun n b t0 -> Coq_tLetIn (n, b, t0)) (fun f l _ _ -> Coq_tApp (f, l))
      (fun x -> Coq_tConst x) (fun x x0 x1 -> Coq_tConstruct (x, x0, x1))
      (fun p t0 l -> Coq_tCase (p, t0, l)) (fun p t0 -> Coq_tProj (p, t0))
      (fun mfix n -> Coq_tFix (mfix, n)) (fun mfix n -> Coq_tCoFix (mfix, n))
      (fun p -> Coq_tPrim p) (fun x -> Coq_tLazy x) (fun x -> Coq_tForce x)
 end
