open BasicAst
open Datatypes
open EAst
open EAstUtils
open EPrimitive
open Kernames

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module MkAppsInd =
 struct
  (** val inspect : 'a1 -> 'a1 **)

  let inspect x =
    x

  (** val case_clause_7 :
      (term -> term list -> __ -> __ -> 'a1) -> term -> term -> (term * term
      list) -> 'a1 **)

  let case_clause_7 papp _ _ = function
  | (t, l) -> papp t l __ __

  (** val case :
      'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
      (name -> term -> 'a1) -> (name -> term -> term -> 'a1) -> (term -> term
      list -> __ -> __ -> 'a1) -> (kername -> 'a1) -> (inductive -> nat ->
      term list -> 'a1) -> ((inductive * nat) -> term -> (name list * term)
      list -> 'a1) -> (projection -> term -> 'a1) -> (term mfixpoint -> nat
      -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term prim_val -> 'a1) ->
      (term -> 'a1) -> (term -> 'a1) -> term -> 'a1 **)

  let case pbox prel pvar pevar plam plet papp pconst pconstruct pcase pproj pfix pcofix pprim plazy pforce = function
  | Coq_tBox -> pbox
  | Coq_tRel n -> prel n
  | Coq_tVar i -> pvar i
  | Coq_tEvar (n, l) -> pevar n l
  | Coq_tLambda (na, t0) -> plam na t0
  | Coq_tLetIn (na, b, t0) -> plet na b t0
  | Coq_tApp (u, v) ->
    let (t0, l) = inspect (decompose_app (Coq_tApp (u, v))) in papp t0 l __ __
  | Coq_tConst k -> pconst k
  | Coq_tConstruct (ind, n, args) -> pconstruct ind n args
  | Coq_tCase (indn, c, brs) -> pcase indn c brs
  | Coq_tProj (p, c) -> pproj p c
  | Coq_tFix (mfix, idx) -> pfix mfix idx
  | Coq_tCoFix (mfix, idx) -> pcofix mfix idx
  | Coq_tPrim prim -> pprim prim
  | Coq_tLazy t0 -> plazy t0
  | Coq_tForce t0 -> pforce t0
 end
