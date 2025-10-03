open Datatypes
open EAst
open EPrimitive
open List0
open Nat0
open PeanoNat

(** val csubst : term -> nat -> term -> term **)

let rec csubst t k u = match u with
| Coq_tBox -> Coq_tBox
| Coq_tRel n ->
  (match Nat.compare k n with
   | Eq -> t
   | Lt -> Coq_tRel (Nat.pred n)
   | Gt -> Coq_tRel n)
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (csubst t k) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (csubst t (S k) m))
| Coq_tLetIn (na, b, b') ->
  Coq_tLetIn (na, (csubst t k b), (csubst t (S k) b'))
| Coq_tApp (u0, v) -> Coq_tApp ((csubst t k u0), (csubst t k v))
| Coq_tConstruct (ind, n, args) ->
  Coq_tConstruct (ind, n, (map (csubst t k) args))
| Coq_tCase (ind, c, brs) ->
  let brs' =
    map (fun br -> ((fst br), (csubst t (add (length (fst br)) k) (snd br))))
      brs
  in
  Coq_tCase (ind, (csubst t k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (csubst t k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (csubst t k')) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (csubst t k')) mfix in Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (csubst t k) p)
| Coq_tLazy u0 -> Coq_tLazy (csubst t k u0)
| Coq_tForce u0 -> Coq_tForce (csubst t k u0)
| _ -> u

(** val substl : term list -> term -> term **)

let substl defs body =
  fold_left (fun bod term0 -> csubst term0 O bod) defs body
