open Datatypes
open EAst
open EPrimitive
open List0
open Nat0
open PeanoNat

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t = match t with
| Coq_tRel i -> if Nat.leb k i then Coq_tRel (add n i) else Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (lift n (S k) m))
| Coq_tLetIn (na, b, b') -> Coq_tLetIn (na, (lift n k b), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (lift n k v))
| Coq_tConstruct (ind, i, args) ->
  Coq_tConstruct (ind, i, (map (lift n k) args))
| Coq_tCase (ind, c, brs) ->
  let brs' =
    map (fun br -> ((fst br), (lift n (add (length (fst br)) k) (snd br))))
      brs
  in
  Coq_tCase (ind, (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k')) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k')) mfix in Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (lift n k) p)
| Coq_tLazy t0 -> Coq_tLazy (lift n k t0)
| Coq_tForce t0 -> Coq_tForce (lift n k t0)
| _ -> t

(** val up : term -> term **)

let up =
  lift (S O) O

(** val subst : term list -> nat -> term -> term **)

let rec subst s k = function
| Coq_tRel n ->
  if Nat.leb k n
  then (match nth_error s (sub n k) with
        | Some b -> lift k O b
        | None -> Coq_tRel (sub n (length s)))
  else Coq_tRel n
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst s k) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (subst s (S k) m))
| Coq_tLetIn (na, b, b') -> Coq_tLetIn (na, (subst s k b), (subst s (S k) b'))
| Coq_tApp (u0, v) -> Coq_tApp ((subst s k u0), (subst s k v))
| Coq_tConstruct (ind, i, args) ->
  Coq_tConstruct (ind, i, (map (subst s k) args))
| Coq_tCase (ind, c, brs) ->
  let brs' =
    map (fun br -> ((fst br), (subst s (add (length (fst br)) k) (snd br))))
      brs
  in
  Coq_tCase (ind, (subst s k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (subst s k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k')) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k')) mfix in Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (subst s k) p)
| Coq_tLazy t -> Coq_tLazy (subst s k t)
| Coq_tForce t -> Coq_tForce (subst s k t)
| x -> x

(** val subst1 : term -> nat -> term -> term **)

let subst1 t k u =
  subst (t :: []) k u

(** val closedn : nat -> term -> bool **)

let rec closedn k = function
| Coq_tRel i -> Nat.ltb i k
| Coq_tEvar (_, args) -> forallb (closedn k) args
| Coq_tLambda (_, m) -> closedn (S k) m
| Coq_tLetIn (_, b, b') -> (&&) (closedn k b) (closedn (S k) b')
| Coq_tApp (u, v) -> (&&) (closedn k u) (closedn k v)
| Coq_tConstruct (_, _, args) -> forallb (closedn k) args
| Coq_tCase (_, c, brs) ->
  let brs' =
    forallb (fun br -> closedn (add (length (fst br)) k) (snd br)) brs
  in
  (&&) (closedn k c) brs'
| Coq_tProj (_, c) -> closedn k c
| Coq_tFix (mfix, _) ->
  let k' = add (length mfix) k in forallb (test_def (closedn k')) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = add (length mfix) k in forallb (test_def (closedn k')) mfix
| Coq_tPrim p -> test_prim (closedn k) p
| Coq_tLazy t0 -> closedn k t0
| Coq_tForce t0 -> closedn k t0
| _ -> true
