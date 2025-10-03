open All_Forall
open BasicAst
open BinNums
open Byte
open CRelationClasses
open Classes0
open Datatypes
open EnvironmentTyping
open Kernames
open List0
open MCList
open MCProd
open MCReflect
open Nat0
open PCUICPrimitive
open PeanoNat
open Primitive
open Reflect
open ReflectEq
open Signature
open Specif
open Universes0
open Bytestring
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'term predicate = { pparams : 'term list; puinst : Instance.t;
                         pcontext : 'term context_decl list; preturn : 
                         'term }

(** val pparams : 'a1 predicate -> 'a1 list **)

let pparams p =
  p.pparams

(** val puinst : 'a1 predicate -> Instance.t **)

let puinst p =
  p.puinst

(** val pcontext : 'a1 predicate -> 'a1 context_decl list **)

let pcontext p =
  p.pcontext

(** val preturn : 'a1 predicate -> 'a1 **)

let preturn p =
  p.preturn

(** val coq_NoConfusionPackage_predicate :
    'a1 predicate coq_NoConfusionPackage **)

let coq_NoConfusionPackage_predicate =
  Build_NoConfusionPackage

(** val map_predicate :
    (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1
    context_decl list -> 'a2 context_decl list) -> 'a1 predicate -> 'a2
    predicate **)

let map_predicate uf paramf preturnf pcontextf p =
  { pparams = (map paramf p.pparams); puinst = (uf p.puinst); pcontext =
    (pcontextf p.pcontext); preturn = (preturnf p.preturn) }

(** val shiftf : (nat -> 'a1 -> 'a2) -> nat -> nat -> 'a1 -> 'a2 **)

let shiftf f k k' =
  f (add k' k)

(** val map_predicate_k :
    (Instance.t -> Instance.t) -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 predicate
    -> 'a1 predicate **)

let map_predicate_k uf f k p =
  { pparams = (map (f k) p.pparams); puinst = (uf p.puinst); pcontext =
    p.pcontext; preturn = (f (add (length p.pcontext) k) p.preturn) }

(** val test_predicate :
    (Instance.t -> bool) -> ('a1 -> bool) -> 'a1 predicate -> bool **)

let test_predicate instp p pred =
  (&&)
    ((&&) ((&&) (instp pred.puinst) (forallb p pred.pparams))
      (test_context p pred.pcontext)) (p pred.preturn)

(** val test_predicate_k :
    (Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate ->
    bool **)

let test_predicate_k instp p k pred =
  (&&)
    ((&&) ((&&) (instp pred.puinst) (forallb (p k) pred.pparams))
      (test_context_k p (length pred.pparams) pred.pcontext))
    (p (add (length pred.pcontext) k) pred.preturn)

(** val test_predicate_ku :
    (nat -> Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1
    predicate -> bool **)

let test_predicate_ku instp p k pred =
  (&&)
    ((&&) ((&&) (instp k pred.puinst) (forallb (p k) pred.pparams))
      (test_context (p (length pred.puinst)) pred.pcontext))
    (p k pred.preturn)

type 'term branch = { bcontext : 'term context_decl list; bbody : 'term }

(** val bcontext : 'a1 branch -> 'a1 context_decl list **)

let bcontext b =
  b.bcontext

(** val bbody : 'a1 branch -> 'a1 **)

let bbody b =
  b.bbody

(** val coq_NoConfusionPackage_branch : 'a1 branch coq_NoConfusionPackage **)

let coq_NoConfusionPackage_branch =
  Build_NoConfusionPackage

(** val string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t **)

let string_of_branch f b =
  String.append (String.String (Coq_x28, (String.String (Coq_x5b,
    String.EmptyString))))
    (String.append
      (String.concat (String.String (Coq_x2c, String.EmptyString))
        (map
          (let g0 =
             let f0 = fun b0 -> b0.binder_name in
             (fun x -> string_of_name (f0 x))
           in
           let f0 = fun c -> c.decl_name in (fun x -> g0 (f0 x))) b.bcontext))
      (String.append (String.String (Coq_x5d, (String.String (Coq_x2c,
        (String.String (Coq_x20, String.EmptyString))))))
        (String.append (f b.bbody) (String.String (Coq_x29,
          String.EmptyString)))))

(** val pretty_string_of_branch :
    ('a1 -> String.t) -> 'a1 branch -> String.t **)

let pretty_string_of_branch f b =
  String.append
    (String.concat (String.String (Coq_x20, String.EmptyString))
      (map
        (let g0 =
           let f0 = fun b0 -> b0.binder_name in
           (fun x -> string_of_name (f0 x))
         in
         let f0 = fun c -> c.decl_name in (fun x -> g0 (f0 x))) b.bcontext))
    (String.append (String.String (Coq_x20, (String.String (Coq_x3d,
      (String.String (Coq_x3e, (String.String (Coq_x20,
      String.EmptyString)))))))) (f b.bbody))

(** val test_branch : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 branch -> bool **)

let test_branch pctx p b =
  (&&) (test_context pctx b.bcontext) (p b.bbody)

(** val test_branch_k :
    'a1 predicate -> (nat -> 'a1 -> bool) -> nat -> 'a1 branch -> bool **)

let test_branch_k pred p k b =
  (&&) (test_context_k p (length pred.pparams) b.bcontext)
    (p (add (length b.bcontext) k) b.bbody)

(** val map_branch :
    ('a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list) -> 'a1
    branch -> 'a2 branch **)

let map_branch f g b =
  { bcontext = (g b.bcontext); bbody = (f b.bbody) }

(** val map_branches :
    ('a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list) -> 'a1
    branch list -> 'a2 branch list **)

let map_branches f h l =
  map (map_branch f h) l

(** val map_branch_k :
    (nat -> 'a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list)
    -> nat -> 'a1 branch -> 'a2 branch **)

let map_branch_k f g k b =
  { bcontext = (g b.bcontext); bbody =
    (f (add (length b.bcontext) k) b.bbody) }

module Coq__1 = struct
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Sort.t
 | Coq_tProd of aname * term * term
 | Coq_tLambda of aname * term * term
 | Coq_tLetIn of aname * term * term * term
 | Coq_tApp of term * term
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of case_info * term predicate * term * term branch list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
 | Coq_tPrim of term prim_val
end
include Coq__1

(** val term_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Sort.t ->
    'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 ->
    term -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername ->
    Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive ->
    nat -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1
    -> term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) ->
    (term mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
    prim_val -> 'a1) -> term -> 'a1 **)

let rec term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| Coq_tRel n -> f n
| Coq_tVar i -> f0 i
| Coq_tEvar (n, l) -> f1 n l
| Coq_tSort u -> f2 u
| Coq_tProd (na, a, b) ->
  f3 na a (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 a) b
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b)
| Coq_tLambda (na, a, t1) ->
  f4 na a (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 a)
    t1 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
| Coq_tLetIn (na, b, b0, t1) ->
  f5 na b (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b)
    b0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b0) t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
| Coq_tApp (u, v) ->
  f6 u (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 u) v
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 v)
| Coq_tConst (k, ui) -> f7 k ui
| Coq_tInd (ind, ui) -> f8 ind ui
| Coq_tConstruct (ind, n, ui) -> f9 ind n ui
| Coq_tCase (indn, p, c, brs) ->
  f10 indn p c
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 c) brs
| Coq_tProj (p, c) ->
  f11 p c (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 c)
| Coq_tFix (mfix, idx) -> f12 mfix idx
| Coq_tCoFix (mfix, idx) -> f13 mfix idx
| Coq_tPrim prim -> f14 prim

(** val term_rec :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Sort.t ->
    'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 ->
    term -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername ->
    Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive ->
    nat -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1
    -> term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) ->
    (term mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
    prim_val -> 'a1) -> term -> 'a1 **)

let rec term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| Coq_tRel n -> f n
| Coq_tVar i -> f0 i
| Coq_tEvar (n, l) -> f1 n l
| Coq_tSort u -> f2 u
| Coq_tProd (na, a, b) ->
  f3 na a (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 a) b
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b)
| Coq_tLambda (na, a, t1) ->
  f4 na a (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 a) t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
| Coq_tLetIn (na, b, b0, t1) ->
  f5 na b (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b) b0
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 b0) t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
| Coq_tApp (u, v) ->
  f6 u (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 u) v
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 v)
| Coq_tConst (k, ui) -> f7 k ui
| Coq_tInd (ind, ui) -> f8 ind ui
| Coq_tConstruct (ind, n, ui) -> f9 ind n ui
| Coq_tCase (indn, p, c, brs) ->
  f10 indn p c
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 c) brs
| Coq_tProj (p, c) ->
  f11 p c (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 c)
| Coq_tFix (mfix, idx) -> f12 mfix idx
| Coq_tCoFix (mfix, idx) -> f13 mfix idx
| Coq_tPrim prim -> f14 prim

(** val coq_NoConfusionPackage_term : term coq_NoConfusionPackage **)

let coq_NoConfusionPackage_term =
  Build_NoConfusionPackage

(** val mkApps : term -> term list -> term **)

let rec mkApps t0 = function
| [] -> t0
| u :: us0 -> mkApps (Coq_tApp (t0, u)) us0

(** val isApp : term -> bool **)

let isApp = function
| Coq_tApp (_, _) -> true
| _ -> false

(** val isLambda : term -> bool **)

let isLambda = function
| Coq_tLambda (_, _, _) -> true
| _ -> false

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t0 = match t0 with
| Coq_tRel i -> Coq_tRel (if Nat.leb k i then add n i else i)
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (lift n k a), (lift n (S k) b))
| Coq_tLambda (na, t1, m) -> Coq_tLambda (na, (lift n k t1), (lift n (S k) m))
| Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (lift n k b), (lift n k t1), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (lift n k v))
| Coq_tCase (ind, p, c, brs) ->
  let p' = map_predicate_k (Obj.magic id) (lift n) k p in
  let brs' = map (map_branch_k (lift n) (Obj.magic id) k) brs in
  Coq_tCase (ind, p', (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (mapu_prim (Obj.magic id) (lift n k) p)
| _ -> t0

(** val subst : term list -> nat -> term -> term **)

let rec subst s k u = match u with
| Coq_tRel n ->
  if Nat.leb k n
  then (match nth_error s (sub n k) with
        | Some b -> lift k O b
        | None -> Coq_tRel (sub n (length s)))
  else Coq_tRel n
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst s k) args))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (subst s k a), (subst s (S k) b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst s k t0), (subst s (S k) m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst s k b), (subst s k ty), (subst s (S k) b'))
| Coq_tApp (u0, v) -> Coq_tApp ((subst s k u0), (subst s k v))
| Coq_tCase (ind, p, c, brs) ->
  let p' = map_predicate_k (Obj.magic id) (subst s) k p in
  let brs' = map (map_branch_k (subst s) (Obj.magic id) k) brs in
  Coq_tCase (ind, p', (subst s k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (subst s k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (mapu_prim (Obj.magic id) (subst s k) p)
| _ -> u

(** val subst1 : term -> nat -> term -> term **)

let subst1 t0 k u =
  subst (t0 :: []) k u

(** val closedn : nat -> term -> bool **)

let rec closedn k = function
| Coq_tRel i -> Nat.ltb i k
| Coq_tEvar (_, args) -> forallb (closedn k) args
| Coq_tProd (_, t1, m) -> (&&) (closedn k t1) (closedn (S k) m)
| Coq_tLambda (_, t1, m) -> (&&) (closedn k t1) (closedn (S k) m)
| Coq_tLetIn (_, b, t1, b') ->
  (&&) ((&&) (closedn k b) (closedn k t1)) (closedn (S k) b')
| Coq_tApp (u, v) -> (&&) (closedn k u) (closedn k v)
| Coq_tCase (_, p, c, brs) ->
  let p' = test_predicate_k (fun _ -> true) closedn k p in
  let brs' = forallb (test_branch_k p closedn k) brs in
  (&&) ((&&) p' (closedn k c)) brs'
| Coq_tProj (_, c) -> closedn k c
| Coq_tFix (mfix, _) ->
  let k' = add (length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = add (length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| Coq_tPrim p -> test_prim (closedn k) p
| _ -> true

(** val test_context_nlict :
    (term -> bool) -> term context_decl list -> bool **)

let rec test_context_nlict test = function
| [] -> true
| d :: bcontext1 ->
  (&&) ((&&) (test_context_nlict test bcontext1) (test d.decl_type))
    (match d.decl_body with
     | Some _ -> false
     | None -> true)

(** val test_branch_nlict : (term -> bool) -> term branch -> bool **)

let test_branch_nlict test b =
  (&&) (test_context_nlict test b.bcontext) (test b.bbody)

(** val test_branches_nlict : (term -> bool) -> term branch list -> bool **)

let test_branches_nlict test brs =
  forallb (test_branch_nlict test) brs

(** val nlict : term -> bool **)

let rec nlict = function
| Coq_tEvar (_, args) -> forallb nlict args
| Coq_tProd (_, t1, m) -> (&&) (nlict t1) (nlict m)
| Coq_tLambda (_, t1, m) -> (&&) (nlict t1) (nlict m)
| Coq_tLetIn (_, b, t1, b') -> (&&) ((&&) (nlict b) (nlict t1)) (nlict b')
| Coq_tApp (u, v) -> (&&) (nlict u) (nlict v)
| Coq_tCase (_, p, c, brs) ->
  let p' = test_predicate_k (fun _ -> true) (fun _ -> nlict) O p in
  let brs' = test_branches_nlict nlict brs in (&&) ((&&) p' (nlict c)) brs'
| Coq_tProj (_, c) -> nlict c
| Coq_tFix (mfix, _) -> forallb (test_def nlict nlict) mfix
| Coq_tCoFix (mfix, _) -> forallb (test_def nlict nlict) mfix
| Coq_tPrim p -> test_prim nlict p
| _ -> true

(** val noccur_between : nat -> nat -> term -> bool **)

let rec noccur_between k n = function
| Coq_tRel i -> (||) (Nat.ltb i k) (Nat.leb (add k n) i)
| Coq_tEvar (_, args) -> forallb (noccur_between k n) args
| Coq_tProd (_, t1, m) ->
  (&&) (noccur_between k n t1) (noccur_between (S k) n m)
| Coq_tLambda (_, t1, m) ->
  (&&) (noccur_between k n t1) (noccur_between (S k) n m)
| Coq_tLetIn (_, b, t1, b') ->
  (&&) ((&&) (noccur_between k n b) (noccur_between k n t1))
    (noccur_between (S k) n b')
| Coq_tApp (u, v) -> (&&) (noccur_between k n u) (noccur_between k n v)
| Coq_tCase (_, p, c, brs) ->
  let p' =
    test_predicate_k (fun _ -> true) (fun k' -> noccur_between k' n) k p
  in
  let brs' = forallb (test_branch_k p (fun k0 -> noccur_between k0 n) k) brs
  in
  (&&) ((&&) p' (noccur_between k n c)) brs'
| Coq_tProj (_, c) -> noccur_between k n c
| Coq_tFix (mfix, _) ->
  let k' = add (length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = add (length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| Coq_tPrim p -> test_prim (noccur_between k n) p
| _ -> true

(** val subst_instance_constr : term coq_UnivSubst **)

let rec subst_instance_constr u c = match c with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst_instance_constr u) args))
| Coq_tSort s -> Coq_tSort (subst_instance_sort u s)
| Coq_tProd (na, a, b) ->
  Coq_tProd (na, (subst_instance_constr u a), (subst_instance_constr u b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst_instance_constr u t0), (subst_instance_constr u m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst_instance_constr u b), (subst_instance_constr u ty),
    (subst_instance_constr u b'))
| Coq_tApp (f, v) ->
  Coq_tApp ((subst_instance_constr u f), (subst_instance_constr u v))
| Coq_tConst (c0, u') -> Coq_tConst (c0, (subst_instance_instance u u'))
| Coq_tInd (i, u') -> Coq_tInd (i, (subst_instance_instance u u'))
| Coq_tConstruct (ind, k, u') ->
  Coq_tConstruct (ind, k, (subst_instance_instance u u'))
| Coq_tCase (ind, p, c0, brs) ->
  let p' =
    map_predicate (subst_instance_instance u) (subst_instance_constr u)
      (subst_instance_constr u) (Obj.magic id) p
  in
  let brs' = map (map_branch (subst_instance_constr u) (Obj.magic id)) brs in
  Coq_tCase (ind, p', (subst_instance_constr u c0), brs')
| Coq_tProj (p, c0) -> Coq_tProj (p, (subst_instance_constr u c0))
| Coq_tFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tCoFix (mfix', idx)
| Coq_tPrim p ->
  Coq_tPrim (mapu_prim (subst_instance_level u) (subst_instance_constr u) p)
| _ -> c

(** val closedu : nat -> term -> bool **)

let rec closedu k = function
| Coq_tEvar (_, args) -> forallb (closedu k) args
| Coq_tSort s -> closedu_sort k s
| Coq_tProd (_, t1, m) -> (&&) (closedu k t1) (closedu k m)
| Coq_tLambda (_, t1, m) -> (&&) (closedu k t1) (closedu k m)
| Coq_tLetIn (_, b, t1, b') ->
  (&&) ((&&) (closedu k b) (closedu k t1)) (closedu k b')
| Coq_tApp (u, v) -> (&&) (closedu k u) (closedu k v)
| Coq_tConst (_, u) -> closedu_instance k u
| Coq_tInd (_, u) -> closedu_instance k u
| Coq_tConstruct (_, _, u) -> closedu_instance k u
| Coq_tCase (_, p, c, brs) ->
  let p' = test_predicate_ku closedu_instance closedu k p in
  let brs' = forallb (test_branch (closedu (length p.puinst)) (closedu k)) brs
  in
  (&&) ((&&) p' (closedu k c)) brs'
| Coq_tProj (_, c) -> closedu k c
| Coq_tFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| Coq_tCoFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| Coq_tPrim p -> test_primu (closedu_level k) (closedu k) p
| _ -> true

module PCUICTerm =
 struct
  type term = Coq__1.term

  (** val tRel : nat -> Coq__1.term **)

  let tRel x =
    Coq_tRel x

  (** val tSort : Sort.t -> Coq__1.term **)

  let tSort x =
    Coq_tSort x

  (** val tProd : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tProd x x0 x1 =
    Coq_tProd (x, x0, x1)

  (** val tLambda : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLambda x x0 x1 =
    Coq_tLambda (x, x0, x1)

  (** val tLetIn :
      aname -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLetIn x x0 x1 x2 =
    Coq_tLetIn (x, x0, x1, x2)

  (** val tInd : inductive -> Instance.t -> Coq__1.term **)

  let tInd x x0 =
    Coq_tInd (x, x0)

  (** val tProj : projection -> Coq__1.term -> Coq__1.term **)

  let tProj x x0 =
    Coq_tProj (x, x0)

  (** val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term **)

  let mkApps =
    mkApps

  (** val lift : nat -> nat -> Coq__1.term -> Coq__1.term **)

  let lift =
    lift

  (** val subst : Coq__1.term list -> nat -> Coq__1.term -> Coq__1.term **)

  let subst =
    subst

  (** val closedn : nat -> Coq__1.term -> bool **)

  let closedn =
    closedn

  (** val noccur_between : nat -> nat -> Coq__1.term -> bool **)

  let noccur_between =
    noccur_between

  (** val subst_instance_constr : Instance.t -> Coq__1.term -> Coq__1.term **)

  let subst_instance_constr =
    subst_instance subst_instance_constr
 end

module PCUICEnvironment = Environment.Environment(PCUICTerm)

(** val destArity :
    term context_decl list -> term -> (term context_decl list * Sort.t) option **)

let rec destArity _UU0393_ = function
| Coq_tSort s -> Some (_UU0393_, s)
| Coq_tProd (na, t1, b) ->
  destArity (snoc _UU0393_ (PCUICEnvironment.vass na t1)) b
| Coq_tLetIn (na, b, b_ty, b') ->
  destArity (snoc _UU0393_ (PCUICEnvironment.vdef na b b_ty)) b'
| _ -> None

(** val inds :
    kername -> Instance.t -> PCUICEnvironment.one_inductive_body list -> term
    list **)

let inds ind u l =
  let rec aux = function
  | O -> []
  | S n0 ->
    (Coq_tInd ({ inductive_mind = ind; inductive_ind = n0 }, u)) :: (aux n0)
  in aux (length l)

module PCUICTermUtils =
 struct
  (** val destArity :
      term context_decl list -> term -> (term context_decl list * Sort.t)
      option **)

  let destArity =
    destArity

  (** val inds :
      kername -> Instance.t -> PCUICEnvironment.one_inductive_body list ->
      term list **)

  let inds =
    inds
 end

module PCUICEnvTyping = EnvTyping(PCUICTerm)(PCUICEnvironment)(PCUICTermUtils)

module PCUICConversion =
 Conversion(PCUICTerm)(PCUICEnvironment)(PCUICTermUtils)(PCUICEnvTyping)

(** val context_reflect :
    term coq_ReflectEq -> term context_decl list coq_ReflectEq **)

let context_reflect h =
  reflect_list (eq_decl_reflect h)

(** val string_of_predicate :
    ('a1 -> String.t) -> 'a1 predicate -> String.t **)

let string_of_predicate f p =
  String.append (String.String (Coq_x28, String.EmptyString))
    (String.append (String.String (Coq_x28, String.EmptyString))
      (String.append
        (String.concat (String.String (Coq_x2c, String.EmptyString))
          (map f p.pparams))
        (String.append (String.String (Coq_x29, String.EmptyString))
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_universe_instance p.puinst)
              (String.append (String.String (Coq_x2c, (String.String
                (Coq_x28, String.EmptyString))))
                (String.append
                  (String.concat (String.String (Coq_x2c,
                    String.EmptyString))
                    (map
                      (let g0 =
                         let f0 = fun b -> b.binder_name in
                         (fun x -> string_of_name (f0 x))
                       in
                       let f0 = fun c -> c.decl_name in (fun x -> g0 (f0 x)))
                      p.pcontext))
                  (String.append (String.String (Coq_x29,
                    String.EmptyString))
                    (String.append (String.String (Coq_x2c,
                      String.EmptyString))
                      (String.append (f p.preturn) (String.String (Coq_x29,
                        String.EmptyString))))))))))))

(** val eqb_predicate_gen :
    (Instance.t -> Instance.t -> bool) -> (term context_decl -> term
    context_decl -> bool) -> (term -> term -> bool) -> term predicate -> term
    predicate -> bool **)

let eqb_predicate_gen eqb_univ_instance eqdecl eqterm p p' =
  (&&)
    ((&&)
      ((&&) (forallb2 eqterm p.pparams p'.pparams)
        (eqb_univ_instance p.puinst p'.puinst))
      (forallb2 eqdecl p.pcontext p'.pcontext)) (eqterm p.preturn p'.preturn)

(** val eqb_predicate :
    (term -> term -> bool) -> term predicate -> term predicate -> bool **)

let eqb_predicate eqterm p p' =
  eqb_predicate_gen (reflect_list Level.reflect_level)
    (eqb_context_decl eqterm) eqterm p p'

type 'p tCasePredProp_k = (term, 'p) coq_All * ((term, 'p) onctx_k * 'p)

type ('term, 'pparams, 'preturn) tCasePredProp =
  ('term, 'pparams) coq_All * (('term context_decl, ('term, 'pparams) ondecl)
  coq_All * 'preturn)

(** val test_prim_primProp :
    ('a1 -> bool) -> 'a1 prim_val -> ('a1, __) tPrimProp **)

let test_prim_primProp p = function
| Coq_existT (_, p1) ->
  (match p1 with
   | Coq_primArrayModel a ->
     let _evar_0_ = fun _ _ -> (__, (__, (forallb_All p a.array_value))) in
     Obj.magic _evar_0_ __ __
   | _ -> Obj.magic ())

(** val tPrimProp_impl :
    'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3)
    tPrimProp **)

let tPrimProp_impl p hp hpq =
  let Coq_existT (_, p0) = p in
  (match p0 with
   | Coq_primArrayModel a ->
     let (a0, b) = Obj.magic hp in
     let (a1, b0) = b in
     Obj.magic ((hpq a.array_type a0), ((hpq a.array_default a1),
       (coq_All_impl a.array_value b0 hpq)))
   | _ -> hp)

(** val tPrimProp_prod :
    'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a3) tPrimProp -> ('a1,
    'a2 * 'a3) tPrimProp **)

let tPrimProp_prod p h h0 =
  let Coq_existT (_, p0) = p in
  (match p0 with
   | Coq_primArrayModel a ->
     let (a0, b) = Obj.magic h in
     let (a1, b0) = Obj.magic h0 in
     let (a2, b1) = b in
     let (a3, b2) = b0 in
     Obj.magic ((a0, a1), ((a2, a3), (coq_All_prod a.array_value b1 b2)))
   | _ -> h0)

(** val primProp_map :
    ('a1 -> 'a1) -> 'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a2)
    tPrimProp **)

let primProp_map f p h =
  let Coq_existT (_, p0) = p in
  (match p0 with
   | Coq_primArrayModel a ->
     let (a0, b) = Obj.magic h in
     let (a1, b0) = b in
     Obj.magic (a0, (a1, (coq_All_map f a.array_value b0)))
   | _ -> h)

(** val primProp_map_inv :
    ('a1 -> 'a1) -> 'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a2)
    tPrimProp **)

let primProp_map_inv f p h =
  let Coq_existT (_, p0) = p in
  (match p0 with
   | Coq_primArrayModel a ->
     let (a0, b) = Obj.magic h in
     let (a1, b0) = b in
     Obj.magic (a0, (a1, (coq_All_map_inv f a.array_value b0)))
   | _ -> h)

type ('a, 'p) tCaseBrsProp =
  ('a branch, ('a context_decl, ('a, 'p) ondecl) coq_All * 'p) coq_All

type 'p tCaseBrsProp_k = (term branch, (term, 'p) onctx_k * 'p) coq_All

(** val onctx_k_rev :
    nat -> term context_decl list -> ((term, 'a1) onctx_k, (term
    context_decl, (term, 'a1) ondecl) coq_Alli) iffT **)

let onctx_k_rev _ ctx =
  ((fun hi ->
    forall_nth_error_Alli O (List0.rev ctx) (fun i x _ ->
      coq_Alli_nth_error O ctx (sub (length ctx) (S i)) x hi)), (fun hi ->
    forall_nth_error_Alli O ctx (fun i x _ ->
      coq_Alli_rev_nth_error ctx i x hi)))

(** val onctx_k_shift :
    nat -> term context_decl list -> (term, 'a1) onctx_k -> (term, 'a1)
    onctx_k **)

let onctx_k_shift k ctx hi =
  let x = let (x, _) = onctx_k_rev k ctx in x in
  let hi0 = x hi in
  let (_, x0) = onctx_k_rev O ctx in
  x0 (coq_Alli_impl (List0.rev ctx) O hi0 (fun _ _ x1 -> x1))

(** val onctx_k_P :
    (nat -> term -> bool) -> nat -> PCUICEnvironment.context -> (nat -> term
    -> 'a1 reflectT) -> (term, 'a1) onctx_k reflectT **)

let onctx_k_P p k ctx hP =
  equiv_reflectT (test_context_k p k ctx) (fun _ ->
    let (_, x) = onctx_k_rev k ctx in
    x
      (let rec f = function
       | [] -> Alli_nil
       | y :: l0 ->
         coq_Alli_app_inv (List0.rev l0) (y :: []) O (f l0) (Alli_cons (y,
           [],
           (elimT (test_decl (p (add (length l0) k)) y)
             (ondeclP (p (add (length l0) k)) y (hP (add (length l0) k)))),
           Alli_nil))
       in f ctx))

module PCUICLookup = Lookup(PCUICTerm)(PCUICEnvironment)

(** val lookup_constant_gen :
    (kername -> PCUICEnvironment.global_decl option) -> kername ->
    PCUICEnvironment.constant_body option **)

let lookup_constant_gen lookup kn =
  match lookup kn with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl d -> Some d
     | PCUICEnvironment.InductiveDecl _ -> None)
  | None -> None

(** val lookup_constant :
    PCUICEnvironment.global_env -> kername -> PCUICEnvironment.constant_body
    option **)

let lookup_constant _UU03a3_ =
  lookup_constant_gen (PCUICEnvironment.lookup_env _UU03a3_)

(** val lookup_minductive_gen :
    (kername -> PCUICEnvironment.global_decl option) -> kername ->
    PCUICEnvironment.mutual_inductive_body option **)

let lookup_minductive_gen lookup mind =
  match lookup mind with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl _ -> None
     | PCUICEnvironment.InductiveDecl decl -> Some decl)
  | None -> None

(** val lookup_minductive :
    PCUICEnvironment.global_env -> kername ->
    PCUICEnvironment.mutual_inductive_body option **)

let lookup_minductive _UU03a3_ =
  lookup_minductive_gen (PCUICEnvironment.lookup_env _UU03a3_)

(** val lookup_inductive_gen :
    (kername -> PCUICEnvironment.global_decl option) -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option **)

let lookup_inductive_gen lookup ind =
  match lookup_minductive_gen lookup ind.inductive_mind with
  | Some mdecl ->
    (match nth_error (PCUICEnvironment.ind_bodies mdecl) ind.inductive_ind with
     | Some idecl -> Some (mdecl, idecl)
     | None -> None)
  | None -> None

(** val lookup_inductive :
    PCUICEnvironment.global_env -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option **)

let lookup_inductive _UU03a3_ =
  lookup_inductive_gen (PCUICEnvironment.lookup_env _UU03a3_)

(** val lookup_constructor_gen :
    (kername -> PCUICEnvironment.global_decl option) -> inductive -> nat ->
    ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
    option **)

let lookup_constructor_gen lookup ind k =
  match lookup_inductive_gen lookup ind with
  | Some p ->
    let (mdecl, idecl) = p in
    (match nth_error (PCUICEnvironment.ind_ctors idecl) k with
     | Some cdecl -> Some ((mdecl, idecl), cdecl)
     | None -> None)
  | None -> None

(** val lookup_constructor :
    PCUICEnvironment.global_env -> inductive -> nat ->
    ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
    option **)

let lookup_constructor _UU03a3_ =
  lookup_constructor_gen (PCUICEnvironment.lookup_env _UU03a3_)

(** val lookup_projection_gen :
    (kername -> PCUICEnvironment.global_decl option) -> projection ->
    (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
    option **)

let lookup_projection_gen lookup p =
  match lookup_constructor_gen lookup p.proj_ind O with
  | Some p0 ->
    let (p1, cdecl) = p0 in
    let (mdecl, idecl) = p1 in
    (match nth_error (PCUICEnvironment.ind_projs idecl) p.proj_arg with
     | Some pdecl -> Some (((mdecl, idecl), cdecl), pdecl)
     | None -> None)
  | None -> None

(** val lookup_projection :
    PCUICEnvironment.global_env -> projection ->
    (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
    option **)

let lookup_projection _UU03a3_ =
  lookup_projection_gen (PCUICEnvironment.lookup_env _UU03a3_)

(** val on_udecl_decl :
    (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1 **)

let on_udecl_decl f = function
| PCUICEnvironment.ConstantDecl cb -> f (PCUICEnvironment.cst_universes cb)
| PCUICEnvironment.InductiveDecl mb -> f (PCUICEnvironment.ind_universes mb)

(** val universes_decl_of_decl :
    PCUICEnvironment.global_decl -> universes_decl **)

let universes_decl_of_decl =
  on_udecl_decl (fun x -> x)

(** val global_levels : ContextSet.t -> LevelSet.t **)

let global_levels univs =
  LevelSet.union (ContextSet.levels univs)
    (LevelSet.singleton Level.Coq_lzero)

(** val global_constraints :
    PCUICEnvironment.global_env -> ConstraintSet.t **)

let global_constraints _UU03a3_ =
  snd (PCUICEnvironment.universes _UU03a3_)

(** val global_uctx : PCUICEnvironment.global_env -> ContextSet.t **)

let global_uctx _UU03a3_ =
  ((global_levels (PCUICEnvironment.universes _UU03a3_)),
    (global_constraints _UU03a3_))

(** val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t **)

let global_ext_levels _UU03a3_ =
  LevelSet.union (levels_of_udecl (snd _UU03a3_))
    (global_levels (PCUICEnvironment.universes (fst _UU03a3_)))

(** val global_ext_constraints :
    PCUICEnvironment.global_env_ext -> ConstraintSet.t **)

let global_ext_constraints _UU03a3_ =
  ConstraintSet.union (constraints_of_udecl (snd _UU03a3_))
    (global_constraints (fst _UU03a3_))

(** val global_ext_uctx : PCUICEnvironment.global_env_ext -> ContextSet.t **)

let global_ext_uctx _UU03a3_ =
  ((global_ext_levels _UU03a3_), (global_ext_constraints _UU03a3_))

(** val wf_universe_dec :
    PCUICEnvironment.global_env_ext -> Universe.t -> bool **)

let rec wf_universe_dec _UU03a3_ = function
| [] -> true
| y :: l ->
  if wf_universe_dec _UU03a3_ l
  then LevelSetProp.coq_In_dec (LevelExpr.get_level y)
         (global_ext_levels _UU03a3_)
  else false

(** val wf_sort_dec : PCUICEnvironment.global_env_ext -> Sort.t -> bool **)

let wf_sort_dec _UU03a3_ = function
| Sort.Coq_sType t0 -> wf_universe_dec _UU03a3_ t0
| _ -> true

(** val declared_ind_declared_constructors :
    checker_flags -> PCUICEnvironment.global_env -> inductive ->
    PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.one_inductive_body ->
    (PCUICEnvironment.constructor_body, __) coq_Alli **)

let declared_ind_declared_constructors =
  PCUICLookup.declared_ind_declared_constructors

(** val coq_NoConfusionPackage_global_decl :
    PCUICEnvironment.global_decl coq_NoConfusionPackage **)

let coq_NoConfusionPackage_global_decl =
  Build_NoConfusionPackage

module PCUICGlobalMaps =
 GlobalMaps(PCUICTerm)(PCUICEnvironment)(PCUICTermUtils)(PCUICEnvTyping)(PCUICConversion)(PCUICLookup)

type 'p on_context = 'p PCUICEnvTyping.coq_All_local_env

type 'p type_local_ctx = __

type 'p sorts_local_ctx = __

type 'p on_type = 'p

(** val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t **)

let univs_ext_constraints univs _UU03c6_ =
  ConstraintSet.union (constraints_of_udecl _UU03c6_) univs

(** val ind_realargs : PCUICEnvironment.one_inductive_body -> nat **)

let ind_realargs o =
  match destArity [] (PCUICEnvironment.ind_type o) with
  | Some p ->
    let (ctx, _) = p in length (PCUICEnvironment.smash_context [] ctx)
  | None -> O

type positive_cstr_arg = PCUICGlobalMaps.positive_cstr_arg =
| Coq_pos_arg_closed of term
| Coq_pos_arg_concl of term list * nat * PCUICEnvironment.one_inductive_body
   * (term, __) coq_All
| Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
| Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

(** val positive_cstr_arg_rect :
    PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
    -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
    PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
    'a1) -> (term context_decl list -> aname -> term -> term -> term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
    term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term
    context_decl list -> term -> positive_cstr_arg -> 'a1 **)

let rec positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_ _ = function
| Coq_pos_arg_closed ty -> f _UU0393_ ty __
| Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
| Coq_pos_arg_let (na, b, ty, ty', p0) ->
  f1 _UU0393_ na b ty ty' p0
    (positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_ (subst (b :: []) O ty')
      p0)
| Coq_pos_arg_ass (na, ty, ty', p0) ->
  f2 _UU0393_ na ty ty' __ p0
    (positive_cstr_arg_rect mdecl f f0 f1 f2
      ((PCUICEnvironment.vass na ty) :: _UU0393_) ty' p0)

(** val positive_cstr_arg_rec :
    PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
    -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
    PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
    'a1) -> (term context_decl list -> aname -> term -> term -> term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
    term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term
    context_decl list -> term -> positive_cstr_arg -> 'a1 **)

let rec positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_ _ = function
| Coq_pos_arg_closed ty -> f _UU0393_ ty __
| Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
| Coq_pos_arg_let (na, b, ty, ty', p0) ->
  f1 _UU0393_ na b ty ty' p0
    (positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_ (subst (b :: []) O ty')
      p0)
| Coq_pos_arg_ass (na, ty, ty', p0) ->
  f2 _UU0393_ na ty ty' __ p0
    (positive_cstr_arg_rec mdecl f f0 f1 f2
      ((PCUICEnvironment.vass na ty) :: _UU0393_) ty' p0)

type positive_cstr = PCUICGlobalMaps.positive_cstr =
| Coq_pos_concl of term list * (term, __) coq_All
| Coq_pos_let of aname * term * term * term * positive_cstr
| Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

(** val positive_cstr_rect :
    PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list
    -> term list -> (term, __) coq_All -> 'a1) -> (term context_decl list ->
    aname -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> positive_cstr_arg ->
    positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr -> 'a1 **)

let rec positive_cstr_rect mdecl i f f0 f1 _UU0393_ _ = function
| Coq_pos_concl (l, x) -> f _UU0393_ l x
| Coq_pos_let (na, b, ty, ty', p0) ->
  f0 _UU0393_ na b ty ty' p0
    (positive_cstr_rect mdecl i f f0 f1 _UU0393_ (subst (b :: []) O ty') p0)
| Coq_pos_ass (na, ty, ty', p0, p1) ->
  f1 _UU0393_ na ty ty' p0 p1
    (positive_cstr_rect mdecl i f f0 f1
      ((PCUICEnvironment.vass na ty) :: _UU0393_) ty' p1)

(** val positive_cstr_rec :
    PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list
    -> term list -> (term, __) coq_All -> 'a1) -> (term context_decl list ->
    aname -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> positive_cstr_arg ->
    positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr -> 'a1 **)

let rec positive_cstr_rec mdecl i f f0 f1 _UU0393_ _ = function
| Coq_pos_concl (l, x) -> f _UU0393_ l x
| Coq_pos_let (na, b, ty, ty', p0) ->
  f0 _UU0393_ na b ty ty' p0
    (positive_cstr_rec mdecl i f f0 f1 _UU0393_ (subst (b :: []) O ty') p0)
| Coq_pos_ass (na, ty, ty', p0, p1) ->
  f1 _UU0393_ na ty ty' p0 p1
    (positive_cstr_rec mdecl i f f0 f1
      ((PCUICEnvironment.vass na ty) :: _UU0393_) ty' p1)

(** val lift_level : nat -> Level.t_ -> Level.t_ **)

let lift_level n l = match l with
| Level.Coq_lvar k -> Level.Coq_lvar (add n k)
| _ -> l

(** val lift_instance : nat -> Level.t_ list -> Level.t_ list **)

let lift_instance n l =
  map (lift_level n) l

(** val lift_constraint :
    nat -> ((Level.t * ConstraintType.t) * Level.t) ->
    (Level.t_ * ConstraintType.t) * Level.t_ **)

let lift_constraint n = function
| (p, l') -> let (l, r) = p in (((lift_level n l), r), (lift_level n l'))

(** val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t **)

let lift_constraints n cstrs =
  ConstraintSet.fold (fun elt acc ->
    ConstraintSet.add (lift_constraint n elt) acc) cstrs ConstraintSet.empty

(** val level_var_instance : nat -> name list -> Level.t_ list **)

let level_var_instance n inst =
  mapi_rec (fun i _ -> Level.Coq_lvar i) inst n

(** val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t **)

let rec variance_cstrs v u u' =
  match v with
  | [] -> ConstraintSet.empty
  | v0 :: vs ->
    (match u with
     | [] -> ConstraintSet.empty
     | u0 :: us ->
       (match u' with
        | [] -> ConstraintSet.empty
        | u'0 :: us' ->
          (match v0 with
           | Variance.Irrelevant -> variance_cstrs vs us us'
           | Variance.Covariant ->
             ConstraintSet.add ((u0, (ConstraintType.Le Z0)), u'0)
               (variance_cstrs vs us us')
           | Variance.Invariant ->
             ConstraintSet.add ((u0, ConstraintType.Eq), u'0)
               (variance_cstrs vs us us'))))

(** val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl * Level.t_
    list) * Level.t_ list) option **)

let variance_universes univs v =
  match univs with
  | Monomorphic_ctx -> None
  | Polymorphic_ctx auctx ->
    let (inst, cstrs) = auctx in
    let u' = level_var_instance O inst in
    let u = lift_instance (length inst) u' in
    let cstrs0 =
      ConstraintSet.union cstrs (lift_constraints (length inst) cstrs)
    in
    let cstrv = variance_cstrs v u u' in
    let auctx' = ((app inst inst), (ConstraintSet.union cstrs0 cstrv)) in
    Some (((Polymorphic_ctx auctx'), u), u')

(** val ind_arities :
    PCUICEnvironment.mutual_inductive_body -> term context_decl list **)

let ind_arities mdecl =
  PCUICEnvironment.arities_context (PCUICEnvironment.ind_bodies mdecl)

type 'pcmp ind_respects_variance = __

type 'pcmp cstr_respects_variance = __

(** val cstr_concl_head :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term **)

let cstr_concl_head mdecl i cdecl =
  Coq_tRel
    (add
      (add (sub (length (PCUICEnvironment.ind_bodies mdecl)) (S i))
        (length (PCUICEnvironment.ind_params mdecl)))
      (length (PCUICEnvironment.cstr_args cdecl)))

(** val cstr_concl :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term **)

let cstr_concl mdecl i cdecl =
  mkApps (cstr_concl_head mdecl i cdecl)
    (app
      (PCUICEnvironment.to_extended_list_k
        (PCUICEnvironment.ind_params mdecl)
        (length (PCUICEnvironment.cstr_args cdecl)))
      (PCUICEnvironment.cstr_indices cdecl))

type ('pcmp, 'p) on_constructor = ('pcmp, 'p) PCUICGlobalMaps.on_constructor = { 
on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
on_cindices : 'p PCUICEnvTyping.ctx_inst; on_ctype_positive : positive_cstr;
on_ctype_variance : (Variance.t list -> __ -> 'pcmp cstr_respects_variance) }

(** val on_ctype :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 on_type **)

let on_ctype _ _ _ _ _ _ _ _ o =
  o.on_ctype

(** val on_cargs :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 sorts_local_ctx **)

let on_cargs _ _ _ _ _ _ _ _ o =
  o.on_cargs

(** val on_cindices :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 PCUICEnvTyping.ctx_inst **)

let on_cindices _ _ _ _ _ _ _ _ o =
  o.on_cindices

(** val on_ctype_positive :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> positive_cstr **)

let on_ctype_positive _ _ _ _ _ _ _ _ o =
  o.on_ctype_positive

(** val on_ctype_variance :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> Variance.t list -> 'a1 cstr_respects_variance **)

let on_ctype_variance _ _ _ _ _ _ _ _ o v =
  o.on_ctype_variance v __

type ('pcmp, 'p) on_constructors =
  (PCUICEnvironment.constructor_body, Sort.t list, ('pcmp, 'p)
  on_constructor) coq_All2

type on_projections =
  (PCUICEnvironment.projection_body, __) coq_Alli
  (* singleton inductive, whose constructor was Build_on_projections *)

(** val on_projs :
    PCUICEnvironment.mutual_inductive_body -> kername -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> on_projections ->
    (PCUICEnvironment.projection_body, __) coq_Alli **)

let on_projs _ _ _ _ _ _ o =
  o

type constructor_univs = Sort.t list

(** val elim_sort_prop_ind :
    constructor_univs list -> allowed_eliminations **)

let elim_sort_prop_ind = function
| [] -> IntoAny
| s :: l ->
  (match l with
   | [] -> if forallb Sort.is_propositional s then IntoAny else IntoPropSProp
   | _ :: _ -> IntoPropSProp)

(** val elim_sort_sprop_ind :
    constructor_univs list -> allowed_eliminations **)

let elim_sort_sprop_ind = function
| [] -> IntoAny
| _ :: _ -> IntoSProp

type 'p check_ind_sorts = __

type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) PCUICGlobalMaps.on_ind_body = { 
onArity : 'p on_type; ind_cunivs : constructor_univs list;
onConstructors : ('pcmp, 'p) on_constructors; onProjections : __;
ind_sorts : 'p check_ind_sorts; onIndices : __ }

(** val onArity :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    on_type **)

let onArity _ _ _ _ _ _ o =
  o.onArity

(** val ind_cunivs :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list **)

let ind_cunivs _ _ _ _ _ _ o =
  o.ind_cunivs

(** val onConstructors :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1,
    'a2) on_constructors **)

let onConstructors _ _ _ _ _ _ o =
  o.onConstructors

(** val onProjections :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

let onProjections _ _ _ _ _ _ o =
  o.onProjections

(** val ind_sorts :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts **)

let ind_sorts _ _ _ _ _ _ o =
  o.ind_sorts

(** val onIndices :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

let onIndices _ _ _ _ _ _ o =
  o.onIndices

type on_variance = __

type ('pcmp, 'p) on_inductive = ('pcmp, 'p) PCUICGlobalMaps.on_inductive = { 
onInductives : (PCUICEnvironment.one_inductive_body, ('pcmp, 'p) on_ind_body)
               coq_Alli; onParams : 'p on_context; onVariance : on_variance }

(** val onInductives :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    (PCUICEnvironment.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli **)

let onInductives _ _ _ _ o =
  o.onInductives

(** val onParams :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2
    on_context **)

let onParams _ _ _ _ o =
  o.onParams

(** val onVariance :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    on_variance **)

let onVariance _ _ _ _ o =
  o.onVariance

type 'p on_constant_decl = 'p

type ('pcmp, 'p) on_global_decl = __

type ('pcmp, 'p) on_global_decls_data =
  ('pcmp, 'p) on_global_decl
  (* singleton inductive, whose constructor was Build_on_global_decls_data *)

(** val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
    universes_decl **)

let udecl _ _ _ _ _ d _ =
  PCUICLookup.universes_decl_of_decl d

(** val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data -> ('a1,
    'a2) on_global_decl **)

let on_global_decl_d _ _ _ _ _ _ o =
  o

type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) PCUICGlobalMaps.on_global_decls =
| Coq_globenv_nil
| Coq_globenv_decl of PCUICEnvironment.global_declarations * kername
   * PCUICEnvironment.global_decl * ('pcmp, 'p) on_global_decls
   * ('pcmp, 'p) on_global_decls_data

(** val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

let rec on_global_decls_rect cf univs retro f f0 _ = function
| Coq_globenv_nil -> f
| Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
  f0 _UU03a3_ kn d o0 (on_global_decls_rect cf univs retro f f0 _UU03a3_ o0)
    o1

(** val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

let rec on_global_decls_rec cf univs retro f f0 _ = function
| Coq_globenv_nil -> f
| Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
  f0 _UU03a3_ kn d o0 (on_global_decls_rec cf univs retro f f0 _UU03a3_ o0) o1

type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

(** val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
    PCUICEnvironment.global_declarations * ('a1, 'a2) on_global_decls **)

let on_global_decls_sig_pack _ _ _ x on_global_decls_var =
  x,on_global_decls_var

(** val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> (('a1, 'a2) on_global_decls,
    PCUICEnvironment.global_declarations, ('a1, 'a2) on_global_decls_sig)
    coq_Signature **)

let on_global_decls_Signature _ _ _ x on_global_decls_var =
  x,on_global_decls_var

type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

(** val on_global_env_ext_empty_ext :
    checker_flags -> PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a2) on_global_env_ext **)

let on_global_env_ext_empty_ext =
  PCUICGlobalMaps.on_global_env_ext_empty_ext

(** val type_local_ctx_impl_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Sort.t -> __ list -> (__, __ type_local_ctx)
    sigT -> (PCUICEnvironment.context -> PCUICEnvironment.judgment -> (__,
    __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx **)

let type_local_ctx_impl_gen =
  PCUICGlobalMaps.type_local_ctx_impl_gen

(** val type_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t -> 'a1
    type_local_ctx -> (PCUICEnvironment.context -> PCUICEnvironment.judgment
    -> 'a1 -> 'a2) -> 'a2 type_local_ctx **)

let type_local_ctx_impl =
  PCUICGlobalMaps.type_local_ctx_impl

(** val sorts_local_ctx_impl_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Sort.t list -> __ list -> (__, __
    sorts_local_ctx) sigT -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> (__, __) coq_All -> 'a1) -> (__, __
    sorts_local_ctx) coq_All -> 'a1 sorts_local_ctx **)

let sorts_local_ctx_impl_gen =
  PCUICGlobalMaps.sorts_local_ctx_impl_gen

(** val sorts_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t list ->
    'a1 sorts_local_ctx -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> 'a1 -> 'a2) -> 'a2 sorts_local_ctx **)

let sorts_local_ctx_impl =
  PCUICGlobalMaps.sorts_local_ctx_impl

(** val cstr_respects_variance_impl_gen :
    PCUICEnvironment.global_env -> PCUICEnvironment.mutual_inductive_body ->
    Variance.t list -> PCUICEnvironment.constructor_body -> __ list -> (__,
    __ cstr_respects_variance) sigT -> __ -> (__, __ cstr_respects_variance)
    coq_All -> 'a1 cstr_respects_variance **)

let cstr_respects_variance_impl_gen =
  PCUICGlobalMaps.cstr_respects_variance_impl_gen

(** val cstr_respects_variance_impl :
    PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
    PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
    PCUICEnvironment.constructor_body -> __ -> 'a1 cstr_respects_variance ->
    'a2 cstr_respects_variance **)

let cstr_respects_variance_impl =
  PCUICGlobalMaps.cstr_respects_variance_impl

(** val on_constructor_impl_config_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
    -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
    -> PCUICEnvironment.constructor_body -> Sort.t list ->
    ((checker_flags * __) * __) list -> checker_flags ->
    ((checker_flags * __) * __, __) sigT -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ((checker_flags * __) * __, __) coq_All ->
    'a2) -> (universes_decl -> PCUICEnvironment.context -> term -> term ->
    conv_pb -> ((checker_flags * __) * __, __) coq_All -> 'a1) ->
    ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructor **)

let on_constructor_impl_config_gen =
  PCUICGlobalMaps.on_constructor_impl_config_gen

(** val on_constructors_impl_config_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
    -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
    -> PCUICEnvironment.constructor_body list -> Sort.t list list ->
    ((checker_flags * __) * __) list -> checker_flags ->
    ((checker_flags * __) * __, __) sigT -> ((checker_flags * __) * __, __)
    coq_All -> (PCUICEnvironment.context -> PCUICEnvironment.judgment ->
    ((checker_flags * __) * __, __) coq_All -> 'a2) -> (universes_decl ->
    PCUICEnvironment.context -> term -> term -> conv_pb ->
    ((checker_flags * __) * __, __) coq_All -> 'a1) ->
    ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructors **)

let on_constructors_impl_config_gen =
  PCUICGlobalMaps.on_constructors_impl_config_gen

(** val ind_respects_variance_impl :
    PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
    PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
    PCUICEnvironment.context -> __ -> 'a1 ind_respects_variance -> 'a2
    ind_respects_variance **)

let ind_respects_variance_impl =
  PCUICGlobalMaps.ind_respects_variance_impl

(** val on_variance_impl :
    PCUICEnvironment.global_env -> universes_decl -> Variance.t list option
    -> checker_flags -> checker_flags -> on_variance -> on_variance **)

let on_variance_impl =
  PCUICGlobalMaps.on_variance_impl

(** val on_global_decl_impl_full :
    checker_flags -> checker_flags ->
    (PCUICEnvironment.global_env * universes_decl) ->
    (PCUICEnvironment.global_env * universes_decl) -> kername ->
    PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> 'a3 -> 'a4) -> (universes_decl ->
    PCUICEnvironment.context -> conv_pb -> term -> term -> 'a1 -> 'a2) ->
    (universes_decl -> Variance.t list option -> on_variance -> on_variance)
    -> ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl **)

let on_global_decl_impl_full =
  PCUICGlobalMaps.on_global_decl_impl_full

(** val on_global_decl_impl_only_config :
    checker_flags -> checker_flags -> checker_flags ->
    (PCUICEnvironment.global_env * universes_decl) -> kername ->
    PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ('a1, 'a3) on_global_env -> 'a3 -> 'a4) ->
    (universes_decl -> PCUICEnvironment.context -> conv_pb -> term -> term ->
    ('a1, 'a3) on_global_env -> 'a1 -> 'a2) -> ('a1, 'a3) on_global_env ->
    ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl **)

let on_global_decl_impl_only_config =
  PCUICGlobalMaps.on_global_decl_impl_only_config

(** val on_global_decl_impl_simple :
    checker_flags -> (PCUICEnvironment.global_env * universes_decl) ->
    kername -> PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ('a1, 'a2) on_global_env -> 'a2 -> 'a3) ->
    ('a1, 'a2) on_global_env -> ('a1, 'a2) on_global_decl -> ('a1, 'a3)
    on_global_decl **)

let on_global_decl_impl_simple =
  PCUICGlobalMaps.on_global_decl_impl_simple

(** val on_global_env_impl_config :
    checker_flags -> checker_flags ->
    ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> PCUICEnvironment.judgment -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env -> 'a3 -> 'a4) ->
    ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> term -> term -> conv_pb -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) ->
    PCUICEnvironment.global_env -> ('a1, 'a3) on_global_env -> ('a2, 'a4)
    on_global_env **)

let on_global_env_impl_config =
  PCUICGlobalMaps.on_global_env_impl_config

(** val on_global_env_impl :
    checker_flags -> ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> PCUICEnvironment.judgment -> ('a1, 'a2)
    on_global_env -> ('a1, 'a3) on_global_env -> 'a2 -> 'a3) ->
    PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env **)

let on_global_env_impl =
  PCUICGlobalMaps.on_global_env_impl

(** val lookup_on_global_env :
    checker_flags -> PCUICEnvironment.global_env -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_env ->
    (PCUICEnvironment.global_env_ext, ('a1, 'a2)
    on_global_env * (PCUICEnvironment.strictly_extends_decls * ('a1, 'a2)
    on_global_decl)) sigT **)

let lookup_on_global_env =
  PCUICGlobalMaps.lookup_on_global_env

type parameter_entry = { parameter_entry_type : term;
                         parameter_entry_universes : universes_decl }

(** val parameter_entry_type : parameter_entry -> term **)

let parameter_entry_type p =
  p.parameter_entry_type

(** val parameter_entry_universes : parameter_entry -> universes_decl **)

let parameter_entry_universes p =
  p.parameter_entry_universes

type definition_entry = { definition_entry_type : term;
                          definition_entry_body : term;
                          definition_entry_universes : universes_decl;
                          definition_entry_opaque : bool }

(** val definition_entry_type : definition_entry -> term **)

let definition_entry_type d =
  d.definition_entry_type

(** val definition_entry_body : definition_entry -> term **)

let definition_entry_body d =
  d.definition_entry_body

(** val definition_entry_universes : definition_entry -> universes_decl **)

let definition_entry_universes d =
  d.definition_entry_universes

(** val definition_entry_opaque : definition_entry -> bool **)

let definition_entry_opaque d =
  d.definition_entry_opaque

type constant_entry =
| ParameterEntry of parameter_entry
| DefinitionEntry of definition_entry

(** val constant_entry_rect :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rect f f0 = function
| ParameterEntry p -> f p
| DefinitionEntry def0 -> f0 def0

(** val constant_entry_rec :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rec f f0 = function
| ParameterEntry p -> f p
| DefinitionEntry def0 -> f0 def0

(** val coq_NoConfusionPackage_parameter_entry :
    parameter_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_parameter_entry =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_definition_entry :
    definition_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_definition_entry =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_constant_entry :
    constant_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_constant_entry =
  Build_NoConfusionPackage

type local_entry =
| LocalDef of term
| LocalAssum of term

(** val local_entry_rect :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rect f f0 = function
| LocalDef t0 -> f t0
| LocalAssum t0 -> f0 t0

(** val local_entry_rec :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rec f f0 = function
| LocalDef t0 -> f t0
| LocalAssum t0 -> f0 t0

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_template : bool;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

(** val mind_entry_typename : one_inductive_entry -> ident **)

let mind_entry_typename o =
  o.mind_entry_typename

(** val mind_entry_arity : one_inductive_entry -> term **)

let mind_entry_arity o =
  o.mind_entry_arity

(** val mind_entry_template : one_inductive_entry -> bool **)

let mind_entry_template o =
  o.mind_entry_template

(** val mind_entry_consnames : one_inductive_entry -> ident list **)

let mind_entry_consnames o =
  o.mind_entry_consnames

(** val mind_entry_lc : one_inductive_entry -> term list **)

let mind_entry_lc o =
  o.mind_entry_lc

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : PCUICEnvironment.context;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_universes : universes_decl;
                                mind_entry_private : bool option }

(** val mind_entry_record : mutual_inductive_entry -> ident option option **)

let mind_entry_record m =
  m.mind_entry_record

(** val mind_entry_finite : mutual_inductive_entry -> recursivity_kind **)

let mind_entry_finite m =
  m.mind_entry_finite

(** val mind_entry_params :
    mutual_inductive_entry -> PCUICEnvironment.context **)

let mind_entry_params m =
  m.mind_entry_params

(** val mind_entry_inds :
    mutual_inductive_entry -> one_inductive_entry list **)

let mind_entry_inds m =
  m.mind_entry_inds

(** val mind_entry_universes : mutual_inductive_entry -> universes_decl **)

let mind_entry_universes m =
  m.mind_entry_universes

(** val mind_entry_private : mutual_inductive_entry -> bool option **)

let mind_entry_private m =
  m.mind_entry_private

(** val coq_NoConfusionPackage_local_entry :
    local_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_local_entry =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_one_inductive_entry :
    one_inductive_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_one_inductive_entry =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_mutual_inductive_entry :
    mutual_inductive_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_mutual_inductive_entry =
  Build_NoConfusionPackage
