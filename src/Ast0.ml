open All_Forall
open BasicAst
open CRelationClasses
open Classes0
open Datatypes
open Kernames
open List0
open MCProd
open Nat0
open PeanoNat
open PrimString
open Primitive
open Signature
open Specif
open Universes0

type __ = Obj.t

type 'term predicate = { puinst : Instance.t; pparams : 'term list;
                         pcontext : aname list; preturn : 'term }

(** val test_predicate :
    (Instance.t -> bool) -> ('a1 -> bool) -> ('a1 -> bool) -> 'a1 predicate
    -> bool **)

let test_predicate instf paramf preturnf p =
  (&&) ((&&) (instf p.puinst) (forallb paramf p.pparams)) (preturnf p.preturn)

(** val map_predicate :
    (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1
    predicate -> 'a2 predicate **)

let map_predicate uf paramf preturnf p =
  { puinst = (uf p.puinst); pparams = (map paramf p.pparams); pcontext =
    p.pcontext; preturn = (preturnf p.preturn) }

type 'term branch = { bcontext : aname list; bbody : 'term }

(** val test_branch : ('a1 -> bool) -> 'a1 branch -> bool **)

let test_branch bodyf b =
  bodyf b.bbody

(** val map_branch : ('a1 -> 'a2) -> 'a1 branch -> 'a2 branch **)

let map_branch bbodyf b =
  { bcontext = b.bcontext; bbody = (bbodyf b.bbody) }

module Coq__1 = struct
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Sort.t
 | Coq_tCast of term * cast_kind * term
 | Coq_tProd of aname * term * term
 | Coq_tLambda of aname * term * term
 | Coq_tLetIn of aname * term * term * term
 | Coq_tApp of term * term list
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of case_info * term predicate * term * term branch list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
 | Coq_tInt of Uint63.t
 | Coq_tFloat of Float64.t
 | Coq_tString of string
 | Coq_tArray of Level.t * term list * term * term
end
include Coq__1

(** val mkApps : term -> term list -> term **)

let mkApps t0 us = match us with
| [] -> t0
| _ :: _ ->
  (match t0 with
   | Coq_tApp (f, args) -> Coq_tApp (f, (app args us))
   | _ -> Coq_tApp (t0, us))

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t0 = match t0 with
| Coq_tRel i -> Coq_tRel (if Nat.leb k i then add n i else i)
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tCast (c, kind, t1) -> Coq_tCast ((lift n k c), kind, (lift n k t1))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (lift n k a), (lift n (S k) b))
| Coq_tLambda (na, t1, m) -> Coq_tLambda (na, (lift n k t1), (lift n (S k) m))
| Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (lift n k b), (lift n k t1), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (map (lift n k) v))
| Coq_tCase (ind, p, c, brs) ->
  let k' = add (Datatypes.length p.pcontext) k in
  let p' = map_predicate (Obj.magic id) (lift n k) (lift n k') p in
  let brs' =
    map (fun b ->
      map_branch (lift n (add (Datatypes.length b.bcontext) k)) b) brs
  in
  Coq_tCase (ind, p', (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (Datatypes.length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (Datatypes.length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tArray (u, arr, def, ty) ->
  Coq_tArray (u, (map (lift n k) arr), (lift n k def), (lift n k ty))
| _ -> t0

(** val subst : term list -> nat -> term -> term **)

let rec subst s k u = match u with
| Coq_tRel n ->
  if Nat.leb k n
  then (match nth_error s (sub n k) with
        | Some b -> lift k O b
        | None -> Coq_tRel (sub n (Datatypes.length s)))
  else Coq_tRel n
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst s k) args))
| Coq_tCast (c, kind, ty) -> Coq_tCast ((subst s k c), kind, (subst s k ty))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (subst s k a), (subst s (S k) b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst s k t0), (subst s (S k) m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst s k b), (subst s k ty), (subst s (S k) b'))
| Coq_tApp (u0, v) -> mkApps (subst s k u0) (map (subst s k) v)
| Coq_tCase (ind, p, c, brs) ->
  let k' = add (Datatypes.length p.pcontext) k in
  let p' = map_predicate (Obj.magic id) (subst s k) (subst s k') p in
  let brs' =
    map (fun b ->
      map_branch (subst s (add (Datatypes.length b.bcontext) k)) b) brs
  in
  Coq_tCase (ind, p', (subst s k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (subst s k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (Datatypes.length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (Datatypes.length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tArray (u0, arr, def, ty) ->
  Coq_tArray (u0, (map (subst s k) arr), (subst s k def), (subst s k ty))
| _ -> u

(** val closedn : nat -> term -> bool **)

let rec closedn k = function
| Coq_tRel i -> Nat.ltb i k
| Coq_tEvar (_, args) -> forallb (closedn k) args
| Coq_tCast (c, _, t1) -> (&&) (closedn k c) (closedn k t1)
| Coq_tProd (_, t1, m) -> (&&) (closedn k t1) (closedn (S k) m)
| Coq_tLambda (_, t1, m) -> (&&) (closedn k t1) (closedn (S k) m)
| Coq_tLetIn (_, b, t1, b') ->
  (&&) ((&&) (closedn k b) (closedn k t1)) (closedn (S k) b')
| Coq_tApp (u, v) -> (&&) (closedn k u) (forallb (closedn k) v)
| Coq_tCase (_, p, c, brs) ->
  let k' = add (Datatypes.length p.pcontext) k in
  let p' = test_predicate (fun _ -> true) (closedn k) (closedn k') p in
  let brs' =
    forallb (fun b ->
      test_branch (closedn (add (Datatypes.length b.bcontext) k)) b) brs
  in
  (&&) ((&&) p' (closedn k c)) brs'
| Coq_tProj (_, c) -> closedn k c
| Coq_tFix (mfix, _) ->
  let k' = add (Datatypes.length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = add (Datatypes.length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| Coq_tArray (_, arr, def, ty) ->
  (&&) ((&&) (forallb (closedn k) arr) (closedn k def)) (closedn k ty)
| _ -> true

(** val noccur_between : nat -> nat -> term -> bool **)

let rec noccur_between k n = function
| Coq_tRel i -> (&&) (Nat.ltb i k) (Nat.leb (add k n) i)
| Coq_tEvar (_, args) -> forallb (noccur_between k n) args
| Coq_tCast (c, _, t1) -> (&&) (noccur_between k n c) (noccur_between k n t1)
| Coq_tProd (_, t1, m) ->
  (&&) (noccur_between k n t1) (noccur_between (S k) n m)
| Coq_tLambda (_, t1, m) ->
  (&&) (noccur_between k n t1) (noccur_between (S k) n m)
| Coq_tLetIn (_, b, t1, b') ->
  (&&) ((&&) (noccur_between k n b) (noccur_between k n t1))
    (noccur_between (S k) n b')
| Coq_tApp (u, v) ->
  (&&) (noccur_between k n u) (forallb (noccur_between k n) v)
| Coq_tCase (_, p, c, brs) ->
  let k' = add (Datatypes.length p.pcontext) k in
  let p' =
    test_predicate (fun _ -> true) (noccur_between k n) (noccur_between k' n)
      p
  in
  let brs' =
    forallb (fun b ->
      test_branch
        (let k0 = add (Datatypes.length b.bcontext) k in noccur_between k0 n)
        b) brs
  in
  (&&) ((&&) p' (noccur_between k n c)) brs'
| Coq_tProj (_, c) -> noccur_between k n c
| Coq_tFix (mfix, _) ->
  let k' = add (Datatypes.length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = add (Datatypes.length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| Coq_tArray (_, arr, def, ty) ->
  (&&) ((&&) (forallb (noccur_between k n) arr) (noccur_between k n def))
    (noccur_between k n ty)
| _ -> true

(** val subst_instance_constr : term coq_UnivSubst **)

let rec subst_instance_constr u c = match c with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst_instance_constr u) args))
| Coq_tSort s -> Coq_tSort (subst_instance_sort u s)
| Coq_tCast (c0, kind, ty) ->
  Coq_tCast ((subst_instance_constr u c0), kind, (subst_instance_constr u ty))
| Coq_tProd (na, a, b) ->
  Coq_tProd (na, (subst_instance_constr u a), (subst_instance_constr u b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst_instance_constr u t0), (subst_instance_constr u m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst_instance_constr u b), (subst_instance_constr u ty),
    (subst_instance_constr u b'))
| Coq_tApp (f, v) ->
  Coq_tApp ((subst_instance_constr u f), (map (subst_instance_constr u) v))
| Coq_tConst (c0, u') -> Coq_tConst (c0, (subst_instance_instance u u'))
| Coq_tInd (i, u') -> Coq_tInd (i, (subst_instance_instance u u'))
| Coq_tConstruct (ind, k, u') ->
  Coq_tConstruct (ind, k, (subst_instance_instance u u'))
| Coq_tCase (ind, p, c0, brs) ->
  let p' =
    map_predicate (subst_instance_instance u) (subst_instance_constr u)
      (subst_instance_constr u) p
  in
  let brs' = map (map_branch (subst_instance_constr u)) brs in
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
| Coq_tArray (u', arr, def, ty) ->
  Coq_tArray ((subst_instance_level u u'),
    (map (subst_instance_constr u) arr), (subst_instance_constr u def),
    (subst_instance_constr u ty))
| _ -> c

module TemplateTerm =
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

module Env = Environment.Environment(TemplateTerm)

(** val inds :
    kername -> Instance.t -> Env.one_inductive_body list -> term list **)

let inds ind u l =
  let rec aux = function
  | O -> []
  | S n0 ->
    (Coq_tInd ({ inductive_mind = ind; inductive_ind = n0 }, u)) :: (aux n0)
  in aux (Datatypes.length l)

(** val lookup_minductive_gen :
    (kername -> Env.global_decl option) -> kername ->
    Env.mutual_inductive_body option **)

let lookup_minductive_gen lookup mind =
  match lookup mind with
  | Some g ->
    (match g with
     | Env.ConstantDecl _ -> None
     | Env.InductiveDecl decl -> Some decl)
  | None -> None

(** val lookup_inductive_gen :
    (kername -> Env.global_decl option) -> inductive ->
    (Env.mutual_inductive_body * Env.one_inductive_body) option **)

let lookup_inductive_gen lookup ind =
  match lookup_minductive_gen lookup ind.inductive_mind with
  | Some mdecl ->
    (match nth_error (Env.ind_bodies mdecl) ind.inductive_ind with
     | Some idecl -> Some (mdecl, idecl)
     | None -> None)
  | None -> None

(** val lookup_inductive :
    Env.global_env -> inductive ->
    (Env.mutual_inductive_body * Env.one_inductive_body) option **)

let lookup_inductive _UU03a3_ =
  lookup_inductive_gen (Env.lookup_env _UU03a3_)
