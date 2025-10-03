open BasicAst
open BinInt
open BinNums
open BinPos
open Bool
open Byte
open Classes0
open Datatypes
open EqDecInstances
open Int0
open Kernames
open List0
open MCList
open MCPrelude
open MCString
open MSetAVL
open MSetList
open MSetProperties
open Nat0
open PeanoNat
open ReflectEq
open Bytestring

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type valuation = { valuation_mono : (String.t -> positive);
                   valuation_poly : (nat -> nat) }

type 'a coq_Evaluable = valuation -> 'a -> nat

(** val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> nat **)

let coq_val evaluable =
  evaluable

module Level =
 struct
  type t_ =
  | Coq_lzero
  | Coq_level of String.t
  | Coq_lvar of nat

  (** val t__rect : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 = function
  | Coq_lzero -> f
  | Coq_level t1 -> f0 t1
  | Coq_lvar n -> f1 n

  (** val t__rec : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 = function
  | Coq_lzero -> f
  | Coq_level t1 -> f0 t1
  | Coq_lvar n -> f1 n

  (** val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t_ =
    Build_NoConfusionPackage

  type t = t_

  (** val is_set : t -> bool **)

  let is_set = function
  | Coq_lzero -> true
  | _ -> false

  (** val is_var : t -> bool **)

  let is_var = function
  | Coq_lvar _ -> true
  | _ -> false

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v = function
  | Coq_lzero -> O
  | Coq_level s -> Pos.to_nat (v.valuation_mono s)
  | Coq_lvar x -> v.valuation_poly x

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lzero -> (match l2 with
                    | Coq_lzero -> Eq
                    | _ -> Lt)
    | Coq_level s1 ->
      (match l2 with
       | Coq_lzero -> Gt
       | Coq_level s2 -> StringOT.compare s1 s2
       | Coq_lvar _ -> Lt)
    | Coq_lvar n -> (match l2 with
                     | Coq_lvar m -> Nat.compare n m
                     | _ -> Gt)

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature x x0 =
    (x,x0),__

  (** val eq_level : t_ -> t_ -> bool **)

  let eq_level l1 l2 =
    match l1 with
    | Coq_lzero -> (match l2 with
                    | Coq_lzero -> true
                    | _ -> false)
    | Coq_level s1 ->
      (match l2 with
       | Coq_level s2 -> IdentOT.reflect_eq_string s1 s2
       | _ -> false)
    | Coq_lvar n1 ->
      (match l2 with
       | Coq_lvar n2 -> reflect_nat n1 n2
       | _ -> false)

  (** val reflect_level : t coq_ReflectEq **)

  let reflect_level =
    eq_level

  (** val eqb : t_ -> t_ -> bool **)

  let eqb =
    eq_level

  (** val eqb_spec : t -> t -> reflect **)

  let eqb_spec l l' =
    reflectProp_reflect (eqb l l')

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_level)
 end

module LevelSet = Make(Level)

module LevelSetOrdProp = OrdProperties(LevelSet)

module LevelSetProp = LevelSetOrdProp.P

module LevelExpr =
 struct
  type t = Level.t * nat

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v l =
    add (snd l) (coq_val Level.coq_Evaluable v (fst l))

  (** val succ : t -> Level.t * nat **)

  let succ l =
    ((fst l), (S (snd l)))

  (** val get_level : t -> Level.t **)

  let get_level =
    fst

  (** val get_noprop : t -> Level.t option **)

  let get_noprop e =
    Some (fst e)

  (** val is_level : t -> bool **)

  let is_level = function
  | (_, n) -> (match n with
               | O -> true
               | S _ -> false)

  (** val make : Level.t -> t **)

  let make l =
    (l, O)

  (** val set : t **)

  let set =
    (Level.Coq_lzero, O)

  (** val type1 : t **)

  let type1 =
    (Level.Coq_lzero, (S O))

  (** val compare : t -> t -> comparison **)

  let compare x y =
    let (l1, b1) = x in
    let (l2, b2) = y in
    (match Level.compare l1 l2 with
     | Eq -> Nat.compare b1 b2
     | x0 -> x0)

  (** val reflect_t : t coq_ReflectEq **)

  let reflect_t =
    reflect_prod Level.reflect_level reflect_nat

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_t)
 end

module LevelExprSet = MakeWithLeibniz(LevelExpr)

type nonEmptyLevelExprSet =
  LevelExprSet.t
  (* singleton inductive, whose constructor was Build_nonEmptyLevelExprSet *)

module NonEmptySetFacts =
 struct
  (** val singleton : LevelExpr.t -> nonEmptyLevelExprSet **)

  let singleton =
    LevelExprSet.singleton

  (** val add :
      LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let add =
    LevelExprSet.add

  (** val add_list :
      LevelExpr.t list -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let add_list =
    fold_left (fun u e -> add e u)

  (** val to_nonempty_list :
      nonEmptyLevelExprSet -> LevelExpr.t * LevelExpr.t list **)

  let to_nonempty_list u =
    let filtered_var = LevelExprSet.elements u in
    (match filtered_var with
     | [] -> assert false (* absurd case *)
     | e :: l -> (e, l))

  (** val map :
      (LevelExpr.t -> LevelExpr.t) -> nonEmptyLevelExprSet ->
      nonEmptyLevelExprSet **)

  let map f u =
    let (e, l) = to_nonempty_list u in add_list (map f l) (singleton (f e))

  (** val non_empty_union :
      nonEmptyLevelExprSet -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let non_empty_union =
    LevelExprSet.union
 end

module Universe =
 struct
  type t = nonEmptyLevelExprSet

  (** val make : LevelExpr.t -> t **)

  let make =
    NonEmptySetFacts.singleton

  (** val succ : t -> t **)

  let succ =
    NonEmptySetFacts.map LevelExpr.succ

  (** val sup : t -> t -> t **)

  let sup =
    NonEmptySetFacts.non_empty_union
 end

module ConstraintType =
 struct
  type t_ =
  | Le of coq_Z
  | Eq

  (** val t__rect : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1 **)

  let t__rect f f0 = function
  | Le z -> f z
  | Eq -> f0

  (** val t__rec : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1 **)

  let t__rec f f0 = function
  | Le z -> f z
  | Eq -> f0

  (** val t__eqdec : t_ -> t_ -> t_ dec_eq **)

  let t__eqdec x y =
    match x with
    | Le z ->
      (match y with
       | Le z0 -> eq_dec_point z (coq_EqDec_EqDecPoint coq_Z_EqDec z) z0
       | Eq -> false)
    | Eq -> (match y with
             | Le _ -> false
             | Eq -> true)

  (** val t__EqDec : t_ coq_EqDec **)

  let t__EqDec =
    t__eqdec

  type t = t_

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Le n -> (match y with
               | Le m -> Z.compare n m
               | Eq -> Lt)
    | Eq -> (match y with
             | Le _ -> Gt
             | Eq -> Datatypes.Eq)
 end

module UnivConstraint =
 struct
  type t = (Level.t * ConstraintType.t) * Level.t

  (** val make : Level.t -> ConstraintType.t -> Level.t -> t **)

  let make l1 ct l2 =
    ((l1, ct), l2)

  (** val compare : t -> t -> comparison **)

  let compare pat pat0 =
    let (p, l2) = pat in
    let (l1, t0) = p in
    let (p0, l2') = pat0 in
    let (l1', t') = p0 in
    (match Level.compare l1 l1' with
     | Eq ->
       (match ConstraintType.compare t0 t' with
        | Eq -> Level.compare l2 l2'
        | x -> x)
     | x -> x)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let (a, b) = x in
    let (p, t0) = y in
    if eq_dec
         (prod_eqdec (coq_ReflectEq_EqDec Level.reflect_level)
           ConstraintType.t__EqDec) a p
    then eq_dec (coq_ReflectEq_EqDec Level.reflect_level) b t0
    else false
 end

module ConstraintSet = Make(UnivConstraint)

module Instance =
 struct
  type t = Level.t list

  (** val empty : t **)

  let empty =
    []
 end

module UContext =
 struct
  type t = name list * (Instance.t * ConstraintSet.t)

  (** val instance : t -> Instance.t **)

  let instance x =
    fst (snd x)
 end

module AUContext =
 struct
  type t = name list * ConstraintSet.t

  (** val repr : t -> UContext.t **)

  let repr = function
  | (u, cst) -> (u, ((mapi (fun i _ -> Level.Coq_lvar i) u), cst))

  (** val levels : t -> LevelSet.t **)

  let levels uctx =
    LevelSetProp.of_list (fst (snd (repr uctx)))
 end

module ContextSet =
 struct
  type t = LevelSet.t * ConstraintSet.t

  (** val levels : t -> LevelSet.t **)

  let levels =
    fst

  (** val constraints : t -> ConstraintSet.t **)

  let constraints =
    snd

  (** val empty : t **)

  let empty =
    (LevelSet.empty, ConstraintSet.empty)

  (** val union : t -> t -> t **)

  let union x y =
    ((LevelSet.union (levels x) (levels y)),
      (ConstraintSet.union (constraints x) (constraints y)))
 end

module Variance =
 struct
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

type universes_decl =
| Monomorphic_ctx
| Polymorphic_ctx of AUContext.t

(** val levels_of_udecl : universes_decl -> LevelSet.t **)

let levels_of_udecl = function
| Monomorphic_ctx -> LevelSet.empty
| Polymorphic_ctx ctx -> AUContext.levels ctx

(** val constraints_of_udecl : universes_decl -> ConstraintSet.t **)

let constraints_of_udecl = function
| Monomorphic_ctx -> ConstraintSet.empty
| Polymorphic_ctx ctx -> snd (snd (AUContext.repr ctx))

module Sort =
 struct
  type 'univ t_ =
  | Coq_sProp
  | Coq_sSProp
  | Coq_sType of 'univ

  type t = Universe.t t_

  type family =
  | Coq_fSProp
  | Coq_fProp
  | Coq_fType

  (** val is_prop : 'a1 t_ -> bool **)

  let is_prop = function
  | Coq_sProp -> true
  | _ -> false

  (** val is_propositional : 'a1 t_ -> bool **)

  let is_propositional = function
  | Coq_sType _ -> false
  | _ -> true

  (** val type0 : t **)

  let type0 =
    Coq_sType (Universe.make LevelExpr.set)

  (** val super_ : 'a1 -> ('a1 -> 'a1) -> 'a1 t_ -> 'a1 t_ **)

  let super_ type2 univ_succ = function
  | Coq_sType l -> Coq_sType (univ_succ l)
  | _ -> Coq_sType type2

  (** val super : t -> t **)

  let super =
    super_ (Universe.make LevelExpr.type1) Universe.succ

  (** val sup_ : ('a1 -> 'a1 -> 'a1) -> 'a1 t_ -> 'a1 t_ -> 'a1 t_ **)

  let sup_ univ_sup s s' =
    match s with
    | Coq_sProp -> (match s' with
                    | Coq_sSProp -> Coq_sProp
                    | _ -> s')
    | Coq_sSProp -> s'
    | Coq_sType u1 ->
      (match s' with
       | Coq_sType u2 -> Coq_sType (univ_sup u1 u2)
       | _ -> s)

  (** val sort_of_product_ :
      ('a1 -> 'a1 -> 'a1) -> 'a1 t_ -> 'a1 t_ -> 'a1 t_ **)

  let sort_of_product_ univ_sup domsort rangsort = match rangsort with
  | Coq_sType _ -> sup_ univ_sup domsort rangsort
  | _ -> rangsort

  (** val sort_of_product : t -> t -> t **)

  let sort_of_product =
    sort_of_product_ Universe.sup

  (** val to_family : 'a1 t_ -> family **)

  let to_family = function
  | Coq_sProp -> Coq_fProp
  | Coq_sSProp -> Coq_fSProp
  | Coq_sType _ -> Coq_fType
 end

type allowed_eliminations =
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

(** val subst_instance : 'a1 coq_UnivSubst -> Instance.t -> 'a1 -> 'a1 **)

let subst_instance univSubst =
  univSubst

(** val subst_instance_level : Level.t coq_UnivSubst **)

let subst_instance_level u l = match l with
| Level.Coq_lvar n -> nth n u Level.Coq_lzero
| _ -> l

(** val subst_instance_level_expr : LevelExpr.t coq_UnivSubst **)

let subst_instance_level_expr u e = match e with
| (t0, b) ->
  (match t0 with
   | Level.Coq_lvar n ->
     (match nth_error u n with
      | Some l -> (l, b)
      | None -> (Level.Coq_lzero, b))
   | _ -> e)

(** val subst_instance_universe : Universe.t coq_UnivSubst **)

let subst_instance_universe u =
  NonEmptySetFacts.map (subst_instance_level_expr u)

(** val subst_instance_sort : Sort.t coq_UnivSubst **)

let subst_instance_sort u e = match e with
| Sort.Coq_sType u' ->
  Sort.Coq_sType (subst_instance subst_instance_universe u u')
| _ -> e

(** val subst_instance_instance : Instance.t coq_UnivSubst **)

let subst_instance_instance u u' =
  map (subst_instance_level u) u'

(** val closedu_level : nat -> Level.t -> bool **)

let closedu_level k = function
| Level.Coq_lvar n -> Nat.ltb n k
| _ -> true

(** val closedu_level_expr : nat -> LevelExpr.t -> bool **)

let closedu_level_expr k s =
  closedu_level k (LevelExpr.get_level s)

(** val closedu_universe : nat -> Universe.t -> bool **)

let closedu_universe k u =
  LevelExprSet.for_all (closedu_level_expr k) u

(** val closedu_sort : nat -> Sort.t -> bool **)

let closedu_sort k = function
| Sort.Coq_sType l -> closedu_universe k l
| _ -> true

(** val closedu_instance : nat -> Instance.t -> bool **)

let closedu_instance k u =
  forallb (closedu_level k) u

(** val string_of_level : Level.t -> String.t **)

let string_of_level = function
| Level.Coq_lzero ->
  String.String (Coq_x53, (String.String (Coq_x65, (String.String (Coq_x74,
    String.EmptyString)))))
| Level.Coq_level s -> s
| Level.Coq_lvar n ->
  String.append (String.String (Coq_x6c, (String.String (Coq_x76,
    (String.String (Coq_x61, (String.String (Coq_x72,
    String.EmptyString)))))))) (string_of_nat n)

(** val string_of_universe_instance : Level.t list -> String.t **)

let string_of_universe_instance u =
  string_of_list string_of_level u

(** val abstract_instance : universes_decl -> Instance.t **)

let abstract_instance = function
| Monomorphic_ctx -> Instance.empty
| Polymorphic_ctx auctx -> UContext.instance (AUContext.repr auctx)
