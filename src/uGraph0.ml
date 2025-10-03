open BinInt
open BinNums
open BinPos
open Bool
open Classes0
open Datatypes
open EqDecInstances
open Int0
open Kernames
open MSetAVL
open PeanoNat
open ReflectEq
open Signature
open Specif
open Universes0
open Bytestring
open Config0
open Monad_utils
open WGraph

type __ = Obj.t

module VariableLevel =
 struct
  type t_ =
  | Coq_level of String.t
  | Coq_lvar of nat

  type t = t_

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Coq_level s0 ->
      (match y with
       | Coq_level s' -> StringOT.compare s0 s'
       | Coq_lvar _ -> Lt)
    | Coq_lvar n ->
      (match y with
       | Coq_level _ -> Gt
       | Coq_lvar n' -> Nat.compare n n')

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | Coq_level t0 ->
      (match y with
       | Coq_level t1 ->
         eq_dec (coq_ReflectEq_EqDec IdentOT.reflect_eq_string) t0 t1
       | Coq_lvar _ -> false)
    | Coq_lvar n ->
      (match y with
       | Coq_level _ -> false
       | Coq_lvar n0 -> Nat.eq_dec n n0)

  (** val to_noprop : t -> Level.t **)

  let to_noprop = function
  | Coq_level s0 -> Level.Coq_level s0
  | Coq_lvar n -> Level.Coq_lvar n

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v = function
  | Coq_level s0 -> Pos.to_nat (v.valuation_mono s0)
  | Coq_lvar x -> v.valuation_poly x
 end

module GoodConstraint =
 struct
  type t_ =
  | Coq_gc_le of VariableLevel.t * coq_Z * VariableLevel.t
  | Coq_gc_lt_set_level of nat * String.t
  | Coq_gc_le_set_var of nat * nat
  | Coq_gc_le_level_set of String.t * nat
  | Coq_gc_le_var_set of nat * nat

  (** val t__rect :
      (VariableLevel.t -> coq_Z -> VariableLevel.t -> 'a1) -> (nat ->
      String.t -> 'a1) -> (nat -> nat -> 'a1) -> (String.t -> nat -> 'a1) ->
      (nat -> nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 f2 f3 = function
  | Coq_gc_le (t1, z, t2) -> f t1 z t2
  | Coq_gc_lt_set_level (n, t1) -> f0 n t1
  | Coq_gc_le_set_var (n, n0) -> f1 n n0
  | Coq_gc_le_level_set (t1, n) -> f2 t1 n
  | Coq_gc_le_var_set (n, n0) -> f3 n n0

  (** val t__rec :
      (VariableLevel.t -> coq_Z -> VariableLevel.t -> 'a1) -> (nat ->
      String.t -> 'a1) -> (nat -> nat -> 'a1) -> (String.t -> nat -> 'a1) ->
      (nat -> nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 f2 f3 = function
  | Coq_gc_le (t1, z, t2) -> f t1 z t2
  | Coq_gc_lt_set_level (n, t1) -> f0 n t1
  | Coq_gc_le_set_var (n, n0) -> f1 n n0
  | Coq_gc_le_level_set (t1, n) -> f2 t1 n
  | Coq_gc_le_var_set (n, n0) -> f3 n n0

  (** val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t_ =
    Build_NoConfusionPackage

  type t = t_

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | Coq_gc_le (t0, z, t1) ->
      (match y with
       | Coq_gc_le (t2, z0, t3) ->
         if VariableLevel.eq_dec t0 t2
         then if Z.eq_dec z z0 then VariableLevel.eq_dec t1 t3 else false
         else false
       | _ -> false)
    | Coq_gc_lt_set_level (n, t0) ->
      (match y with
       | Coq_gc_lt_set_level (n0, t1) ->
         if eq_dec nat_EqDec n n0
         then eq_dec (coq_ReflectEq_EqDec IdentOT.reflect_eq_string) t0 t1
         else false
       | _ -> false)
    | Coq_gc_le_set_var (n, n0) ->
      (match y with
       | Coq_gc_le_set_var (n1, n2) ->
         if eq_dec nat_EqDec n n1 then eq_dec nat_EqDec n0 n2 else false
       | _ -> false)
    | Coq_gc_le_level_set (t0, n) ->
      (match y with
       | Coq_gc_le_level_set (t1, n0) ->
         if eq_dec (coq_ReflectEq_EqDec IdentOT.reflect_eq_string) t0 t1
         then eq_dec nat_EqDec n n0
         else false
       | _ -> false)
    | Coq_gc_le_var_set (n, n0) ->
      (match y with
       | Coq_gc_le_var_set (n1, n2) ->
         if eq_dec nat_EqDec n n1 then eq_dec nat_EqDec n0 n2 else false
       | _ -> false)

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Coq_gc_le (u, n, v) ->
      (match y with
       | Coq_gc_le (u', n', v') ->
         (match VariableLevel.compare u u' with
          | Eq ->
            (match Z.compare n n' with
             | Eq -> VariableLevel.compare v v'
             | x0 -> x0)
          | x0 -> x0)
       | _ -> Gt)
    | Coq_gc_lt_set_level (n, s0) ->
      (match y with
       | Coq_gc_le (_, _, _) -> Lt
       | Coq_gc_lt_set_level (n', s') ->
         (match Nat.compare n n' with
          | Eq -> StringOT.compare s0 s'
          | x0 -> x0)
       | _ -> Gt)
    | Coq_gc_le_set_var (n, s0) ->
      (match y with
       | Coq_gc_le (_, _, _) -> Lt
       | Coq_gc_lt_set_level (_, _) -> Lt
       | Coq_gc_le_set_var (n', s') ->
         (match Nat.compare n n' with
          | Eq -> Nat.compare s0 s'
          | x0 -> x0)
       | _ -> Gt)
    | Coq_gc_le_level_set (s0, n) ->
      (match y with
       | Coq_gc_le_level_set (s', n') ->
         (match Nat.compare n n' with
          | Eq -> StringOT.compare s0 s'
          | x0 -> x0)
       | Coq_gc_le_var_set (_, _) -> Gt
       | _ -> Lt)
    | Coq_gc_le_var_set (n, k) ->
      (match y with
       | Coq_gc_le_var_set (n', k') ->
         (match Nat.compare n n' with
          | Eq -> Nat.compare k k'
          | x0 -> x0)
       | _ -> Lt)

  (** val satisfies : valuation -> t -> bool **)

  let satisfies v = function
  | Coq_gc_le (l, z, l'0) ->
    Z.leb (Z.of_nat (coq_val VariableLevel.coq_Evaluable v l))
      (Z.sub (Z.of_nat (coq_val VariableLevel.coq_Evaluable v l'0)) z)
  | Coq_gc_lt_set_level (k, l) -> Nat.ltb k (Pos.to_nat (v.valuation_mono l))
  | Coq_gc_le_set_var (k, l) -> Nat.leb k (v.valuation_poly l)
  | Coq_gc_le_level_set (l, k) -> Nat.leb (Pos.to_nat (v.valuation_mono l)) k
  | Coq_gc_le_var_set (l, k) -> Nat.leb (v.valuation_poly l) k
 end

module GoodConstraintSet = Make(GoodConstraint)

(** val coq_GoodConstraintSet_pair :
    GoodConstraintSet.elt -> GoodConstraintSet.elt -> GoodConstraintSet.t **)

let coq_GoodConstraintSet_pair x y =
  GoodConstraintSet.add y (GoodConstraintSet.singleton x)

(** val gc_of_constraint :
    checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option **)

let gc_of_constraint _ uc =
  let empty0 = Some GoodConstraintSet.empty in
  let singleton0 = fun x -> Some (GoodConstraintSet.singleton x) in
  let pair = fun x y -> Some (coq_GoodConstraintSet_pair x y) in
  let (p, r0) = uc in
  let (t0, t1) = p in
  (match t0 with
   | Level.Coq_lzero ->
     (match t1 with
      | ConstraintType.Le z ->
        (match Z.compare z Z0 with
         | Gt ->
           (match r0 with
            | Level.Coq_lzero -> None
            | Level.Coq_level s0 ->
              singleton0 (GoodConstraint.Coq_gc_lt_set_level
                ((Z.to_nat (Z.sub z (Zpos Coq_xH))), s0))
            | Level.Coq_lvar n ->
              singleton0 (GoodConstraint.Coq_gc_le_set_var ((Z.to_nat z), n)))
         | _ -> empty0)
      | ConstraintType.Eq ->
        (match r0 with
         | Level.Coq_lzero -> empty0
         | Level.Coq_level _ -> None
         | Level.Coq_lvar n ->
           singleton0 (GoodConstraint.Coq_gc_le_var_set (n, O))))
   | Level.Coq_level l ->
     (match t1 with
      | ConstraintType.Le z ->
        (match r0 with
         | Level.Coq_lzero ->
           if Z.leb z Z0
           then singleton0 (GoodConstraint.Coq_gc_le_level_set (l,
                  (Z.to_nat (Z.abs z))))
           else None
         | Level.Coq_level l'0 ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_level l),
             z, (VariableLevel.Coq_level l'0)))
         | Level.Coq_lvar n ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_level l),
             z, (VariableLevel.Coq_lvar n))))
      | ConstraintType.Eq ->
        (match r0 with
         | Level.Coq_lzero -> None
         | Level.Coq_level l'0 ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_level l), Z0,
             (VariableLevel.Coq_level l'0))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Coq_level l'0), Z0, (VariableLevel.Coq_level l)))
         | Level.Coq_lvar n ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_level l), Z0,
             (VariableLevel.Coq_lvar n))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Coq_lvar n), Z0, (VariableLevel.Coq_level l)))))
   | Level.Coq_lvar n ->
     (match t1 with
      | ConstraintType.Le z ->
        (match r0 with
         | Level.Coq_lzero ->
           if Z.leb z Z0
           then singleton0 (GoodConstraint.Coq_gc_le_var_set (n,
                  (Z.to_nat (Z.abs z))))
           else None
         | Level.Coq_level l ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_lvar n),
             z, (VariableLevel.Coq_level l)))
         | Level.Coq_lvar n' ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_lvar n),
             z, (VariableLevel.Coq_lvar n'))))
      | ConstraintType.Eq ->
        (match r0 with
         | Level.Coq_lzero ->
           singleton0 (GoodConstraint.Coq_gc_le_var_set (n, O))
         | Level.Coq_level l ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_lvar n), Z0,
             (VariableLevel.Coq_level l))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Coq_level l), Z0, (VariableLevel.Coq_lvar n)))
         | Level.Coq_lvar n' ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Coq_lvar n), Z0,
             (VariableLevel.Coq_lvar n'))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Coq_lvar n'), Z0, (VariableLevel.Coq_lvar n))))))

(** val add_gc_of_constraint :
    checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option ->
    GoodConstraintSet.t option **)

let add_gc_of_constraint cf uc s0 =
  bind (Obj.magic option_monad) s0 (fun s1 ->
    bind (Obj.magic option_monad) (gc_of_constraint cf uc) (fun s2 ->
      ret (Obj.magic option_monad) (GoodConstraintSet.union s1 s2)))

(** val gc_of_constraints :
    checker_flags -> ConstraintSet.t -> GoodConstraintSet.t option **)

let gc_of_constraints cf ctrs =
  ConstraintSet.fold (add_gc_of_constraint cf) ctrs (Some
    GoodConstraintSet.empty)

module Coq_wGraph = WeightedGraph(Level)(LevelSet)

module VSet = LevelSet

type universes_graph = Coq_wGraph.t

(** val edge_of_level : VariableLevel.t -> Coq_wGraph.EdgeSet.elt **)

let edge_of_level = function
| VariableLevel.Coq_level l0 ->
  ((Level.Coq_lzero, (Zpos Coq_xH)), (Level.Coq_level l0))
| VariableLevel.Coq_lvar n -> ((Level.Coq_lzero, Z0), (Level.Coq_lvar n))

(** val edge_of_constraint : GoodConstraint.t -> Coq_wGraph.EdgeSet.elt **)

let edge_of_constraint = function
| GoodConstraint.Coq_gc_le (l, z, l'0) ->
  (((VariableLevel.to_noprop l), z), (VariableLevel.to_noprop l'0))
| GoodConstraint.Coq_gc_lt_set_level (k, s0) ->
  ((Level.Coq_lzero, (Z.of_nat (S k))),
    (VariableLevel.to_noprop (VariableLevel.Coq_level s0)))
| GoodConstraint.Coq_gc_le_set_var (k, n) ->
  ((Level.Coq_lzero, (Z.of_nat k)),
    (VariableLevel.to_noprop (VariableLevel.Coq_lvar n)))
| GoodConstraint.Coq_gc_le_level_set (s0, k) ->
  (((VariableLevel.to_noprop (VariableLevel.Coq_level s0)),
    (Z.opp (Z.of_nat k))), Level.Coq_lzero)
| GoodConstraint.Coq_gc_le_var_set (n, k) ->
  (((VariableLevel.to_noprop (VariableLevel.Coq_lvar n)),
    (Z.opp (Z.of_nat k))), Level.Coq_lzero)

(** val variable_of_level : Level.t -> VariableLevel.t option **)

let variable_of_level = function
| Level.Coq_lzero -> None
| Level.Coq_level s0 -> Some (VariableLevel.Coq_level s0)
| Level.Coq_lvar n -> Some (VariableLevel.Coq_lvar n)

(** val add_level_edges :
    VSet.t -> Coq_wGraph.EdgeSet.t -> Coq_wGraph.EdgeSet.t **)

let add_level_edges =
  VSet.fold (fun l e ->
    match variable_of_level l with
    | Some ll -> Coq_wGraph.EdgeSet.add (edge_of_level ll) e
    | None -> e)

(** val add_cstrs :
    GoodConstraintSet.t -> Coq_wGraph.EdgeSet.t -> Coq_wGraph.EdgeSet.t **)

let add_cstrs ctrs =
  GoodConstraintSet.fold (fun ctr ->
    Coq_wGraph.EdgeSet.add (edge_of_constraint ctr)) ctrs

(** val make_graph : (VSet.t * GoodConstraintSet.t) -> Coq_wGraph.t **)

let make_graph uctx =
  let init_edges = add_level_edges (fst uctx) Coq_wGraph.EdgeSet.empty in
  let edges = add_cstrs (snd uctx) init_edges in
  (((fst uctx), edges), Level.Coq_lzero)

(** val leqb_level_n :
    universes_graph -> coq_Z -> Level.t -> Level.t -> bool **)

let leqb_level_n =
  Coq_wGraph.leqb_vertices

(** val add_uctx :
    (VSet.t * GoodConstraintSet.t) -> universes_graph -> universes_graph **)

let add_uctx uctx g =
  let levels = VSet.union (fst uctx) (fst (fst g)) in
  let edges = add_level_edges (fst uctx) (snd (fst g)) in
  let edges0 = add_cstrs (snd uctx) edges in ((levels, edges0), (snd g))
