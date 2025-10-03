open BinInt
open BinNums
open BinPos
open Bool
open Classes0
open Datatypes
open Int0
open List0
open MSetAVL
open MSetDecide
open MSetFacts
open MSetInterface
open MSetProperties
open Nat0
open Orders
open PeanoNat
open ReflectEq
open Signature
open Specif
open Ssrbool

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Nbar =
 struct
  type t = coq_Z option

  (** val max : t -> t -> t **)

  let max n m =
    match n with
    | Some n0 ->
      (match m with
       | Some m0 -> Some (Z.max n0 m0)
       | None -> Some n0)
    | None -> m

  (** val add : t -> t -> t **)

  let add n m =
    match n with
    | Some n0 -> (match m with
                  | Some m0 -> Some (Z.add n0 m0)
                  | None -> None)
    | None -> None

  (** val le_dec : t -> t -> bool **)

  let le_dec n m =
    match n with
    | Some z ->
      (match m with
       | Some z0 ->
         let c = Z.compare z z0 in (match c with
                                    | Gt -> false
                                    | _ -> true)
       | None -> false)
    | None -> true
 end

module WeightedGraph =
 functor (V:UsualOrderedType) ->
 functor (VSet:S with module E = V) ->
 struct
  module VSetFact = WFactsOn(V)(VSet)

  module VSetProp = WPropertiesOn(V)(VSet)

  module VSetDecide = WDecide(VSet)

  module Edge =
   struct
    type t = (V.t * coq_Z) * V.t

    (** val compare : t -> t -> comparison **)

    let compare pat pat0 =
      let (p, y) = pat in
      let (x, n) = p in
      let (p0, y') = pat0 in
      let (x', n') = p0 in
      (match V.compare x x' with
       | Eq -> (match Z.compare n n' with
                | Eq -> V.compare y y'
                | x0 -> x0)
       | x0 -> x0)

    (** val eq_dec : t -> t -> bool **)

    let eq_dec x y =
      let (a, b) = x in
      let (p, t0) = y in
      if let (a0, b0) = a in
         let (t1, z) = p in if V.eq_dec a0 t1 then Z.eq_dec b0 z else false
      then V.eq_dec b t0
      else false

    (** val eqb : t -> t -> bool **)

    let eqb x y =
      match compare x y with
      | Eq -> true
      | _ -> false
   end

  module EdgeSet = Make(Edge)

  module EdgeSetFact = WFactsOn(Edge)(EdgeSet)

  module EdgeSetProp = WPropertiesOn(Edge)(EdgeSet)

  module EdgeSetDecide = WDecide(EdgeSet)

  type t = (VSet.t * EdgeSet.t) * V.t

  (** val coq_V : t -> VSet.t **)

  let coq_V g =
    fst (fst g)

  (** val coq_E : t -> EdgeSet.t **)

  let coq_E g =
    snd (fst g)

  (** val s : t -> V.t **)

  let s =
    snd

  (** val e_source : Edge.t -> V.t **)

  let e_source x =
    fst (fst x)

  (** val e_target : Edge.t -> V.t **)

  let e_target =
    snd

  (** val e_weight : Edge.t -> coq_Z **)

  let e_weight x =
    snd (fst x)

  (** val opp_edge : Edge.t -> Edge.t **)

  let opp_edge e =
    (((e_target e), (Z.opp (e_weight e))), (e_source e))

  type labelling = V.t -> nat

  (** val add_node : t -> VSet.elt -> t **)

  let add_node g x =
    (((VSet.add x (coq_V g)), (coq_E g)), (s g))

  (** val add_edge : t -> Edge.t -> t **)

  let add_edge g e =
    (((VSet.add (e_source e) (VSet.add (e_target e) (coq_V g))),
      (EdgeSet.add e (coq_E g))), (s g))

  type coq_EdgeOf = (coq_Z, __) sigT

  type coq_PathOf =
  | Coq_pathOf_refl of V.t
  | Coq_pathOf_step of V.t * V.t * V.t * coq_EdgeOf * coq_PathOf

  (** val coq_PathOf_rect :
      t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf ->
      'a1 -> 'a1) -> V.t -> V.t -> coq_PathOf -> 'a1 **)

  let rec coq_PathOf_rect g f f0 _ _ = function
  | Coq_pathOf_refl x -> f x
  | Coq_pathOf_step (x, y, z, e, p0) ->
    f0 x y z e p0 (coq_PathOf_rect g f f0 y z p0)

  (** val coq_PathOf_rec :
      t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf ->
      'a1 -> 'a1) -> V.t -> V.t -> coq_PathOf -> 'a1 **)

  let rec coq_PathOf_rec g f f0 _ _ = function
  | Coq_pathOf_refl x -> f x
  | Coq_pathOf_step (x, y, z, e, p0) ->
    f0 x y z e p0 (coq_PathOf_rec g f f0 y z p0)

  (** val weight : t -> V.t -> V.t -> coq_PathOf -> coq_Z **)

  let rec weight g _ _ = function
  | Coq_pathOf_refl _ -> Z0
  | Coq_pathOf_step (_, y0, z, e, p0) -> Z.add (projT1 e) (weight g y0 z p0)

  (** val nodes : t -> V.t -> V.t -> coq_PathOf -> VSet.t **)

  let rec nodes g x _ = function
  | Coq_pathOf_refl _ -> VSet.empty
  | Coq_pathOf_step (_, y0, z, _, p0) -> VSet.add x (nodes g y0 z p0)

  (** val concat :
      t -> V.t -> V.t -> V.t -> coq_PathOf -> coq_PathOf -> coq_PathOf **)

  let rec concat g _ _ z p q =
    match p with
    | Coq_pathOf_refl _ -> q
    | Coq_pathOf_step (x0, y0, z0, e, p0) ->
      Coq_pathOf_step (x0, y0, z, e, (concat g y0 z0 z p0 q))

  (** val length : t -> V.t -> V.t -> coq_PathOf -> coq_Z **)

  let rec length g _ _ = function
  | Coq_pathOf_refl _ -> Z0
  | Coq_pathOf_step (_, y0, z, _, p0) -> Z.succ (length g y0 z p0)

  type coq_SPath =
  | Coq_spath_refl of VSet.t * V.t
  | Coq_spath_step of VSet.t * VSet.t * V.t * V.t * V.t * coq_EdgeOf
     * coq_SPath

  (** val coq_SPath_rect :
      t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t
      -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t
      -> coq_SPath -> 'a1 **)

  let rec coq_SPath_rect g f f0 _ _ _ = function
  | Coq_spath_refl (s1, x) -> f s1 x
  | Coq_spath_step (s1, s', x, y, z, e, s2) ->
    f0 s1 s' x y z __ e s2 (coq_SPath_rect g f f0 s1 y z s2)

  (** val coq_SPath_rec :
      t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t
      -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t
      -> coq_SPath -> 'a1 **)

  let rec coq_SPath_rec g f f0 _ _ _ = function
  | Coq_spath_refl (s1, x) -> f s1 x
  | Coq_spath_step (s1, s', x, y, z, e, s2) ->
    f0 s1 s' x y z __ e s2 (coq_SPath_rec g f f0 s1 y z s2)

  type coq_SPath_sig = coq_SPath

  (** val coq_SPath_sig_pack :
      t -> VSet.t -> V.t -> V.t -> coq_SPath ->
      (VSet.t * (V.t * V.t)) * coq_SPath **)

  let coq_SPath_sig_pack _ x x0 x1 sPath_var =
    (x,(x0,x1)),sPath_var

  (** val coq_SPath_Signature :
      t -> VSet.t -> V.t -> V.t -> (coq_SPath, VSet.t * (V.t * V.t),
      coq_SPath_sig) coq_Signature **)

  let coq_SPath_Signature =
    coq_SPath_sig_pack

  (** val coq_NoConfusionPackage_SPath :
      t -> ((VSet.t * (V.t * V.t)) * coq_SPath) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_SPath _ =
    Build_NoConfusionPackage

  (** val to_pathOf : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_PathOf **)

  let rec to_pathOf g _ _ _ = function
  | Coq_spath_refl (_, x) -> Coq_pathOf_refl x
  | Coq_spath_step (s0, _, x0, y0, z, e, p0) ->
    Coq_pathOf_step (x0, y0, z, e, (to_pathOf g s0 y0 z p0))

  (** val sweight : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_Z **)

  let rec sweight g _ _ _ = function
  | Coq_spath_refl (_, _) -> Z0
  | Coq_spath_step (s0, _, _, y0, z, e, p0) ->
    Z.add (projT1 e) (sweight g s0 y0 z p0)

  (** val is_simple : t -> V.t -> V.t -> coq_PathOf -> bool **)

  let rec is_simple g _ _ = function
  | Coq_pathOf_refl _ -> true
  | Coq_pathOf_step (x, y, z, _, p0) ->
    (&&) (negb (VSet.mem x (nodes g y z p0))) (is_simple g y z p0)

  (** val to_simple : t -> V.t -> V.t -> coq_PathOf -> coq_SPath **)

  let rec to_simple g _ _ = function
  | Coq_pathOf_refl x -> Coq_spath_refl ((nodes g x x (Coq_pathOf_refl x)), x)
  | Coq_pathOf_step (x, y, z, e, p0) ->
    Coq_spath_step ((nodes g y z p0),
      (nodes g x z (Coq_pathOf_step (x, y, z, e, p0))), x, y, z, e,
      (to_simple g y z p0))

  (** val add_end :
      t -> VSet.t -> V.t -> V.t -> coq_SPath -> V.t -> coq_EdgeOf -> VSet.t
      -> coq_SPath **)

  let rec add_end g _ _ _ p z e s' =
    match p with
    | Coq_spath_refl (s0, x) ->
      Coq_spath_step (s0, s', x, z, z, e, (Coq_spath_refl (s0, z)))
    | Coq_spath_step (s0, _, x0, y0, z0, e0, p0) ->
      Coq_spath_step ((VSet.add z0 s0), s', x0, y0, z, e0,
        (add_end g s0 y0 z0 p0 z e (VSet.add z0 s0)))

  (** val coq_SPath_sub :
      t -> VSet.t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath **)

  let rec coq_SPath_sub g _ s' _ _ = function
  | Coq_spath_refl (_, x) -> Coq_spath_refl (s', x)
  | Coq_spath_step (s0, _, x, y, z, e, s1) ->
    Coq_spath_step ((VSet.remove x s'), s', x, y, z, e,
      (coq_SPath_sub g s0 (VSet.remove x s') y z s1))

  (** val sconcat :
      t -> VSet.t -> VSet.t -> V.t -> V.t -> V.t -> coq_SPath -> coq_SPath ->
      coq_SPath **)

  let rec sconcat g _ s' _ _ z p x =
    match p with
    | Coq_spath_refl (s0, x0) -> coq_SPath_sub g s' (VSet.union s0 s') x0 z x
    | Coq_spath_step (s0, s1, x0, y, z', e, p0) ->
      Coq_spath_step ((VSet.union s0 s'), (VSet.union s1 s'), x0, y, z, e,
        (sconcat g s0 s' y z' z p0 x))

  (** val snodes : t -> VSet.t -> V.t -> V.t -> coq_SPath -> VSet.t **)

  let rec snodes g _ x _ = function
  | Coq_spath_refl (_, _) -> VSet.empty
  | Coq_spath_step (s0, _, _, y0, z, _, p0) ->
    VSet.add x (snodes g s0 y0 z p0)

  (** val split :
      t -> VSet.t -> V.t -> V.t -> coq_SPath -> VSet.elt -> bool ->
      coq_SPath * coq_SPath **)

  let rec split g _ _ _ p u hu =
    match p with
    | Coq_spath_refl (s0, x) ->
      if hu
      then assert false (* absurd case *)
      else ((Coq_spath_refl ((VSet.remove x s0), x)), (Coq_spath_refl (s0,
             x)))
    | Coq_spath_step (s0, s', x, y, z, e, s1) ->
      let s2 = V.eq_dec x u in
      if s2
      then ((Coq_spath_refl ((VSet.remove u s'), u)), (Coq_spath_step (s0,
             s', u, y, z, e, s1)))
      else let iHp = split g s0 y z s1 u hu in
           ((Coq_spath_step ((VSet.remove u s0), (VSet.remove u s'), x, y, u,
           e, (fst iHp))), (coq_SPath_sub g s0 s' u z (snd iHp)))

  (** val split' :
      t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath * coq_SPath **)

  let split' g s0 x y p =
    split g s0 x y p y false

  (** val spath_one : t -> VSet.t -> VSet.elt -> V.t -> coq_Z -> coq_SPath **)

  let spath_one _ s0 x y k =
    Coq_spath_step ((VSet.remove x s0), s0, x, y, y, (Coq_existT (k, __)),
      (Coq_spath_refl ((VSet.remove x s0), y)))

  (** val simplify :
      t -> VSet.t -> V.t -> V.t -> coq_PathOf -> coq_SPath -> VSet.t -> (V.t,
      coq_SPath) sigT **)

  let rec simplify g s0 _ _ q p s' =
    match q with
    | Coq_pathOf_refl x -> Coq_existT (x, (coq_SPath_sub g s0 s' x x p))
    | Coq_pathOf_step (y, y', z, e, q0) ->
      if VSet.mem y s0
      then let (p1, p2) = split' g s0 z y p in
           if Z.ltb Z0 (sweight g s0 y y p2)
           then Coq_existT (y, (coq_SPath_sub g s0 s' y y p2))
           else simplify g s0 z y' q0
                  (add_end g (VSet.remove y s0) z y p1 y' e s0) s'
      else simplify g (VSet.add y s0) z y' q0
             (add_end g s0 z y p y' e (VSet.add y s0)) s'

  (** val succs : t -> V.t -> (coq_Z * V.t) list **)

  let succs g x =
    let l =
      filter (fun e -> is_left (V.eq_dec (e_source e) x))
        (EdgeSet.elements (coq_E g))
    in
    map (fun e -> ((e_weight e), (e_target e))) l

  (** val lsp00 : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t **)

  let rec lsp00 g fuel s0 x z =
    let base = if is_left (V.eq_dec x z) then Some Z0 else None in
    (match fuel with
     | O -> base
     | S fuel0 ->
       if VSet.mem x s0
       then let ds =
              map (fun pat ->
                let (n, y) = pat in
                Nbar.add (Some n) (lsp00 g fuel0 (VSet.remove x s0) y z))
                (succs g x)
            in
            fold_left Nbar.max ds base
       else base)

  (** val lsp0 : t -> VSet.t -> V.t -> V.t -> Nbar.t **)

  let lsp0 g s0 =
    lsp00 g (VSet.cardinal s0) s0

  (** val lsp00_fast : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t **)

  let rec lsp00_fast g fuel s0 x z =
    let base = if is_left (V.eq_dec x z) then Some Z0 else None in
    (match fuel with
     | O -> base
     | S fuel0 ->
       if VSet.mem x s0
       then let s1 = VSet.remove x s0 in
            EdgeSet.fold (fun pat acc ->
              let (p, tgt) = pat in
              let (src, w) = p in
              if is_left (V.eq_dec src x)
              then Nbar.max acc
                     (Nbar.add (Some w) (lsp00_fast g fuel0 s1 tgt z))
              else acc) (coq_E g) base
       else base)

  (** val lsp_fast : t -> V.t -> V.t -> Nbar.t **)

  let lsp_fast g =
    lsp00_fast g (VSet.cardinal (coq_V g)) (coq_V g)

  (** val lsp : t -> V.t -> V.t -> Nbar.t **)

  let lsp g =
    lsp0 g (coq_V g)

  (** val is_nonpos : coq_Z option -> bool **)

  let is_nonpos = function
  | Some z -> Z.leb z Z0
  | None -> false

  (** val reduce : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath **)

  let rec reduce g _ _ _ = function
  | Coq_spath_refl (_, x) -> Coq_spath_refl (VSet.empty, x)
  | Coq_spath_step (s0, _, x, y, z, e, s1) ->
    Coq_spath_step ((snodes g s0 y z s1), (VSet.add x (snodes g s0 y z s1)),
      x, y, z, e, (reduce g s0 y z s1))

  (** val simplify2 : t -> V.t -> V.t -> coq_PathOf -> coq_SPath **)

  let rec simplify2 g _ _ = function
  | Coq_pathOf_refl x -> Coq_spath_refl (VSet.empty, x)
  | Coq_pathOf_step (x, y, z, e, p0) ->
    let iHp = simplify2 g y z p0 in
    if VSet.mem x (snodes g (nodes g y z p0) y z iHp)
    then coq_SPath_sub g (nodes g y z p0) (VSet.add x (nodes g y z p0)) x z
           (snd (split g (nodes g y z p0) y z iHp x true))
    else coq_SPath_sub g (VSet.add x (snodes g (nodes g y z p0) y z iHp))
           (VSet.add x (nodes g y z p0)) x z (Coq_spath_step
           ((snodes g (nodes g y z p0) y z iHp),
           (VSet.add x (snodes g (nodes g y z p0) y z iHp)), x, y, z, e,
           (reduce g (nodes g y z p0) y z iHp)))

  (** val simplify2' : t -> V.t -> V.t -> coq_PathOf -> coq_SPath **)

  let simplify2' g x z p =
    coq_SPath_sub g (nodes g x z p) (coq_V g) x z (simplify2 g x z p)

  (** val to_label : coq_Z option -> nat **)

  let to_label = function
  | Some z0 -> (match z0 with
                | Zpos p -> Pos.to_nat p
                | _ -> O)
  | None -> O

  (** val coq_VSet_Forall_reflect :
      t -> (VSet.elt -> bool) -> (VSet.elt -> reflect) -> VSet.t -> reflect **)

  let coq_VSet_Forall_reflect _ f _ s0 =
    iff_reflect (VSet.for_all f s0)

  (** val reflect_logically_equiv : bool -> reflect -> reflect **)

  let reflect_logically_equiv _ h0 =
    h0

  (** val is_acyclic : t -> bool **)

  let is_acyclic g =
    VSet.for_all (fun x ->
      match lsp g x x with
      | Some z -> (match z with
                   | Z0 -> true
                   | _ -> false)
      | None -> false) (coq_V g)

  (** val edge_pathOf : t -> EdgeSet.elt -> coq_PathOf **)

  let edge_pathOf _ e =
    Coq_pathOf_step ((e_source e), (e_target e), (e_target e), (Coq_existT
      ((e_weight e), __)), (Coq_pathOf_refl (e_target e)))

  module Subgraph1 =
   struct
    (** val coq_G' : t -> V.t -> V.t -> coq_Z -> t **)

    let coq_G' g y_0 x_0 k =
      (((coq_V g), (EdgeSet.add ((y_0, (Z.opp k)), x_0) (coq_E g))), (s g))

    (** val to_G' :
        t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> coq_PathOf **)

    let rec to_G' g y_0 x_0 k _ _ = function
    | Coq_pathOf_refl x -> Coq_pathOf_refl x
    | Coq_pathOf_step (x, y, z, e, p) ->
      Coq_pathOf_step (x, y, z, (Coq_existT ((projT1 e), __)),
        (to_G' g y_0 x_0 k y z p))

    (** val from_G'_path :
        t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> (coq_PathOf,
        coq_PathOf * coq_PathOf) sum **)

    let rec from_G'_path g y_0 x_0 k _ _ = function
    | Coq_pathOf_refl x -> Coq_inl (Coq_pathOf_refl x)
    | Coq_pathOf_step (x, y, z, e, p) ->
      let s0 = Edge.eq_dec ((y_0, (Z.opp k)), x_0) ((x, (projT1 e)), y) in
      if s0
      then Coq_inr ((Coq_pathOf_refl x),
             (match from_G'_path g y_0 x_0 k y z p with
              | Coq_inl p0 -> p0
              | Coq_inr p0 -> snd p0))
      else (match from_G'_path g y_0 x_0 k y z p with
            | Coq_inl a ->
              Coq_inl (Coq_pathOf_step (x, y, z, (Coq_existT ((projT1 e),
                __)), a))
            | Coq_inr b ->
              Coq_inr ((Coq_pathOf_step (x, y, y_0, (Coq_existT ((projT1 e),
                __)), (fst b))), (snd b)))

    (** val from_G' :
        t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
        (coq_SPath, coq_SPath * coq_SPath) sum **)

    let rec from_G' g y_0 x_0 k _ _ _ = function
    | Coq_spath_refl (s0, x) -> Coq_inl (Coq_spath_refl (s0, x))
    | Coq_spath_step (s0, s', x, y, z, e, s1) ->
      let s2 = Edge.eq_dec ((y_0, (Z.opp k)), x_0) ((x, (projT1 e)), y) in
      if s2
      then Coq_inr ((Coq_spath_refl (s', x)),
             (coq_SPath_sub g s0 s' x_0 z
               (match from_G' g y_0 x_0 k s0 y z s1 with
                | Coq_inl a -> a
                | Coq_inr b -> snd b)))
      else (match from_G' g y_0 x_0 k s0 y z s1 with
            | Coq_inl a ->
              Coq_inl (Coq_spath_step (s0, s', x, y, z, (Coq_existT
                ((projT1 e), __)), a))
            | Coq_inr b ->
              Coq_inr ((Coq_spath_step (s0, s', x, y, y_0, (Coq_existT
                ((projT1 e), __)), (fst b))),
                (coq_SPath_sub g s0 s' x_0 z (snd b))))

    (** val sto_G' :
        t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
        coq_SPath **)

    let rec sto_G' g y_0 x_0 k _ _ _ = function
    | Coq_spath_refl (s0, x) -> Coq_spath_refl (s0, x)
    | Coq_spath_step (s0, s', x, y, z, e, s1) ->
      Coq_spath_step (s0, s', x, y, z, (Coq_existT ((projT1 e), __)),
        (sto_G' g y_0 x_0 k s0 y z s1))
   end

  (** val coq_G' : t -> V.t -> V.t -> coq_Z -> t **)

  let coq_G' g y_0 x_0 k =
    (((coq_V g), (EdgeSet.add ((y_0, k), x_0) (coq_E g))), (s g))

  (** val to_G' :
      t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> coq_PathOf **)

  let rec to_G' g y_0 x_0 k _ _ = function
  | Coq_pathOf_refl x -> Coq_pathOf_refl x
  | Coq_pathOf_step (x, y, z, e, p) ->
    Coq_pathOf_step (x, y, z, (Coq_existT ((projT1 e), __)),
      (to_G' g y_0 x_0 k y z p))

  (** val from_G'_path :
      t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> (coq_PathOf,
      coq_PathOf * coq_PathOf) sum **)

  let rec from_G'_path g y_0 x_0 k _ _ = function
  | Coq_pathOf_refl x -> Coq_inl (Coq_pathOf_refl x)
  | Coq_pathOf_step (x, y, z, e, p) ->
    let s0 = Edge.eq_dec ((y_0, k), x_0) ((x, (projT1 e)), y) in
    if s0
    then Coq_inr ((Coq_pathOf_refl x),
           (match from_G'_path g y_0 x_0 k y z p with
            | Coq_inl p0 -> p0
            | Coq_inr p0 -> snd p0))
    else (match from_G'_path g y_0 x_0 k y z p with
          | Coq_inl a ->
            Coq_inl (Coq_pathOf_step (x, y, z, (Coq_existT ((projT1 e), __)),
              a))
          | Coq_inr b ->
            Coq_inr ((Coq_pathOf_step (x, y, y_0, (Coq_existT ((projT1 e),
              __)), (fst b))), (snd b)))

  (** val from_G' :
      t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
      (coq_SPath, coq_SPath * coq_SPath) sum **)

  let rec from_G' g y_0 x_0 k _ _ _ = function
  | Coq_spath_refl (s0, x) -> Coq_inl (Coq_spath_refl (s0, x))
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    let s2 = Edge.eq_dec ((y_0, k), x_0) ((x, (projT1 e)), y) in
    if s2
    then Coq_inr ((Coq_spath_refl (s', x)),
           (coq_SPath_sub g s0 s' x_0 z
             (match from_G' g y_0 x_0 k s0 y z s1 with
              | Coq_inl a -> a
              | Coq_inr b -> snd b)))
    else (match from_G' g y_0 x_0 k s0 y z s1 with
          | Coq_inl a ->
            Coq_inl (Coq_spath_step (s0, s', x, y, z, (Coq_existT
              ((projT1 e), __)), a))
          | Coq_inr b ->
            Coq_inr ((Coq_spath_step (s0, s', x, y, y_0, (Coq_existT
              ((projT1 e), __)), (fst b))),
              (coq_SPath_sub g s0 s' x_0 z (snd b))))

  (** val sto_G' :
      t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
      coq_SPath **)

  let rec sto_G' g y_0 x_0 k _ _ _ = function
  | Coq_spath_refl (s0, x) -> Coq_spath_refl (s0, x)
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    Coq_spath_step (s0, s', x, y, z, (Coq_existT ((projT1 e), __)),
      (sto_G' g y_0 x_0 k s0 y z s1))

  (** val coq_PathOf_add_end :
      t -> V.t -> V.t -> V.t -> coq_PathOf -> coq_EdgeOf -> coq_PathOf **)

  let rec coq_PathOf_add_end g _ _ z p e =
    match p with
    | Coq_pathOf_refl x0 -> Coq_pathOf_step (x0, z, z, e, (Coq_pathOf_refl z))
    | Coq_pathOf_step (x0, y0, z0, e', p') ->
      Coq_pathOf_step (x0, y0, z, e', (coq_PathOf_add_end g y0 z0 z p' e))

  (** val leqb_vertices : t -> coq_Z -> V.t -> VSet.elt -> bool **)

  let leqb_vertices g z x y =
    if VSet.mem y (coq_V g)
    then is_left (Nbar.le_dec (Some z) (lsp_fast g x y))
    else (&&) (Z.leb z Z0)
           ((||) (is_left (V.eq_dec x y))
             (is_left (Nbar.le_dec (Some z) (lsp_fast g x (s g)))))

  (** val edge_map : (Edge.t -> Edge.t) -> EdgeSet.t -> EdgeSet.t **)

  let edge_map f es =
    EdgeSetProp.of_list (map f (EdgeSetProp.to_list es))

  (** val diff : labelling -> V.t -> V.t -> coq_Z **)

  let diff l x y =
    Z.sub (Z.of_nat (l y)) (Z.of_nat (l x))

  (** val relabel : t -> labelling -> t **)

  let relabel g l =
    (((coq_V g),
      (edge_map (fun e -> (((e_source e),
        (diff l (e_source e) (e_target e))), (e_target e))) (coq_E g))),
      (s g))

  (** val relabel_path :
      t -> labelling -> V.t -> V.t -> coq_PathOf -> coq_PathOf **)

  let relabel_path _ l x y _top_assumption_ =
    let _evar_0_ = fun x0 -> Coq_pathOf_refl x0 in
    let _evar_0_0 = fun x0 y0 z e _ ih -> Coq_pathOf_step (x0, y0, z,
      (Coq_existT
      ((diff l (e_source ((x0, (projT1 e)), y0))
         (e_target ((x0, (projT1 e)), y0))), __)), ih)
    in
    let rec f _ _ = function
    | Coq_pathOf_refl x0 -> _evar_0_ x0
    | Coq_pathOf_step (x0, y0, z, e, p0) -> _evar_0_0 x0 y0 z e p0 (f y0 z p0)
    in f x y _top_assumption_

  (** val relabel_map : t -> labelling -> Edge.t -> Edge.t **)

  let relabel_map g1 l e =
    if EdgeSet.mem e (coq_E g1)
    then (((e_source e), (diff l (e_source e) (e_target e))), (e_target e))
    else e

  (** val relabel_on : t -> t -> labelling -> t **)

  let relabel_on g1 g2 l =
    (((coq_V g2), (edge_map (relabel_map g1 l) (coq_E g2))), (s g2))

  (** val map_path :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> V.t -> V.t ->
      coq_PathOf -> coq_PathOf **)

  let rec map_path g1 g2 on_edge _ _ = function
  | Coq_pathOf_refl x -> Coq_pathOf_refl x
  | Coq_pathOf_step (x, y, z, e, p0) ->
    Coq_pathOf_step (x, y, z, (on_edge x y e),
      (map_path g1 g2 on_edge y z p0))

  type map_path_graph =
  | Coq_map_path_graph_equation_1 of V.t
  | Coq_map_path_graph_equation_2 of V.t * V.t * V.t * coq_EdgeOf
     * coq_PathOf * map_path_graph

  (** val map_path_graph_rect :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> 'a1) ->
      (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> map_path_graph -> 'a1
      -> 'a1) -> V.t -> V.t -> coq_PathOf -> coq_PathOf -> map_path_graph ->
      'a1 **)

  let rec map_path_graph_rect g1 g2 on_edge f f0 _ _ _ _ = function
  | Coq_map_path_graph_equation_1 x -> f x
  | Coq_map_path_graph_equation_2 (x, y, y', e, p, hind) ->
    f0 x y y' e p hind
      (map_path_graph_rect g1 g2 on_edge f f0 y' y p
        (map_path g1 g2 on_edge y' y p) hind)

  (** val map_path_graph_correct :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> V.t -> V.t ->
      coq_PathOf -> map_path_graph **)

  let rec map_path_graph_correct g1 g2 on_edge _ _ = function
  | Coq_pathOf_refl x -> Coq_map_path_graph_equation_1 x
  | Coq_pathOf_step (x, y, z, e, p0) ->
    Coq_map_path_graph_equation_2 (x, z, y, e, p0,
      (map_path_graph_correct g1 g2 on_edge y z p0))

  (** val map_path_elim :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> 'a1) ->
      (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> 'a1 -> 'a1) -> V.t ->
      V.t -> coq_PathOf -> 'a1 **)

  let map_path_elim g1 g2 on_edge f f0 x y p =
    let rec f1 _ _ _ _ = function
    | Coq_map_path_graph_equation_1 x0 -> f x0
    | Coq_map_path_graph_equation_2 (x0, y0, y', e, p0, hind) ->
      f0 x0 y0 y' e p0 (f1 y' y0 p0 (map_path g1 g2 on_edge y' y0 p0) hind)
    in f1 x y p (map_path g1 g2 on_edge x y p)
         (map_path_graph_correct g1 g2 on_edge x y p)

  (** val coq_FunctionalElimination_map_path :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> __) ->
      (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> __ -> __) -> V.t ->
      V.t -> coq_PathOf -> __ **)

  let coq_FunctionalElimination_map_path =
    map_path_elim

  (** val coq_FunctionalInduction_map_path :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> V.t ->
      coq_PathOf -> coq_PathOf) coq_FunctionalInduction **)

  let coq_FunctionalInduction_map_path g1 g2 on_edge =
    Obj.magic map_path_graph_correct g1 g2 on_edge

  (** val map_spath :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> VSet.t -> V.t ->
      V.t -> coq_SPath -> coq_SPath **)

  let rec map_spath g1 g2 on_edge _ _ _ = function
  | Coq_spath_refl (s0, x) -> Coq_spath_refl (s0, x)
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    Coq_spath_step (s0, s', x, y, z, (on_edge x y e),
      (map_spath g1 g2 on_edge s0 y z s1))

  type map_spath_graph =
  | Coq_map_spath_graph_equation_1 of VSet.t * V.t
  | Coq_map_spath_graph_equation_2 of VSet.t * V.t * V.t * VSet.t * V.t
     * coq_EdgeOf * coq_SPath * map_spath_graph

  (** val map_spath_graph_rect :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
      'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
      coq_SPath -> map_spath_graph -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t ->
      coq_SPath -> coq_SPath -> map_spath_graph -> 'a1 **)

  let rec map_spath_graph_rect g1 g2 on_edge f f0 _ _ _ _ _ = function
  | Coq_map_spath_graph_equation_1 (s0, x) -> f s0 x
  | Coq_map_spath_graph_equation_2 (s0, x, y, s1, y', e, p, hind) ->
    f0 s0 x y s1 y' __ e p hind
      (map_spath_graph_rect g1 g2 on_edge f f0 s1 y' y p
        (map_spath g1 g2 on_edge s1 y' y p) hind)

  (** val map_spath_graph_correct :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> VSet.t -> V.t ->
      V.t -> coq_SPath -> map_spath_graph **)

  let rec map_spath_graph_correct g1 g2 on_edge _ _ _ = function
  | Coq_spath_refl (s0, x) -> Coq_map_spath_graph_equation_1 (s0, x)
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    Coq_map_spath_graph_equation_2 (s', x, z, s0, y, e, s1,
      (map_spath_graph_correct g1 g2 on_edge s0 y z s1))

  (** val map_spath_elim :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
      'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
      coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t -> coq_SPath -> 'a1 **)

  let map_spath_elim g1 g2 on_edge f f0 s0 x y p =
    let rec f1 _ _ _ _ _ = function
    | Coq_map_spath_graph_equation_1 (s1, x0) -> f s1 x0
    | Coq_map_spath_graph_equation_2 (s1, x0, y0, s2, y', e, p0, hind) ->
      f0 s1 x0 y0 s2 y' __ e p0
        (f1 s2 y' y0 p0 (map_spath g1 g2 on_edge s2 y' y0 p0) hind)
    in f1 s0 x y p (map_spath g1 g2 on_edge s0 x y p)
         (map_spath_graph_correct g1 g2 on_edge s0 x y p)

  (** val coq_FunctionalElimination_map_spath :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
      __) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
      coq_SPath -> __ -> __) -> VSet.t -> V.t -> V.t -> coq_SPath -> __ **)

  let coq_FunctionalElimination_map_spath =
    map_spath_elim

  (** val coq_FunctionalInduction_map_spath :
      t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
      V.t -> coq_SPath -> coq_SPath) coq_FunctionalInduction **)

  let coq_FunctionalInduction_map_spath g1 g2 on_edge =
    Obj.magic map_spath_graph_correct g1 g2 on_edge

  (** val first_in_clause_2 :
      t -> (VSet.t -> V.t -> V.t -> coq_SPath -> V.t) -> VSet.t -> V.t ->
      bool -> V.t -> VSet.t -> V.t -> coq_EdgeOf -> coq_SPath -> V.t **)

  let first_in_clause_2 _ first_in0 _ x refine y s1 y0 _ q =
    if refine then x else first_in0 s1 y0 y q

  (** val first_in : t -> t -> VSet.t -> V.t -> V.t -> coq_SPath -> V.t **)

  let rec first_in g1 g2 _ _ _ = function
  | Coq_spath_refl (_, x) -> x
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    first_in_clause_2 g2 (first_in g1 g2) s' x (VSet.mem x (coq_V g1)) z s0 y
      e s1

  type first_in_graph =
  | Coq_first_in_graph_equation_1 of VSet.t * V.t
  | Coq_first_in_graph_refinement_2 of VSet.t * V.t * V.t * VSet.t * 
     V.t * coq_EdgeOf * coq_SPath * first_in_clause_2_graph
  and first_in_clause_2_graph =
  | Coq_first_in_clause_2_graph_equation_1 of VSet.t * V.t * V.t * VSet.t
     * V.t * coq_EdgeOf * coq_SPath
  | Coq_first_in_clause_2_graph_equation_2 of VSet.t * V.t * V.t * VSet.t
     * V.t * coq_EdgeOf * coq_SPath * first_in_graph

  (** val first_in_graph_mut :
      t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
      V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2
      -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf
      -> coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
      coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t ->
      V.t -> V.t -> coq_SPath -> V.t -> first_in_graph -> 'a1 **)

  let first_in_graph_mut g1 g2 f f0 f1 f2 =
    let rec f3 _ _ _ _ _ = function
    | Coq_first_in_graph_equation_1 (s0, x) -> f s0 x
    | Coq_first_in_graph_refinement_2 (s0, x, y, s1, y0, e, q, hind) ->
      f0 s0 x y s1 y0 __ e q hind
        (f4 s0 x (VSet.mem x (coq_V g1)) y s1 y0 __ e q
          (first_in_clause_2 g2 (first_in g1 g2) s0 x (VSet.mem x (coq_V g1))
            y s1 y0 e q) hind)
    and f4 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_first_in_clause_2_graph_equation_1 (s2, x0, z0, s1, y0, e, q) ->
      f1 s2 x0 z0 s1 y0 __ e q
    | Coq_first_in_clause_2_graph_equation_2 (s2, x0, z0, s1, y0, e, q, hind) ->
      f2 s2 x0 z0 s1 y0 __ e q hind
        (f3 s1 y0 z0 q (first_in g1 g2 s1 y0 z0 q) hind)
    in f3

  (** val first_in_clause_2_graph_mut :
      t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
      V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2
      -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf
      -> coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
      coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t ->
      V.t -> bool -> V.t -> VSet.t -> V.t -> coq_EdgeOf -> coq_SPath -> V.t
      -> first_in_clause_2_graph -> 'a2 **)

  let first_in_clause_2_graph_mut g1 g2 f f0 f1 f2 s0 x refine y s1 y0 e q t0 f3 =
    let rec f4 _ _ _ _ _ = function
    | Coq_first_in_graph_equation_1 (s2, x0) -> f s2 x0
    | Coq_first_in_graph_refinement_2 (s2, x0, y1, s3, y2, e0, q0, hind) ->
      f0 s2 x0 y1 s3 y2 __ e0 q0 hind
        (f5 s2 x0 (VSet.mem x0 (coq_V g1)) y1 s3 y2 e0 q0
          (first_in_clause_2 g2 (first_in g1 g2) s2 x0
            (VSet.mem x0 (coq_V g1)) y1 s3 y2 e0 q0) hind)
    and f5 _ _ _ _ _ _ _ _ _ = function
    | Coq_first_in_clause_2_graph_equation_1 (s2, x0, z0, s3, y1, e0, q0) ->
      f1 s2 x0 z0 s3 y1 __ e0 q0
    | Coq_first_in_clause_2_graph_equation_2 (s2, x0, z0, s3, y1, e0, q0, hind) ->
      f2 s2 x0 z0 s3 y1 __ e0 q0 hind
        (f4 s3 y1 z0 q0 (first_in g1 g2 s3 y1 z0 q0) hind)
    in f5 s0 x refine y s1 y0 e q t0 f3

  (** val first_in_graph_rect :
      t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
      V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2
      -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf
      -> coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
      coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t ->
      V.t -> V.t -> coq_SPath -> V.t -> first_in_graph -> 'a1 **)

  let first_in_graph_rect =
    first_in_graph_mut

  (** val first_in_graph_correct :
      t -> t -> VSet.t -> V.t -> V.t -> coq_SPath -> first_in_graph **)

  let rec first_in_graph_correct g1 g2 _ _ _ = function
  | Coq_spath_refl (s0, x) -> Coq_first_in_graph_equation_1 (s0, x)
  | Coq_spath_step (s0, s', x, y, z, e, s1) ->
    Coq_first_in_graph_refinement_2 (s', x, z, s0, y, e, s1,
      (let refine = VSet.mem x (coq_V g1) in
       if refine
       then Coq_first_in_clause_2_graph_equation_1 (s', x, z, s0, y, e, s1)
       else Coq_first_in_clause_2_graph_equation_2 (s', x, z, s0, y, e, s1,
              (first_in_graph_correct g1 g2 s0 y z s1))))

  (** val first_in_elim :
      t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
      V.t -> __ -> coq_EdgeOf -> coq_SPath -> __ -> 'a1) -> (VSet.t -> V.t ->
      V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> __ ->
      'a1) -> VSet.t -> V.t -> V.t -> coq_SPath -> 'a1 **)

  let first_in_elim g1 g2 f f1 f2 s0 x y p =
    first_in_graph_mut g1 g2 f (fun _ _ _ _ _ _ _ _ _ x0 -> x0 __) f1
      (fun s2 x0 z0 s1 y0 _ e q _ -> f2 s2 x0 z0 s1 y0 __ e q) s0 x y p
      (first_in g1 g2 s0 x y p) (first_in_graph_correct g1 g2 s0 x y p)

  (** val coq_FunctionalElimination_first_in :
      t -> t -> (VSet.t -> V.t -> __) -> (VSet.t -> V.t -> V.t -> VSet.t ->
      V.t -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __) -> (VSet.t -> V.t ->
      V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __ ->
      __) -> VSet.t -> V.t -> V.t -> coq_SPath -> __ **)

  let coq_FunctionalElimination_first_in =
    first_in_elim

  (** val coq_FunctionalInduction_first_in :
      t -> t -> (VSet.t -> V.t -> V.t -> coq_SPath -> V.t)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_first_in g1 g2 =
    Obj.magic first_in_graph_correct g1 g2

  (** val from1 :
      t -> t -> labelling -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf **)

  let from1 _ _ l x y _ =
    Coq_existT ((diff l x y), __)

  (** val from2 :
      t -> t -> labelling -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf **)

  let from2 g1 _ l x y x0 =
    Coq_existT
      ((if EdgeSet.mem ((x, (projT1 x0)), y) (coq_E g1)
        then diff l x y
        else projT1 x0), __)

  (** val coq_SPath_direct_subterm_sig_pack :
      t -> VSet.t -> V.t -> V.t -> VSet.t -> V.t -> V.t -> coq_SPath ->
      coq_SPath ->
      (VSet.t * (V.t * (V.t * (VSet.t * (V.t * (V.t * (coq_SPath * coq_SPath))))))) * __ **)

  let coq_SPath_direct_subterm_sig_pack _ x x0 x1 x2 x3 x4 x5 x6 =
    (x,(x0,(x1,(x2,(x3,(x4,(x5,x6))))))),__

  (** val coq_SPath_direct_subterm_Signature :
      t -> VSet.t -> V.t -> V.t -> VSet.t -> V.t -> V.t -> coq_SPath ->
      coq_SPath ->
      (VSet.t * (V.t * (V.t * (VSet.t * (V.t * (V.t * (coq_SPath * coq_SPath))))))) * __ **)

  let coq_SPath_direct_subterm_Signature =
    coq_SPath_direct_subterm_sig_pack

  (** val subgraph_on_edge :
      t -> t -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf **)

  let subgraph_on_edge _ _ _ _ __top_assumption_ =
    let _evar_0_ = fun w -> Coq_existT (w, __) in
    let Coq_existT (x, _) = __top_assumption_ in _evar_0_ x

  (** val reflectEq_vertices : VSet.E.t coq_ReflectEq **)

  let reflectEq_vertices x y =
    match VSet.E.compare x y with
    | Eq -> true
    | _ -> false

  (** val reflectEq_Z : coq_Z coq_ReflectEq **)

  let reflectEq_Z =
    Z.eqb

  (** val reflectEq_nbar : Nbar.t coq_ReflectEq **)

  let reflectEq_nbar =
    reflect_option reflectEq_Z

  module IsFullSubgraph =
   struct
    (** val add_from_orig : t -> VSet.elt -> VSet.t -> VSet.t **)

    let add_from_orig g1 v s0 =
      if VSet.mem v (coq_V g1) then VSet.add v s0 else s0

    (** val fold_fun : t -> Edge.t -> VSet.t -> VSet.t **)

    let fold_fun g1 e s0 =
      add_from_orig g1 (e_source e) (add_from_orig g1 (e_target e) s0)

    (** val border_set : t -> EdgeSet.t -> VSet.t **)

    let border_set g1 ext =
      EdgeSet.fold (fold_fun g1) ext VSet.empty

    (** val is_full_extension : t -> t -> bool **)

    let is_full_extension g1 g2 =
      let ext = EdgeSet.diff (coq_E g2) (coq_E g1) in
      let bs = border_set g1 ext in
      VSet.for_all (fun x ->
        VSet.for_all (fun y -> reflectEq_nbar (lsp g1 x y) (lsp g2 x y)) bs)
        bs

    (** val is_full_subgraph : t -> t -> bool **)

    let is_full_subgraph g1 g2 =
      (&&)
        ((&&)
          ((&&) (VSet.subset (coq_V g1) (coq_V g2))
            (EdgeSet.subset (coq_E g1) (coq_E g2)))
          (reflectEq_vertices (s g1) (s g2)))
        (VSet.for_all (fun x ->
          VSet.for_all (fun y -> reflectEq_nbar (lsp g1 x y) (lsp g2 x y))
            (coq_V g1)) (coq_V g1))
   end

  module RelabelWrtEdge =
   struct
    (** val r : t -> labelling -> V.t -> nat -> labelling **)

    let r g l x k =
      let d = Some (Z.of_nat (add k (l x))) in
      (fun z -> Nat.max (l z) (to_label (Nbar.add (lsp g x z) d)))

    (** val stdl : t -> labelling **)

    let stdl g x =
      to_label (lsp g (s g) x)

    (** val dxy : t -> V.t -> V.t -> coq_Z -> nat **)

    let dxy g x y nxy =
      Z.to_nat (Z.sub (Z.sub (Z.of_nat (stdl g y)) (Z.of_nat (stdl g x))) nxy)

    (** val l' : t -> V.t -> V.t -> coq_Z -> labelling **)

    let l' g x y nxy =
      r g (stdl g) x (dxy g x y nxy)
   end
 end
