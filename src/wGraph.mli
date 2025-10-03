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

module Nbar :
 sig
  type t = coq_Z option

  val max : t -> t -> t

  val add : t -> t -> t

  val le_dec : t -> t -> bool
 end

module WeightedGraph :
 functor (V:UsualOrderedType) ->
 functor (VSet:S with module E = V) ->
 sig
  module VSetFact :
   sig
    val eqb : V.t -> V.t -> bool
   end

  module VSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : V.t -> V.t -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : V.t -> V.t -> bool
     end

    val coq_In_dec : VSet.elt -> VSet.t -> bool

    val of_list : VSet.elt list -> VSet.t

    val to_list : VSet.t -> VSet.elt list

    val fold_rec :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> __ -> 'a2) ->
      (VSet.elt -> 'a1 -> VSet.t -> VSet.t -> __ -> __ -> __ -> 'a2 -> 'a2)
      -> 'a2

    val fold_rec_bis :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> VSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> __
      -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> 'a2 -> (VSet.elt -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> (VSet.t -> VSet.t -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> 'a2 -> 'a2)
      -> VSet.t -> 'a2

    val fold_rel :
      (VSet.elt -> 'a1 -> 'a1) -> (VSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
      VSet.t -> 'a3 -> (VSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (VSet.t -> __ -> 'a1) -> (VSet.t -> VSet.t -> 'a1 -> VSet.elt -> __ ->
      __ -> 'a1) -> VSet.t -> 'a1

    val set_induction_bis :
      (VSet.t -> VSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VSet.elt -> VSet.t ->
      __ -> 'a1 -> 'a1) -> VSet.t -> 'a1

    val cardinal_inv_2 : VSet.t -> nat -> VSet.elt

    val cardinal_inv_2b : VSet.t -> VSet.elt
   end

  module VSetDecide :
   sig
    module F :
     sig
      val eqb : V.t -> V.t -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module Edge :
   sig
    type t = (V.t * coq_Z) * V.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool

    val eqb : t -> t -> bool
   end

  module EdgeSet :
   sig
    module Raw :
     sig
      type elt = (V.t * coq_Z) * V.t

      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : ((V.t * coq_Z) * V.t) -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux :
        ((V.t * coq_Z) * V.t) list -> tree -> ((V.t * coq_Z) * V.t) list

      val elements : tree -> ((V.t * coq_Z) * V.t) list

      val rev_elements_aux :
        ((V.t * coq_Z) * V.t) list -> tree -> ((V.t * coq_Z) * V.t) list

      val rev_elements : tree -> ((V.t * coq_Z) * V.t) list

      val cardinal : tree -> nat

      val maxdepth : tree -> nat

      val mindepth : tree -> nat

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        ((V.t * coq_Z) * V.t) -> (enumeration -> comparison) -> enumeration
        -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> ((V.t * coq_Z) * V.t) -> tree -> bool

      val subsetr : (tree -> bool) -> ((V.t * coq_Z) * V.t) -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Z_as_Int.t

      val singleton : ((V.t * coq_Z) * V.t) -> tree

      val create : t -> ((V.t * coq_Z) * V.t) -> t -> tree

      val assert_false : t -> ((V.t * coq_Z) * V.t) -> t -> tree

      val bal : t -> ((V.t * coq_Z) * V.t) -> t -> tree

      val add : ((V.t * coq_Z) * V.t) -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : ((V.t * coq_Z) * V.t) -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : ((V.t * coq_Z) * V.t) -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : ((V.t * coq_Z) * V.t) -> tree -> bool

      val gtb_tree : ((V.t * coq_Z) * V.t) -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (V.t * coq_Z) * V.t

            val compare :
              ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> comparison

            val eq_dec :
              ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
           end

          module TO :
           sig
            type t = (V.t * coq_Z) * V.t

            val compare :
              ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> comparison

            val eq_dec :
              ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
           end
         end

        val eq_dec : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool

        val lt_dec : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool

        val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = (V.t * coq_Z) * V.t

              val compare :
                ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> comparison

              val eq_dec :
                ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
             end

            module TO :
             sig
              type t = (V.t * coq_Z) * V.t

              val compare :
                ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> comparison

              val eq_dec :
                ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
             end
           end

          val eq_dec : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool

          val lt_dec : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool

          val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * ((V.t * coq_Z) * V.t) * t
      | R_bal_1 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_2 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_3 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_4 of t * ((V.t * coq_Z) * V.t) * t
      | R_bal_5 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_6 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_7 of t * ((V.t * coq_Z) * V.t) * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree
      | R_bal_8 of t * ((V.t * coq_Z) * V.t) * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
         * ((V.t * coq_Z) * V.t) * tree * (t * elt) * coq_R_remove_min * 
         t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * bool * t * tree * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * bool * t * tree * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * bool * t * tree * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * bool * t * tree * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t)
         * tree * Z_as_Int.t * tree * ((V.t * coq_Z) * V.t) * tree * 
         t * bool * t * tree * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = (V.t * coq_Z) * V.t

      val compare :
        ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> comparison

      val eq_dec : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
     end

    type elt = (V.t * coq_Z) * V.t

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  module EdgeSetFact :
   sig
    val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
   end

  module EdgeSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
     end

    val coq_In_dec : EdgeSet.elt -> EdgeSet.t -> bool

    val of_list : EdgeSet.elt list -> EdgeSet.t

    val to_list : EdgeSet.t -> EdgeSet.elt list

    val fold_rec :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> (EdgeSet.t -> __ ->
      'a2) -> (EdgeSet.elt -> 'a1 -> EdgeSet.t -> EdgeSet.t -> __ -> __ -> __
      -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> (EdgeSet.t ->
      EdgeSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (EdgeSet.elt -> 'a1 ->
      EdgeSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> EdgeSet.t -> 'a2 -> (EdgeSet.elt
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (EdgeSet.elt -> 'a1 -> 'a1) -> 'a1 -> (EdgeSet.t -> EdgeSet.t -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2 -> (EdgeSet.elt -> 'a1 -> EdgeSet.t -> __ ->
      'a2 -> 'a2) -> EdgeSet.t -> 'a2

    val fold_rel :
      (EdgeSet.elt -> 'a1 -> 'a1) -> (EdgeSet.elt -> 'a2 -> 'a2) -> 'a1 ->
      'a2 -> EdgeSet.t -> 'a3 -> (EdgeSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
      'a3) -> 'a3

    val set_induction :
      (EdgeSet.t -> __ -> 'a1) -> (EdgeSet.t -> EdgeSet.t -> 'a1 ->
      EdgeSet.elt -> __ -> __ -> 'a1) -> EdgeSet.t -> 'a1

    val set_induction_bis :
      (EdgeSet.t -> EdgeSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (EdgeSet.elt ->
      EdgeSet.t -> __ -> 'a1 -> 'a1) -> EdgeSet.t -> 'a1

    val cardinal_inv_2 : EdgeSet.t -> nat -> EdgeSet.elt

    val cardinal_inv_2b : EdgeSet.t -> EdgeSet.elt
   end

  module EdgeSetDecide :
   sig
    module F :
     sig
      val eqb : ((V.t * coq_Z) * V.t) -> ((V.t * coq_Z) * V.t) -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  type t = (VSet.t * EdgeSet.t) * V.t

  val coq_V : t -> VSet.t

  val coq_E : t -> EdgeSet.t

  val s : t -> V.t

  val e_source : Edge.t -> V.t

  val e_target : Edge.t -> V.t

  val e_weight : Edge.t -> coq_Z

  val opp_edge : Edge.t -> Edge.t

  type labelling = V.t -> nat

  val add_node : t -> VSet.elt -> t

  val add_edge : t -> Edge.t -> t

  type coq_EdgeOf = (coq_Z, __) sigT

  type coq_PathOf =
  | Coq_pathOf_refl of V.t
  | Coq_pathOf_step of V.t * V.t * V.t * coq_EdgeOf * coq_PathOf

  val coq_PathOf_rect :
    t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf ->
    'a1 -> 'a1) -> V.t -> V.t -> coq_PathOf -> 'a1

  val coq_PathOf_rec :
    t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf ->
    'a1 -> 'a1) -> V.t -> V.t -> coq_PathOf -> 'a1

  val weight : t -> V.t -> V.t -> coq_PathOf -> coq_Z

  val nodes : t -> V.t -> V.t -> coq_PathOf -> VSet.t

  val concat :
    t -> V.t -> V.t -> V.t -> coq_PathOf -> coq_PathOf -> coq_PathOf

  val length : t -> V.t -> V.t -> coq_PathOf -> coq_Z

  type coq_SPath =
  | Coq_spath_refl of VSet.t * V.t
  | Coq_spath_step of VSet.t * VSet.t * V.t * V.t * V.t * coq_EdgeOf
     * coq_SPath

  val coq_SPath_rect :
    t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t ->
    __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t ->
    coq_SPath -> 'a1

  val coq_SPath_rec :
    t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t ->
    __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t ->
    coq_SPath -> 'a1

  type coq_SPath_sig = coq_SPath

  val coq_SPath_sig_pack :
    t -> VSet.t -> V.t -> V.t -> coq_SPath ->
    (VSet.t * (V.t * V.t)) * coq_SPath

  val coq_SPath_Signature :
    t -> VSet.t -> V.t -> V.t -> (coq_SPath, VSet.t * (V.t * V.t),
    coq_SPath_sig) coq_Signature

  val coq_NoConfusionPackage_SPath :
    t -> ((VSet.t * (V.t * V.t)) * coq_SPath) coq_NoConfusionPackage

  val to_pathOf : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_PathOf

  val sweight : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_Z

  val is_simple : t -> V.t -> V.t -> coq_PathOf -> bool

  val to_simple : t -> V.t -> V.t -> coq_PathOf -> coq_SPath

  val add_end :
    t -> VSet.t -> V.t -> V.t -> coq_SPath -> V.t -> coq_EdgeOf -> VSet.t ->
    coq_SPath

  val coq_SPath_sub :
    t -> VSet.t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath

  val sconcat :
    t -> VSet.t -> VSet.t -> V.t -> V.t -> V.t -> coq_SPath -> coq_SPath ->
    coq_SPath

  val snodes : t -> VSet.t -> V.t -> V.t -> coq_SPath -> VSet.t

  val split :
    t -> VSet.t -> V.t -> V.t -> coq_SPath -> VSet.elt -> bool ->
    coq_SPath * coq_SPath

  val split' : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath * coq_SPath

  val spath_one : t -> VSet.t -> VSet.elt -> V.t -> coq_Z -> coq_SPath

  val simplify :
    t -> VSet.t -> V.t -> V.t -> coq_PathOf -> coq_SPath -> VSet.t -> (V.t,
    coq_SPath) sigT

  val succs : t -> V.t -> (coq_Z * V.t) list

  val lsp00 : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t

  val lsp0 : t -> VSet.t -> V.t -> V.t -> Nbar.t

  val lsp00_fast : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t

  val lsp_fast : t -> V.t -> V.t -> Nbar.t

  val lsp : t -> V.t -> V.t -> Nbar.t

  val is_nonpos : coq_Z option -> bool

  val reduce : t -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath

  val simplify2 : t -> V.t -> V.t -> coq_PathOf -> coq_SPath

  val simplify2' : t -> V.t -> V.t -> coq_PathOf -> coq_SPath

  val to_label : coq_Z option -> nat

  val coq_VSet_Forall_reflect :
    t -> (VSet.elt -> bool) -> (VSet.elt -> reflect) -> VSet.t -> reflect

  val reflect_logically_equiv : bool -> reflect -> reflect

  val is_acyclic : t -> bool

  val edge_pathOf : t -> EdgeSet.elt -> coq_PathOf

  module Subgraph1 :
   sig
    val coq_G' : t -> V.t -> V.t -> coq_Z -> t

    val to_G' :
      t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> coq_PathOf

    val from_G'_path :
      t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> (coq_PathOf,
      coq_PathOf * coq_PathOf) sum

    val from_G' :
      t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
      (coq_SPath, coq_SPath * coq_SPath) sum

    val sto_G' :
      t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
      coq_SPath
   end

  val coq_G' : t -> V.t -> V.t -> coq_Z -> t

  val to_G' :
    t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> coq_PathOf

  val from_G'_path :
    t -> V.t -> V.t -> coq_Z -> V.t -> V.t -> coq_PathOf -> (coq_PathOf,
    coq_PathOf * coq_PathOf) sum

  val from_G' :
    t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath ->
    (coq_SPath, coq_SPath * coq_SPath) sum

  val sto_G' :
    t -> V.t -> V.t -> coq_Z -> VSet.t -> V.t -> V.t -> coq_SPath -> coq_SPath

  val coq_PathOf_add_end :
    t -> V.t -> V.t -> V.t -> coq_PathOf -> coq_EdgeOf -> coq_PathOf

  val leqb_vertices : t -> coq_Z -> V.t -> VSet.elt -> bool

  val edge_map : (Edge.t -> Edge.t) -> EdgeSet.t -> EdgeSet.t

  val diff : labelling -> V.t -> V.t -> coq_Z

  val relabel : t -> labelling -> t

  val relabel_path : t -> labelling -> V.t -> V.t -> coq_PathOf -> coq_PathOf

  val relabel_map : t -> labelling -> Edge.t -> Edge.t

  val relabel_on : t -> t -> labelling -> t

  val map_path :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> V.t -> V.t ->
    coq_PathOf -> coq_PathOf

  type map_path_graph =
  | Coq_map_path_graph_equation_1 of V.t
  | Coq_map_path_graph_equation_2 of V.t * V.t * V.t * coq_EdgeOf
     * coq_PathOf * map_path_graph

  val map_path_graph_rect :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> 'a1) ->
    (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> map_path_graph -> 'a1
    -> 'a1) -> V.t -> V.t -> coq_PathOf -> coq_PathOf -> map_path_graph -> 'a1

  val map_path_graph_correct :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> V.t -> V.t ->
    coq_PathOf -> map_path_graph

  val map_path_elim :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> 'a1) ->
    (V.t -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> 'a1 -> 'a1) -> V.t ->
    V.t -> coq_PathOf -> 'a1

  val coq_FunctionalElimination_map_path :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> __) -> (V.t
    -> V.t -> V.t -> coq_EdgeOf -> coq_PathOf -> __ -> __) -> V.t -> V.t ->
    coq_PathOf -> __

  val coq_FunctionalInduction_map_path :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (V.t -> V.t ->
    coq_PathOf -> coq_PathOf) coq_FunctionalInduction

  val map_spath :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> VSet.t -> V.t ->
    V.t -> coq_SPath -> coq_SPath

  type map_spath_graph =
  | Coq_map_spath_graph_equation_1 of VSet.t * V.t
  | Coq_map_spath_graph_equation_2 of VSet.t * V.t * V.t * VSet.t * V.t
     * coq_EdgeOf * coq_SPath * map_spath_graph

  val map_spath_graph_rect :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
    'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> map_spath_graph -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t ->
    coq_SPath -> coq_SPath -> map_spath_graph -> 'a1

  val map_spath_graph_correct :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> VSet.t -> V.t ->
    V.t -> coq_SPath -> map_spath_graph

  val map_spath_elim :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
    'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> 'a1 -> 'a1) -> VSet.t -> V.t -> V.t -> coq_SPath -> 'a1

  val coq_FunctionalElimination_map_spath :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
    __) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> __ -> __) -> VSet.t -> V.t -> V.t -> coq_SPath -> __

  val coq_FunctionalInduction_map_spath :
    t -> t -> (V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf) -> (VSet.t -> V.t ->
    V.t -> coq_SPath -> coq_SPath) coq_FunctionalInduction

  val first_in_clause_2 :
    t -> (VSet.t -> V.t -> V.t -> coq_SPath -> V.t) -> VSet.t -> V.t -> bool
    -> V.t -> VSet.t -> V.t -> coq_EdgeOf -> coq_SPath -> V.t

  val first_in : t -> t -> VSet.t -> V.t -> V.t -> coq_SPath -> V.t

  type first_in_graph =
  | Coq_first_in_graph_equation_1 of VSet.t * V.t
  | Coq_first_in_graph_refinement_2 of VSet.t * V.t * V.t * VSet.t * 
     V.t * coq_EdgeOf * coq_SPath * first_in_clause_2_graph
  and first_in_clause_2_graph =
  | Coq_first_in_clause_2_graph_equation_1 of VSet.t * V.t * V.t * VSet.t
     * V.t * coq_EdgeOf * coq_SPath
  | Coq_first_in_clause_2_graph_equation_2 of VSet.t * V.t * V.t * VSet.t
     * V.t * coq_EdgeOf * coq_SPath * first_in_graph

  val first_in_graph_mut :
    t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
    V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2 ->
    'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
    coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t -> V.t
    -> V.t -> coq_SPath -> V.t -> first_in_graph -> 'a1

  val first_in_clause_2_graph_mut :
    t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
    V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2 ->
    'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
    coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t -> V.t
    -> bool -> V.t -> VSet.t -> V.t -> coq_EdgeOf -> coq_SPath -> V.t ->
    first_in_clause_2_graph -> 'a2

  val first_in_graph_rect :
    t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
    V.t -> __ -> coq_EdgeOf -> coq_SPath -> first_in_clause_2_graph -> 'a2 ->
    'a1) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf ->
    coq_SPath -> 'a2) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t -> __ ->
    coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) -> VSet.t -> V.t
    -> V.t -> coq_SPath -> V.t -> first_in_graph -> 'a1

  val first_in_graph_correct :
    t -> t -> VSet.t -> V.t -> V.t -> coq_SPath -> first_in_graph

  val first_in_elim :
    t -> t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> V.t -> V.t -> VSet.t ->
    V.t -> __ -> coq_EdgeOf -> coq_SPath -> __ -> 'a1) -> (VSet.t -> V.t ->
    V.t -> VSet.t -> V.t -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> __ ->
    'a1) -> VSet.t -> V.t -> V.t -> coq_SPath -> 'a1

  val coq_FunctionalElimination_first_in :
    t -> t -> (VSet.t -> V.t -> __) -> (VSet.t -> V.t -> V.t -> VSet.t -> V.t
    -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __) -> (VSet.t -> V.t -> V.t ->
    VSet.t -> V.t -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __ -> __) ->
    VSet.t -> V.t -> V.t -> coq_SPath -> __

  val coq_FunctionalInduction_first_in :
    t -> t -> (VSet.t -> V.t -> V.t -> coq_SPath -> V.t)
    coq_FunctionalInduction

  val from1 : t -> t -> labelling -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf

  val from2 : t -> t -> labelling -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf

  val coq_SPath_direct_subterm_sig_pack :
    t -> VSet.t -> V.t -> V.t -> VSet.t -> V.t -> V.t -> coq_SPath ->
    coq_SPath ->
    (VSet.t * (V.t * (V.t * (VSet.t * (V.t * (V.t * (coq_SPath * coq_SPath))))))) * __

  val coq_SPath_direct_subterm_Signature :
    t -> VSet.t -> V.t -> V.t -> VSet.t -> V.t -> V.t -> coq_SPath ->
    coq_SPath ->
    (VSet.t * (V.t * (V.t * (VSet.t * (V.t * (V.t * (coq_SPath * coq_SPath))))))) * __

  val subgraph_on_edge : t -> t -> V.t -> V.t -> coq_EdgeOf -> coq_EdgeOf

  val reflectEq_vertices : VSet.E.t coq_ReflectEq

  val reflectEq_Z : coq_Z coq_ReflectEq

  val reflectEq_nbar : Nbar.t coq_ReflectEq

  module IsFullSubgraph :
   sig
    val add_from_orig : t -> VSet.elt -> VSet.t -> VSet.t

    val fold_fun : t -> Edge.t -> VSet.t -> VSet.t

    val border_set : t -> EdgeSet.t -> VSet.t

    val is_full_extension : t -> t -> bool

    val is_full_subgraph : t -> t -> bool
   end

  module RelabelWrtEdge :
   sig
    val r : t -> labelling -> V.t -> nat -> labelling

    val stdl : t -> labelling

    val dxy : t -> V.t -> V.t -> coq_Z -> nat

    val l' : t -> V.t -> V.t -> coq_Z -> labelling
   end
 end
