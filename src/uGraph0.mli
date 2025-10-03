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

module VariableLevel :
 sig
  type t_ =
  | Coq_level of String.t
  | Coq_lvar of nat

  type t = t_

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool

  val to_noprop : t -> Level.t

  val coq_Evaluable : t coq_Evaluable
 end

module GoodConstraint :
 sig
  type t_ =
  | Coq_gc_le of VariableLevel.t * coq_Z * VariableLevel.t
  | Coq_gc_lt_set_level of nat * String.t
  | Coq_gc_le_set_var of nat * nat
  | Coq_gc_le_level_set of String.t * nat
  | Coq_gc_le_var_set of nat * nat

  val t__rect :
    (VariableLevel.t -> coq_Z -> VariableLevel.t -> 'a1) -> (nat -> String.t
    -> 'a1) -> (nat -> nat -> 'a1) -> (String.t -> nat -> 'a1) -> (nat -> nat
    -> 'a1) -> t_ -> 'a1

  val t__rec :
    (VariableLevel.t -> coq_Z -> VariableLevel.t -> 'a1) -> (nat -> String.t
    -> 'a1) -> (nat -> nat -> 'a1) -> (String.t -> nat -> 'a1) -> (nat -> nat
    -> 'a1) -> t_ -> 'a1

  val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage

  type t = t_

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val satisfies : valuation -> t -> bool
 end

module GoodConstraintSet :
 sig
  module Raw :
   sig
    type elt = GoodConstraint.t_

    type tree =
    | Leaf
    | Node of Z_as_Int.t * tree * GoodConstraint.t_ * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : GoodConstraint.t_ -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux :
      GoodConstraint.t_ list -> tree -> GoodConstraint.t_ list

    val elements : tree -> GoodConstraint.t_ list

    val rev_elements_aux :
      GoodConstraint.t_ list -> tree -> GoodConstraint.t_ list

    val rev_elements : tree -> GoodConstraint.t_ list

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
      GoodConstraint.t_ -> (enumeration -> comparison) -> enumeration ->
      comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> GoodConstraint.t_ -> tree -> bool

    val subsetr : (tree -> bool) -> GoodConstraint.t_ -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Z_as_Int.t

    val singleton : GoodConstraint.t_ -> tree

    val create : t -> GoodConstraint.t_ -> t -> tree

    val assert_false : t -> GoodConstraint.t_ -> t -> tree

    val bal : t -> GoodConstraint.t_ -> t -> tree

    val add : GoodConstraint.t_ -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : GoodConstraint.t_ -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : GoodConstraint.t_ -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : GoodConstraint.t_ -> tree -> bool

    val gtb_tree : GoodConstraint.t_ -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = GoodConstraint.t_

          val compare : GoodConstraint.t_ -> GoodConstraint.t_ -> comparison

          val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
         end

        module TO :
         sig
          type t = GoodConstraint.t_

          val compare : GoodConstraint.t_ -> GoodConstraint.t_ -> comparison

          val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
         end
       end

      val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool

      val lt_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool

      val eqb : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = GoodConstraint.t_

            val compare : GoodConstraint.t_ -> GoodConstraint.t_ -> comparison

            val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
           end

          module TO :
           sig
            type t = GoodConstraint.t_

            val compare : GoodConstraint.t_ -> GoodConstraint.t_ -> comparison

            val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
           end
         end

        val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool

        val lt_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool

        val eqb : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * GoodConstraint.t_ * t
    | R_bal_1 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree
    | R_bal_2 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree
    | R_bal_3 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree * Z_as_Int.t * tree * GoodConstraint.t_
       * tree
    | R_bal_4 of t * GoodConstraint.t_ * t
    | R_bal_5 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree
    | R_bal_6 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree
    | R_bal_7 of t * GoodConstraint.t_ * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree * Z_as_Int.t * tree * GoodConstraint.t_
       * tree
    | R_bal_8 of t * GoodConstraint.t_ * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
       * GoodConstraint.t_ * tree * (t * elt) * coq_R_remove_min * t * 
       elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_
       * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree
    | R_union_2 of tree * tree * Z_as_Int.t * tree * GoodConstraint.t_ * 
       tree * Z_as_Int.t * tree * GoodConstraint.t_ * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = GoodConstraint.t_

    val compare : GoodConstraint.t_ -> GoodConstraint.t_ -> comparison

    val eq_dec : GoodConstraint.t_ -> GoodConstraint.t_ -> bool
   end

  type elt = GoodConstraint.t_

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

val coq_GoodConstraintSet_pair :
  GoodConstraintSet.elt -> GoodConstraintSet.elt -> GoodConstraintSet.t

val gc_of_constraint :
  checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option

val add_gc_of_constraint :
  checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option ->
  GoodConstraintSet.t option

val gc_of_constraints :
  checker_flags -> ConstraintSet.t -> GoodConstraintSet.t option

module Coq_wGraph :
 sig
  module VSetFact :
   sig
    val eqb : Level.t_ -> Level.t_ -> bool
   end

  module VSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : Level.t_ -> Level.t_ -> bool
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
      val eqb : Level.t_ -> Level.t_ -> bool
     end

    val coq_In_dec : LevelSet.elt -> LevelSet.t -> bool

    val of_list : LevelSet.elt list -> LevelSet.t

    val to_list : LevelSet.t -> LevelSet.elt list

    val fold_rec :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t -> __
      -> 'a2) -> (LevelSet.elt -> 'a1 -> LevelSet.t -> LevelSet.t -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t ->
      LevelSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1
      -> LevelSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> 'a2 ->
      (LevelSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.t -> LevelSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 -> LevelSet.t -> __
      -> 'a2 -> 'a2) -> LevelSet.t -> 'a2

    val fold_rel :
      (LevelSet.elt -> 'a1 -> 'a1) -> (LevelSet.elt -> 'a2 -> 'a2) -> 'a1 ->
      'a2 -> LevelSet.t -> 'a3 -> (LevelSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
      'a3) -> 'a3

    val set_induction :
      (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 ->
      LevelSet.elt -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

    val set_induction_bis :
      (LevelSet.t -> LevelSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.elt
      -> LevelSet.t -> __ -> 'a1 -> 'a1) -> LevelSet.t -> 'a1

    val cardinal_inv_2 : LevelSet.t -> nat -> LevelSet.elt

    val cardinal_inv_2b : LevelSet.t -> LevelSet.elt
   end

  module VSetDecide :
   sig
    module F :
     sig
      val eqb : Level.t_ -> Level.t_ -> bool
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
    type t = (Level.t_ * coq_Z) * Level.t_

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool

    val eqb : t -> t -> bool
   end

  module EdgeSet :
   sig
    module Raw :
     sig
      type elt = (Level.t_ * coq_Z) * Level.t_

      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * ((Level.t_ * coq_Z) * Level.t_) * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : ((Level.t_ * coq_Z) * Level.t_) -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux :
        ((Level.t_ * coq_Z) * Level.t_) list -> tree ->
        ((Level.t_ * coq_Z) * Level.t_) list

      val elements : tree -> ((Level.t_ * coq_Z) * Level.t_) list

      val rev_elements_aux :
        ((Level.t_ * coq_Z) * Level.t_) list -> tree ->
        ((Level.t_ * coq_Z) * Level.t_) list

      val rev_elements : tree -> ((Level.t_ * coq_Z) * Level.t_) list

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
        ((Level.t_ * coq_Z) * Level.t_) -> (enumeration -> comparison) ->
        enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl :
        (tree -> bool) -> ((Level.t_ * coq_Z) * Level.t_) -> tree -> bool

      val subsetr :
        (tree -> bool) -> ((Level.t_ * coq_Z) * Level.t_) -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Z_as_Int.t

      val singleton : ((Level.t_ * coq_Z) * Level.t_) -> tree

      val create : t -> ((Level.t_ * coq_Z) * Level.t_) -> t -> tree

      val assert_false : t -> ((Level.t_ * coq_Z) * Level.t_) -> t -> tree

      val bal : t -> ((Level.t_ * coq_Z) * Level.t_) -> t -> tree

      val add : ((Level.t_ * coq_Z) * Level.t_) -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : ((Level.t_ * coq_Z) * Level.t_) -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : ((Level.t_ * coq_Z) * Level.t_) -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : ((Level.t_ * coq_Z) * Level.t_) -> tree -> bool

      val gtb_tree : ((Level.t_ * coq_Z) * Level.t_) -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (Level.t_ * coq_Z) * Level.t_

            val compare :
              ((Level.t_ * coq_Z) * Level.t_) ->
              ((Level.t_ * coq_Z) * Level.t_) -> comparison

            val eq_dec :
              ((Level.t_ * coq_Z) * Level.t_) ->
              ((Level.t_ * coq_Z) * Level.t_) -> bool
           end

          module TO :
           sig
            type t = (Level.t_ * coq_Z) * Level.t_

            val compare :
              ((Level.t_ * coq_Z) * Level.t_) ->
              ((Level.t_ * coq_Z) * Level.t_) -> comparison

            val eq_dec :
              ((Level.t_ * coq_Z) * Level.t_) ->
              ((Level.t_ * coq_Z) * Level.t_) -> bool
           end
         end

        val eq_dec :
          ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_)
          -> bool

        val lt_dec :
          ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_)
          -> bool

        val eqb :
          ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_)
          -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = (Level.t_ * coq_Z) * Level.t_

              val compare :
                ((Level.t_ * coq_Z) * Level.t_) ->
                ((Level.t_ * coq_Z) * Level.t_) -> comparison

              val eq_dec :
                ((Level.t_ * coq_Z) * Level.t_) ->
                ((Level.t_ * coq_Z) * Level.t_) -> bool
             end

            module TO :
             sig
              type t = (Level.t_ * coq_Z) * Level.t_

              val compare :
                ((Level.t_ * coq_Z) * Level.t_) ->
                ((Level.t_ * coq_Z) * Level.t_) -> comparison

              val eq_dec :
                ((Level.t_ * coq_Z) * Level.t_) ->
                ((Level.t_ * coq_Z) * Level.t_) -> bool
             end
           end

          val eq_dec :
            ((Level.t_ * coq_Z) * Level.t_) ->
            ((Level.t_ * coq_Z) * Level.t_) -> bool

          val lt_dec :
            ((Level.t_ * coq_Z) * Level.t_) ->
            ((Level.t_ * coq_Z) * Level.t_) -> bool

          val eqb :
            ((Level.t_ * coq_Z) * Level.t_) ->
            ((Level.t_ * coq_Z) * Level.t_) -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * ((Level.t_ * coq_Z) * Level.t_) * t
      | R_bal_1 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_2 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_3 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * 
         tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_4 of t * ((Level.t_ * coq_Z) * Level.t_) * t
      | R_bal_5 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_6 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_7 of t * ((Level.t_ * coq_Z) * Level.t_) * t * Z_as_Int.t
         * tree * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * 
         tree * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_bal_8 of t * ((Level.t_ * coq_Z) * Level.t_) * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * (t * elt)
         * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * Z_as_Int.t * tree
         * ((Level.t_ * coq_Z) * Level.t_) * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = (Level.t_ * coq_Z) * Level.t_

      val compare :
        ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_) ->
        comparison

      val eq_dec :
        ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_) ->
        bool
     end

    type elt = (Level.t_ * coq_Z) * Level.t_

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
    val eqb :
      ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_) ->
      bool
   end

  module EdgeSetProp :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb :
          ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_)
          -> bool
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
      val eqb :
        ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_) ->
        bool
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
      val eqb :
        ((Level.t_ * coq_Z) * Level.t_) -> ((Level.t_ * coq_Z) * Level.t_) ->
        bool
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

  type t = (LevelSet.t * EdgeSet.t) * Level.t_

  val coq_V : t -> LevelSet.t

  val coq_E : t -> EdgeSet.t

  val s : t -> Level.t_

  val e_source : Edge.t -> Level.t_

  val e_target : Edge.t -> Level.t_

  val e_weight : Edge.t -> coq_Z

  val opp_edge : Edge.t -> Edge.t

  type labelling = Level.t_ -> nat

  val add_node : t -> LevelSet.elt -> t

  val add_edge : t -> Edge.t -> t

  type coq_EdgeOf = (coq_Z, __) sigT

  type coq_PathOf =
  | Coq_pathOf_refl of Level.t_
  | Coq_pathOf_step of Level.t_ * Level.t_ * Level.t_ * coq_EdgeOf
     * coq_PathOf

  val coq_PathOf_rect :
    t -> (Level.t_ -> 'a1) -> (Level.t_ -> Level.t_ -> Level.t_ -> coq_EdgeOf
    -> coq_PathOf -> 'a1 -> 'a1) -> Level.t_ -> Level.t_ -> coq_PathOf -> 'a1

  val coq_PathOf_rec :
    t -> (Level.t_ -> 'a1) -> (Level.t_ -> Level.t_ -> Level.t_ -> coq_EdgeOf
    -> coq_PathOf -> 'a1 -> 'a1) -> Level.t_ -> Level.t_ -> coq_PathOf -> 'a1

  val weight : t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_Z

  val nodes : t -> Level.t_ -> Level.t_ -> coq_PathOf -> LevelSet.t

  val concat :
    t -> Level.t_ -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_PathOf ->
    coq_PathOf

  val length : t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_Z

  type coq_SPath =
  | Coq_spath_refl of LevelSet.t * Level.t_
  | Coq_spath_step of LevelSet.t * LevelSet.t * Level.t_ * Level.t_
     * Level.t_ * coq_EdgeOf * coq_SPath

  val coq_SPath_rect :
    t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> LevelSet.t ->
    Level.t_ -> Level.t_ -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> 'a1
    -> 'a1) -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> 'a1

  val coq_SPath_rec :
    t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> LevelSet.t ->
    Level.t_ -> Level.t_ -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> 'a1
    -> 'a1) -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> 'a1

  type coq_SPath_sig = coq_SPath

  val coq_SPath_sig_pack :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath ->
    (LevelSet.t * (Level.t_ * Level.t_)) * coq_SPath

  val coq_SPath_Signature :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> (coq_SPath,
    LevelSet.t * (Level.t_ * Level.t_), coq_SPath_sig) coq_Signature

  val coq_NoConfusionPackage_SPath :
    t -> ((LevelSet.t * (Level.t_ * Level.t_)) * coq_SPath)
    coq_NoConfusionPackage

  val to_pathOf :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> coq_PathOf

  val sweight : t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> coq_Z

  val is_simple : t -> Level.t_ -> Level.t_ -> coq_PathOf -> bool

  val to_simple : t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_SPath

  val add_end :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_ ->
    coq_EdgeOf -> LevelSet.t -> coq_SPath

  val coq_SPath_sub :
    t -> LevelSet.t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath ->
    coq_SPath

  val sconcat :
    t -> LevelSet.t -> LevelSet.t -> Level.t_ -> Level.t_ -> Level.t_ ->
    coq_SPath -> coq_SPath -> coq_SPath

  val snodes :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> LevelSet.t

  val split :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> LevelSet.elt ->
    bool -> coq_SPath * coq_SPath

  val split' :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath ->
    coq_SPath * coq_SPath

  val spath_one :
    t -> LevelSet.t -> LevelSet.elt -> Level.t_ -> coq_Z -> coq_SPath

  val simplify :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_SPath ->
    LevelSet.t -> (Level.t_, coq_SPath) sigT

  val succs : t -> Level.t_ -> (coq_Z * Level.t_) list

  val lsp00 : t -> nat -> LevelSet.t -> Level.t_ -> Level.t_ -> Nbar.t

  val lsp0 : t -> LevelSet.t -> Level.t_ -> Level.t_ -> Nbar.t

  val lsp00_fast : t -> nat -> LevelSet.t -> Level.t_ -> Level.t_ -> Nbar.t

  val lsp_fast : t -> Level.t_ -> Level.t_ -> Nbar.t

  val lsp : t -> Level.t_ -> Level.t_ -> Nbar.t

  val is_nonpos : coq_Z option -> bool

  val reduce :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> coq_SPath

  val simplify2 : t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_SPath

  val simplify2' : t -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_SPath

  val to_label : coq_Z option -> nat

  val coq_VSet_Forall_reflect :
    t -> (LevelSet.elt -> bool) -> (LevelSet.elt -> reflect) -> LevelSet.t ->
    reflect

  val reflect_logically_equiv : bool -> reflect -> reflect

  val is_acyclic : t -> bool

  val edge_pathOf : t -> EdgeSet.elt -> coq_PathOf

  module Subgraph1 :
   sig
    val coq_G' : t -> Level.t_ -> Level.t_ -> coq_Z -> t

    val to_G' :
      t -> Level.t_ -> Level.t_ -> coq_Z -> Level.t_ -> Level.t_ ->
      coq_PathOf -> coq_PathOf

    val from_G'_path :
      t -> Level.t_ -> Level.t_ -> coq_Z -> Level.t_ -> Level.t_ ->
      coq_PathOf -> (coq_PathOf, coq_PathOf * coq_PathOf) sum

    val from_G' :
      t -> Level.t_ -> Level.t_ -> coq_Z -> LevelSet.t -> Level.t_ ->
      Level.t_ -> coq_SPath -> (coq_SPath, coq_SPath * coq_SPath) sum

    val sto_G' :
      t -> Level.t_ -> Level.t_ -> coq_Z -> LevelSet.t -> Level.t_ ->
      Level.t_ -> coq_SPath -> coq_SPath
   end

  val coq_G' : t -> Level.t_ -> Level.t_ -> coq_Z -> t

  val to_G' :
    t -> Level.t_ -> Level.t_ -> coq_Z -> Level.t_ -> Level.t_ -> coq_PathOf
    -> coq_PathOf

  val from_G'_path :
    t -> Level.t_ -> Level.t_ -> coq_Z -> Level.t_ -> Level.t_ -> coq_PathOf
    -> (coq_PathOf, coq_PathOf * coq_PathOf) sum

  val from_G' :
    t -> Level.t_ -> Level.t_ -> coq_Z -> LevelSet.t -> Level.t_ -> Level.t_
    -> coq_SPath -> (coq_SPath, coq_SPath * coq_SPath) sum

  val sto_G' :
    t -> Level.t_ -> Level.t_ -> coq_Z -> LevelSet.t -> Level.t_ -> Level.t_
    -> coq_SPath -> coq_SPath

  val coq_PathOf_add_end :
    t -> Level.t_ -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_EdgeOf ->
    coq_PathOf

  val leqb_vertices : t -> coq_Z -> Level.t_ -> LevelSet.elt -> bool

  val edge_map : (Edge.t -> Edge.t) -> EdgeSet.t -> EdgeSet.t

  val diff : labelling -> Level.t_ -> Level.t_ -> coq_Z

  val relabel : t -> labelling -> t

  val relabel_path :
    t -> labelling -> Level.t_ -> Level.t_ -> coq_PathOf -> coq_PathOf

  val relabel_map : t -> labelling -> Edge.t -> Edge.t

  val relabel_on : t -> t -> labelling -> t

  val map_path :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> Level.t_
    -> Level.t_ -> coq_PathOf -> coq_PathOf

  type map_path_graph =
  | Coq_map_path_graph_equation_1 of Level.t_
  | Coq_map_path_graph_equation_2 of Level.t_ * Level.t_ * Level.t_
     * coq_EdgeOf * coq_PathOf * map_path_graph

  val map_path_graph_rect :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> (Level.t_
    -> 'a1) -> (Level.t_ -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_PathOf
    -> map_path_graph -> 'a1 -> 'a1) -> Level.t_ -> Level.t_ -> coq_PathOf ->
    coq_PathOf -> map_path_graph -> 'a1

  val map_path_graph_correct :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> Level.t_
    -> Level.t_ -> coq_PathOf -> map_path_graph

  val map_path_elim :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> (Level.t_
    -> 'a1) -> (Level.t_ -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_PathOf
    -> 'a1 -> 'a1) -> Level.t_ -> Level.t_ -> coq_PathOf -> 'a1

  val coq_FunctionalElimination_map_path :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> (Level.t_
    -> __) -> (Level.t_ -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_PathOf
    -> __ -> __) -> Level.t_ -> Level.t_ -> coq_PathOf -> __

  val coq_FunctionalInduction_map_path :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) -> (Level.t_
    -> Level.t_ -> coq_PathOf -> coq_PathOf) coq_FunctionalInduction

  val map_spath :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> coq_SPath

  type map_spath_graph =
  | Coq_map_spath_graph_equation_1 of LevelSet.t * Level.t_
  | Coq_map_spath_graph_equation_2 of LevelSet.t * Level.t_ * Level.t_
     * LevelSet.t * Level.t_ * coq_EdgeOf * coq_SPath * map_spath_graph

  val map_spath_graph_rect :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ -> Level.t_ ->
    LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    map_spath_graph -> 'a1 -> 'a1) -> LevelSet.t -> Level.t_ -> Level.t_ ->
    coq_SPath -> coq_SPath -> map_spath_graph -> 'a1

  val map_spath_graph_correct :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> map_spath_graph

  val map_spath_elim :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ -> Level.t_ ->
    LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> 'a1) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> 'a1

  val coq_FunctionalElimination_map_spath :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    (LevelSet.t -> Level.t_ -> __) -> (LevelSet.t -> Level.t_ -> Level.t_ ->
    LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> __

  val coq_FunctionalInduction_map_spath :
    t -> t -> (Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf) ->
    (LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> coq_SPath)
    coq_FunctionalInduction

  val first_in_clause_2 :
    t -> (LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_) ->
    LevelSet.t -> Level.t_ -> bool -> Level.t_ -> LevelSet.t -> Level.t_ ->
    coq_EdgeOf -> coq_SPath -> Level.t_

  val first_in :
    t -> t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_

  type first_in_graph =
  | Coq_first_in_graph_equation_1 of LevelSet.t * Level.t_
  | Coq_first_in_graph_refinement_2 of LevelSet.t * Level.t_ * Level.t_
     * LevelSet.t * Level.t_ * coq_EdgeOf * coq_SPath
     * first_in_clause_2_graph
  and first_in_clause_2_graph =
  | Coq_first_in_clause_2_graph_equation_1 of LevelSet.t * Level.t_
     * Level.t_ * LevelSet.t * Level.t_ * coq_EdgeOf * coq_SPath
  | Coq_first_in_clause_2_graph_equation_2 of LevelSet.t * Level.t_
     * Level.t_ * LevelSet.t * Level.t_ * coq_EdgeOf * coq_SPath
     * first_in_graph

  val first_in_graph_mut :
    t -> t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    first_in_clause_2_graph -> 'a2 -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    'a2) -> (LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_ ->
    __ -> coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_ ->
    first_in_graph -> 'a1

  val first_in_clause_2_graph_mut :
    t -> t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    first_in_clause_2_graph -> 'a2 -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    'a2) -> (LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_ ->
    __ -> coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) ->
    LevelSet.t -> Level.t_ -> bool -> Level.t_ -> LevelSet.t -> Level.t_ ->
    coq_EdgeOf -> coq_SPath -> Level.t_ -> first_in_clause_2_graph -> 'a2

  val first_in_graph_rect :
    t -> t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    first_in_clause_2_graph -> 'a2 -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath ->
    'a2) -> (LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_ ->
    __ -> coq_EdgeOf -> coq_SPath -> first_in_graph -> 'a1 -> 'a2) ->
    LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_ ->
    first_in_graph -> 'a1

  val first_in_graph_correct :
    t -> t -> LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath ->
    first_in_graph

  val first_in_elim :
    t -> t -> (LevelSet.t -> Level.t_ -> 'a1) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> __
    -> 'a1) -> (LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_
    -> __ -> coq_EdgeOf -> coq_SPath -> 'a1 -> __ -> 'a1) -> LevelSet.t ->
    Level.t_ -> Level.t_ -> coq_SPath -> 'a1

  val coq_FunctionalElimination_first_in :
    t -> t -> (LevelSet.t -> Level.t_ -> __) -> (LevelSet.t -> Level.t_ ->
    Level.t_ -> LevelSet.t -> Level.t_ -> __ -> coq_EdgeOf -> coq_SPath -> __
    -> __) -> (LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_
    -> __ -> coq_EdgeOf -> coq_SPath -> __ -> __ -> __) -> LevelSet.t ->
    Level.t_ -> Level.t_ -> coq_SPath -> __

  val coq_FunctionalInduction_first_in :
    t -> t -> (LevelSet.t -> Level.t_ -> Level.t_ -> coq_SPath -> Level.t_)
    coq_FunctionalInduction

  val from1 :
    t -> t -> labelling -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf

  val from2 :
    t -> t -> labelling -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf

  val coq_SPath_direct_subterm_sig_pack :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_ ->
    Level.t_ -> coq_SPath -> coq_SPath ->
    (LevelSet.t * (Level.t_ * (Level.t_ * (LevelSet.t * (Level.t_ * (Level.t_ * (coq_SPath * coq_SPath))))))) * __

  val coq_SPath_direct_subterm_Signature :
    t -> LevelSet.t -> Level.t_ -> Level.t_ -> LevelSet.t -> Level.t_ ->
    Level.t_ -> coq_SPath -> coq_SPath ->
    (LevelSet.t * (Level.t_ * (Level.t_ * (LevelSet.t * (Level.t_ * (Level.t_ * (coq_SPath * coq_SPath))))))) * __

  val subgraph_on_edge :
    t -> t -> Level.t_ -> Level.t_ -> coq_EdgeOf -> coq_EdgeOf

  val reflectEq_vertices : Level.t_ coq_ReflectEq

  val reflectEq_Z : coq_Z coq_ReflectEq

  val reflectEq_nbar : Nbar.t coq_ReflectEq

  module IsFullSubgraph :
   sig
    val add_from_orig : t -> LevelSet.elt -> LevelSet.t -> LevelSet.t

    val fold_fun : t -> Edge.t -> LevelSet.t -> LevelSet.t

    val border_set : t -> EdgeSet.t -> LevelSet.t

    val is_full_extension : t -> t -> bool

    val is_full_subgraph : t -> t -> bool
   end

  module RelabelWrtEdge :
   sig
    val r : t -> labelling -> Level.t_ -> nat -> labelling

    val stdl : t -> labelling

    val dxy : t -> Level.t_ -> Level.t_ -> coq_Z -> nat

    val l' : t -> Level.t_ -> Level.t_ -> coq_Z -> labelling
   end
 end

module VSet :
 sig
  module Raw :
   sig
    type elt = Level.t_

    type tree = LevelSet.Raw.tree =
    | Leaf
    | Node of Z_as_Int.t * tree * Level.t_ * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : Level.t_ -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : Level.t_ list -> tree -> Level.t_ list

    val elements : tree -> Level.t_ list

    val rev_elements_aux : Level.t_ list -> tree -> Level.t_ list

    val rev_elements : tree -> Level.t_ list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration = LevelSet.Raw.enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      Level.t_ -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> Level.t_ -> tree -> bool

    val subsetr : (tree -> bool) -> Level.t_ -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Z_as_Int.t

    val singleton : Level.t_ -> tree

    val create : t -> Level.t_ -> t -> tree

    val assert_false : t -> Level.t_ -> t -> tree

    val bal : t -> Level.t_ -> t -> tree

    val add : Level.t_ -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : Level.t_ -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = LevelSet.Raw.triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : Level.t_ -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : Level.t_ -> tree -> bool

    val gtb_tree : Level.t_ -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> bool
         end

        module TO :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> bool
         end
       end

      val eq_dec : Level.t_ -> Level.t_ -> bool

      val lt_dec : Level.t_ -> Level.t_ -> bool

      val eqb : Level.t_ -> Level.t_ -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> bool
           end

          module TO :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> bool
           end
         end

        val eq_dec : Level.t_ -> Level.t_ -> bool

        val lt_dec : Level.t_ -> Level.t_ -> bool

        val eqb : Level.t_ -> Level.t_ -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal = LevelSet.Raw.coq_R_bal =
    | R_bal_0 of t * Level.t_ * t
    | R_bal_1 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_2 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_3 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_4 of t * Level.t_ * t
    | R_bal_5 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_6 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_7 of t * Level.t_ * t * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_8 of t * Level.t_ * t

    type coq_R_remove_min = LevelSet.Raw.coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * Level.t_ * 
       tree * (t * elt) * coq_R_remove_min * t * elt

    type coq_R_merge = LevelSet.Raw.coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_concat = LevelSet.Raw.coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_inter = LevelSet.Raw.coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff = LevelSet.Raw.coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union = LevelSet.Raw.coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_union_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = Level.t_

    val compare : Level.t_ -> Level.t_ -> comparison

    val eq_dec : Level.t_ -> Level.t_ -> bool
   end

  type elt = Level.t_

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

type universes_graph = Coq_wGraph.t

val edge_of_level : VariableLevel.t -> Coq_wGraph.EdgeSet.elt

val edge_of_constraint : GoodConstraint.t -> Coq_wGraph.EdgeSet.elt

val variable_of_level : Level.t -> VariableLevel.t option

val add_level_edges : VSet.t -> Coq_wGraph.EdgeSet.t -> Coq_wGraph.EdgeSet.t

val add_cstrs :
  GoodConstraintSet.t -> Coq_wGraph.EdgeSet.t -> Coq_wGraph.EdgeSet.t

val make_graph : (VSet.t * GoodConstraintSet.t) -> Coq_wGraph.t

val leqb_level_n : universes_graph -> coq_Z -> Level.t -> Level.t -> bool

val add_uctx :
  (VSet.t * GoodConstraintSet.t) -> universes_graph -> universes_graph
