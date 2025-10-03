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

type valuation = { valuation_mono : (String.t -> positive);
                   valuation_poly : (nat -> nat) }

type 'a coq_Evaluable = valuation -> 'a -> nat

val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> nat

module Level :
 sig
  type t_ =
  | Coq_lzero
  | Coq_level of String.t
  | Coq_lvar of nat

  val t__rect : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage

  type t = t_

  val is_set : t -> bool

  val is_var : t -> bool

  val coq_Evaluable : t coq_Evaluable

  val compare : t -> t -> comparison

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val eq_level : t_ -> t_ -> bool

  val reflect_level : t coq_ReflectEq

  val eqb : t_ -> t_ -> bool

  val eqb_spec : t -> t -> reflect

  val eq_dec : t -> t -> bool
 end

module LevelSet :
 sig
  module Raw :
   sig
    type elt = Level.t_

    type tree =
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

    type enumeration =
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

    type triple = { t_left : t; t_in : bool; t_right : t }

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

    type coq_R_bal =
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

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * Level.t_ * 
       tree * (t * elt) * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree * Level.t_ * tree
       * Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
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

module LevelSetOrdProp :
 sig
  module ME :
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

  module ML :
   sig
   end

  module P :
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

  val gtb : Level.t_ -> Level.t_ -> bool

  val leb : Level.t_ -> Level.t_ -> bool

  val elements_lt : Level.t_ -> LevelSet.t -> Level.t_ list

  val elements_ge : Level.t_ -> LevelSet.t -> Level.t_ list

  val set_induction_max :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 -> Level.t_
    -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

  val set_induction_min :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 -> Level.t_
    -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1
 end

module LevelSetProp :
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
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t -> __ ->
    'a2) -> (LevelSet.elt -> 'a1 -> LevelSet.t -> LevelSet.t -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t ->
    LevelSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 ->
    LevelSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> 'a2 -> (LevelSet.elt
    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

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
    (LevelSet.t -> LevelSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.elt ->
    LevelSet.t -> __ -> 'a1 -> 'a1) -> LevelSet.t -> 'a1

  val cardinal_inv_2 : LevelSet.t -> nat -> LevelSet.elt

  val cardinal_inv_2b : LevelSet.t -> LevelSet.elt
 end

module LevelExpr :
 sig
  type t = Level.t * nat

  val coq_Evaluable : t coq_Evaluable

  val succ : t -> Level.t * nat

  val get_level : t -> Level.t

  val get_noprop : t -> Level.t option

  val is_level : t -> bool

  val make : Level.t -> t

  val set : t

  val type1 : t

  val compare : t -> t -> comparison

  val reflect_t : t coq_ReflectEq

  val eq_dec : t -> t -> bool
 end

module LevelExprSet :
 sig
  module E :
   sig
    type t = Level.t * nat

    val compare : (Level.t * nat) -> (Level.t * nat) -> comparison

    val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Level.t * nat

          val compare : (Level.t * nat) -> (Level.t * nat) -> comparison

          val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool
         end

        module TO :
         sig
          type t = Level.t * nat

          val compare : (Level.t * nat) -> (Level.t * nat) -> comparison

          val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool
         end
       end

      val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool

      val lt_dec : (Level.t * nat) -> (Level.t * nat) -> bool

      val eqb : (Level.t * nat) -> (Level.t * nat) -> bool
     end

    module ML :
     sig
     end

    type elt = Level.t * nat

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : (Level.t * nat) -> (Level.t * nat) list -> bool

    val add : (Level.t * nat) -> (Level.t * nat) list -> (Level.t * nat) list

    val singleton : elt -> elt list

    val remove : (Level.t * nat) -> (Level.t * nat) list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : (Level.t * nat) list -> (Level.t * nat) list -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val choose : t -> elt option

    val compare : (Level.t * nat) list -> (Level.t * nat) list -> comparison

    val inf : (Level.t * nat) -> (Level.t * nat) list -> bool

    val isok : (Level.t * nat) list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Level.t * nat

            val compare : (Level.t * nat) -> (Level.t * nat) -> comparison

            val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool
           end

          module TO :
           sig
            type t = Level.t * nat

            val compare : (Level.t * nat) -> (Level.t * nat) -> comparison

            val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool
           end
         end

        val eq_dec : (Level.t * nat) -> (Level.t * nat) -> bool

        val lt_dec : (Level.t * nat) -> (Level.t * nat) -> bool

        val eqb : (Level.t * nat) -> (Level.t * nat) -> bool
       end
     end
   end

  type elt = Level.t * nat

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

type nonEmptyLevelExprSet =
  LevelExprSet.t
  (* singleton inductive, whose constructor was Build_nonEmptyLevelExprSet *)

module NonEmptySetFacts :
 sig
  val singleton : LevelExpr.t -> nonEmptyLevelExprSet

  val add : LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet

  val add_list :
    LevelExpr.t list -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet

  val to_nonempty_list :
    nonEmptyLevelExprSet -> LevelExpr.t * LevelExpr.t list

  val map :
    (LevelExpr.t -> LevelExpr.t) -> nonEmptyLevelExprSet ->
    nonEmptyLevelExprSet

  val non_empty_union :
    nonEmptyLevelExprSet -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet
 end

module Universe :
 sig
  type t = nonEmptyLevelExprSet

  val make : LevelExpr.t -> t

  val succ : t -> t

  val sup : t -> t -> t
 end

module ConstraintType :
 sig
  type t_ =
  | Le of coq_Z
  | Eq

  val t__rect : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1

  val t__rec : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1

  val t__eqdec : t_ -> t_ -> t_ dec_eq

  val t__EqDec : t_ coq_EqDec

  type t = t_

  val compare : t -> t -> comparison
 end

module UnivConstraint :
 sig
  type t = (Level.t * ConstraintType.t) * Level.t

  val make : Level.t -> ConstraintType.t -> Level.t -> t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module ConstraintSet :
 sig
  module Raw :
   sig
    type elt = (Level.t * ConstraintType.t) * Level.t

    type tree =
    | Leaf
    | Node of Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t)
       * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : ((Level.t * ConstraintType.t) * Level.t) -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux :
      ((Level.t * ConstraintType.t) * Level.t) list -> tree ->
      ((Level.t * ConstraintType.t) * Level.t) list

    val elements : tree -> ((Level.t * ConstraintType.t) * Level.t) list

    val rev_elements_aux :
      ((Level.t * ConstraintType.t) * Level.t) list -> tree ->
      ((Level.t * ConstraintType.t) * Level.t) list

    val rev_elements : tree -> ((Level.t * ConstraintType.t) * Level.t) list

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
      ((Level.t * ConstraintType.t) * Level.t) -> (enumeration -> comparison)
      -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl :
      (tree -> bool) -> ((Level.t * ConstraintType.t) * Level.t) -> tree ->
      bool

    val subsetr :
      (tree -> bool) -> ((Level.t * ConstraintType.t) * Level.t) -> tree ->
      bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Z_as_Int.t

    val singleton : ((Level.t * ConstraintType.t) * Level.t) -> tree

    val create : t -> ((Level.t * ConstraintType.t) * Level.t) -> t -> tree

    val assert_false :
      t -> ((Level.t * ConstraintType.t) * Level.t) -> t -> tree

    val bal : t -> ((Level.t * ConstraintType.t) * Level.t) -> t -> tree

    val add : ((Level.t * ConstraintType.t) * Level.t) -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : ((Level.t * ConstraintType.t) * Level.t) -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : ((Level.t * ConstraintType.t) * Level.t) -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : ((Level.t * ConstraintType.t) * Level.t) -> tree -> bool

    val gtb_tree : ((Level.t * ConstraintType.t) * Level.t) -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = (Level.t * ConstraintType.t) * Level.t

          val compare :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> comparison

          val eq_dec :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> bool
         end

        module TO :
         sig
          type t = (Level.t * ConstraintType.t) * Level.t

          val compare :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> comparison

          val eq_dec :
            ((Level.t * ConstraintType.t) * Level.t) ->
            ((Level.t * ConstraintType.t) * Level.t) -> bool
         end
       end

      val eq_dec :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool

      val lt_dec :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool

      val eqb :
        ((Level.t * ConstraintType.t) * Level.t) ->
        ((Level.t * ConstraintType.t) * Level.t) -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (Level.t * ConstraintType.t) * Level.t

            val compare :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> comparison

            val eq_dec :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> bool
           end

          module TO :
           sig
            type t = (Level.t * ConstraintType.t) * Level.t

            val compare :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> comparison

            val eq_dec :
              ((Level.t * ConstraintType.t) * Level.t) ->
              ((Level.t * ConstraintType.t) * Level.t) -> bool
           end
         end

        val eq_dec :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool

        val lt_dec :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool

        val eqb :
          ((Level.t * ConstraintType.t) * Level.t) ->
          ((Level.t * ConstraintType.t) * Level.t) -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * ((Level.t * ConstraintType.t) * Level.t) * t
    | R_bal_1 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree
    | R_bal_2 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree
    | R_bal_3 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t)
       * tree
    | R_bal_4 of t * ((Level.t * ConstraintType.t) * Level.t) * t
    | R_bal_5 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree
    | R_bal_6 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree
    | R_bal_7 of t * ((Level.t * ConstraintType.t) * Level.t) * t
       * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t) * 
       tree * Z_as_Int.t * tree * ((Level.t * ConstraintType.t) * Level.t)
       * tree
    | R_bal_8 of t * ((Level.t * ConstraintType.t) * Level.t) * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * (t * elt)
       * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree
    | R_union_2 of tree * tree * Z_as_Int.t * tree
       * ((Level.t * ConstraintType.t) * Level.t) * tree * Z_as_Int.t * 
       tree * ((Level.t * ConstraintType.t) * Level.t) * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = (Level.t * ConstraintType.t) * Level.t

    val compare :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) -> comparison

    val eq_dec :
      ((Level.t * ConstraintType.t) * Level.t) ->
      ((Level.t * ConstraintType.t) * Level.t) -> bool
   end

  type elt = (Level.t * ConstraintType.t) * Level.t

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

module Instance :
 sig
  type t = Level.t list

  val empty : t
 end

module UContext :
 sig
  type t = name list * (Instance.t * ConstraintSet.t)

  val instance : t -> Instance.t
 end

module AUContext :
 sig
  type t = name list * ConstraintSet.t

  val repr : t -> UContext.t

  val levels : t -> LevelSet.t
 end

module ContextSet :
 sig
  type t = LevelSet.t * ConstraintSet.t

  val levels : t -> LevelSet.t

  val constraints : t -> ConstraintSet.t

  val empty : t

  val union : t -> t -> t
 end

module Variance :
 sig
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

type universes_decl =
| Monomorphic_ctx
| Polymorphic_ctx of AUContext.t

val levels_of_udecl : universes_decl -> LevelSet.t

val constraints_of_udecl : universes_decl -> ConstraintSet.t

module Sort :
 sig
  type 'univ t_ =
  | Coq_sProp
  | Coq_sSProp
  | Coq_sType of 'univ

  type t = Universe.t t_

  type family =
  | Coq_fSProp
  | Coq_fProp
  | Coq_fType

  val is_prop : 'a1 t_ -> bool

  val is_propositional : 'a1 t_ -> bool

  val type0 : t

  val super_ : 'a1 -> ('a1 -> 'a1) -> 'a1 t_ -> 'a1 t_

  val super : t -> t

  val sup_ : ('a1 -> 'a1 -> 'a1) -> 'a1 t_ -> 'a1 t_ -> 'a1 t_

  val sort_of_product_ : ('a1 -> 'a1 -> 'a1) -> 'a1 t_ -> 'a1 t_ -> 'a1 t_

  val sort_of_product : t -> t -> t

  val to_family : 'a1 t_ -> family
 end

type allowed_eliminations =
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

val subst_instance : 'a1 coq_UnivSubst -> Instance.t -> 'a1 -> 'a1

val subst_instance_level : Level.t coq_UnivSubst

val subst_instance_level_expr : LevelExpr.t coq_UnivSubst

val subst_instance_universe : Universe.t coq_UnivSubst

val subst_instance_sort : Sort.t coq_UnivSubst

val subst_instance_instance : Instance.t coq_UnivSubst

val closedu_level : nat -> Level.t -> bool

val closedu_level_expr : nat -> LevelExpr.t -> bool

val closedu_universe : nat -> Universe.t -> bool

val closedu_sort : nat -> Sort.t -> bool

val closedu_instance : nat -> Instance.t -> bool

val string_of_level : Level.t -> String.t

val string_of_universe_instance : Level.t list -> String.t

val abstract_instance : universes_decl -> Instance.t
