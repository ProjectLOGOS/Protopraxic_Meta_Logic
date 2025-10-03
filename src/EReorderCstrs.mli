open BasicAst
open Datatypes
open EAst
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCList
open MCOption
open MCProd
open PeanoNat
open ReflectEq
open Monad_utils

val lookup_inductive_assoc :
  (inductive * 'a1) list -> inductive -> 'a1 option

val find_tag : nat list -> nat -> nat -> nat option

val new_tag : nat list -> nat -> nat option

val reorder_list_opt : nat list -> 'a1 list -> 'a1 list option

val reorder_list : nat list -> 'a1 list -> 'a1 list

val one_to_one_map : nat -> nat list -> bool

val wf_tags : nat list -> bool

val lookup_constructor_mapping :
  inductives_mapping -> inductive -> nat -> nat option

val lookup_constructor_ordinal : inductives_mapping -> inductive -> nat -> nat

val reorder_branches :
  inductives_mapping -> inductive -> (name list * term) list -> (name
  list * term) list

val reorder : inductives_mapping -> term -> term

val reorder_constant_decl :
  inductives_mapping -> constant_body -> E.constant_body

val reorder_one_ind :
  inductives_mapping -> kername -> nat -> one_inductive_body ->
  one_inductive_body

val reorder_inductive_decl :
  inductives_mapping -> kername -> mutual_inductive_body ->
  E.mutual_inductive_body

val reorder_decl :
  inductives_mapping -> (kername * global_decl) -> kername * global_decl

val reorder_env :
  inductives_mapping -> (kername * global_decl) list ->
  (kername * global_decl) list

val reorder_program : inductives_mapping -> program -> program

val wf_tags_list : nat list -> nat -> bool
