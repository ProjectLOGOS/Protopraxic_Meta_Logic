open BasicAst
open Byte
open Datatypes
open EAst
open EAstUtils
open EGlobalEnv
open EPrimitive
open Kernames
open List0
open MCString
open Nat0
open Show
open Specif
open Universes0
open Bytestring

val lookup_ind_decl :
  global_declarations -> kername -> nat -> one_inductive_body option

val is_fresh : context -> ident -> bool

val name_from_term : term -> String.t

val fresh_id_from : context -> nat -> String.t -> String.t

val fresh_name : context -> name -> term -> name

module PrintTermTree :
 sig
  val print_def : ('a1 -> Tree.t) -> 'a1 def -> Tree.t

  val print_defs :
    (context -> bool -> bool -> term -> Tree.t) -> context_decl list -> term
    mfixpoint -> Tree.t

  val print_prim : (term -> Tree.t) -> term prim_val -> Tree.t

  val print_term :
    global_declarations -> context -> bool -> bool -> term -> Tree.t

  val pr : global_declarations -> term -> Tree.t

  val print_constant_body :
    global_declarations -> kername -> constant_body -> Tree.t

  val pr_allowed_elim : allowed_eliminations -> String.t

  val print_one_inductive_body : nat -> one_inductive_body -> Tree.t

  val print_recursivity_kind : recursivity_kind -> String.t

  val print_inductive_body : mutual_inductive_body -> Tree.t

  val print_decl : global_declarations -> (kername * global_decl) -> Tree.t

  val print_global_context : global_declarations -> Tree.t

  val print_program : program -> Tree.t
 end

val print_program : program -> String.t
