open BasicAst
open Basics
open Datatypes
open EAst
open EPretty
open Kernames
open List0
open Universes0
open Bytestring

type box_type =
| TBox
| TAny
| TArr of box_type * box_type
| TApp of box_type * box_type
| TVar of nat
| TInd of inductive
| TConst of kername

val box_type_rect :
  'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
  'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
  (kername -> 'a1) -> box_type -> 'a1

val box_type_rec :
  'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
  'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
  (kername -> 'a1) -> box_type -> 'a1

val decompose_arr : box_type -> box_type list * box_type

val can_have_args : box_type -> bool

val mkTApps : box_type -> box_type list -> box_type

type constant_body = { cst_type : (name list * box_type);
                       cst_body : term option }

val cst_type : constant_body -> name list * box_type

val cst_body : constant_body -> term option

type type_var_info = { tvar_name : name; tvar_is_logical : bool;
                       tvar_is_arity : bool; tvar_is_sort : bool }

val tvar_name : type_var_info -> name

val tvar_is_logical : type_var_info -> bool

val tvar_is_arity : type_var_info -> bool

val tvar_is_sort : type_var_info -> bool

type one_inductive_body = { ind_name : ident; ind_propositional : bool;
                            ind_kelim : allowed_eliminations;
                            ind_type_vars : type_var_info list;
                            ind_ctors : ((ident * (name * box_type)
                                        list) * nat) list;
                            ind_projs : (ident * box_type) list }

val ind_name : one_inductive_body -> ident

val ind_propositional : one_inductive_body -> bool

val ind_kelim : one_inductive_body -> allowed_eliminations

val ind_type_vars : one_inductive_body -> type_var_info list

val ind_ctors :
  one_inductive_body -> ((ident * (name * box_type) list) * nat) list

val ind_projs : one_inductive_body -> (ident * box_type) list

type mutual_inductive_body = { ind_finite : recursivity_kind;
                               ind_npars : nat;
                               ind_bodies : one_inductive_body list }

val ind_finite : mutual_inductive_body -> recursivity_kind

val ind_npars : mutual_inductive_body -> nat

val ind_bodies : mutual_inductive_body -> one_inductive_body list

type global_decl =
| ConstantDecl of constant_body
| InductiveDecl of mutual_inductive_body
| TypeAliasDecl of (type_var_info list * box_type) option

val global_decl_rect :
  (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> ((type_var_info
  list * box_type) option -> 'a1) -> global_decl -> 'a1

val global_decl_rec :
  (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> ((type_var_info
  list * box_type) option -> 'a1) -> global_decl -> 'a1

type global_env = ((kername * bool) * global_decl) list

val lookup_env : global_env -> kername -> global_decl option

val lookup_constant : global_env -> kername -> constant_body option

val lookup_minductive : global_env -> kername -> mutual_inductive_body option

val lookup_inductive : global_env -> inductive -> one_inductive_body option

val lookup_constructor :
  global_env -> inductive -> nat -> ((ident * (name * box_type) list) * nat)
  option

val lookup_constructor_full :
  global_env -> inductive -> nat ->
  ((mutual_inductive_body * one_inductive_body) * ((ident * (name * box_type)
  list) * nat)) option

val trans_cst : constant_body -> EAst.constant_body

val trans_ctors :
  ((ident * (name * box_type) list) * nat) list -> constructor_body list

val trans_oib : one_inductive_body -> EAst.one_inductive_body

val trans_mib : mutual_inductive_body -> EAst.mutual_inductive_body

val trans_global_decl : global_decl -> EAst.global_decl

val trans_env : global_env -> global_declarations

val print_term : global_env -> term -> String.t
