open BasicAst
open Datatypes
open EAst
open EAstUtils
open ECSubst
open ELiftSubst
open Kernames
open List0
open MCOption
open MCProd
open Specif
open Monad_utils

type __ = Obj.t

val lookup_env : global_declarations -> kername -> global_decl option

val lookup_constant : global_declarations -> kername -> constant_body option

val lookup_minductive :
  global_declarations -> kername -> mutual_inductive_body option

val lookup_inductive :
  global_declarations -> inductive ->
  (mutual_inductive_body * one_inductive_body) option

val lookup_inductive_pars : global_declarations -> kername -> nat option

val lookup_inductive_kind :
  global_declarations -> kername -> recursivity_kind option

val lookup_constructor :
  global_declarations -> inductive -> nat ->
  ((mutual_inductive_body * one_inductive_body) * constructor_body) option

val lookup_constructor_pars_args :
  global_declarations -> inductive -> nat -> (nat * nat) option

val lookup_projection :
  global_declarations -> projection ->
  (((mutual_inductive_body * one_inductive_body) * constructor_body) * projection_body)
  option

val inductive_isprop_and_pars :
  global_declarations -> inductive -> (bool * nat) option

val constructor_isprop_pars_decl :
  global_declarations -> inductive -> nat ->
  ((bool * nat) * constructor_body) option

val closed_decl : global_decl -> bool

val closed_env : global_declarations -> bool

type extends_prefix = ((kername * global_decl) list, __) sigT

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat * term) option

val cofix_subst : term mfixpoint -> term list

val unfold_cofix : term mfixpoint -> nat -> (nat * term) option

val cunfold_fix : term mfixpoint -> nat -> (nat * term) option

val cunfold_cofix : term mfixpoint -> nat -> (nat * term) option

val is_constructor_app_or_box : term -> bool

val is_nth_constructor_app_or_box : nat -> term list -> bool

val iota_red : nat -> term list -> (name list * term) -> term
