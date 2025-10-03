open BasicAst
open Datatypes
open EAst
open Kernames
open List0
open Monad_utils

module GlobalContextMap :
 sig
  type t = { global_decls : global_declarations;
             map : global_decl EnvMap.EnvMap.t }

  val global_decls : t -> global_declarations

  val map : t -> global_decl EnvMap.EnvMap.t

  val lookup_env : t -> kername -> global_decl option

  val lookup_minductive : t -> kername -> mutual_inductive_body option

  val lookup_inductive :
    t -> inductive -> (mutual_inductive_body * one_inductive_body) option

  val lookup_constructor :
    t -> inductive -> nat ->
    ((mutual_inductive_body * one_inductive_body) * constructor_body) option

  val lookup_projection :
    t -> projection ->
    (((mutual_inductive_body * one_inductive_body) * constructor_body) * projection_body)
    option

  val lookup_inductive_pars : t -> kername -> nat option

  val lookup_inductive_kind : t -> kername -> recursivity_kind option

  val inductive_isprop_and_pars : t -> inductive -> (bool * nat) option

  val lookup_constructor_pars_args :
    t -> inductive -> nat -> (nat * nat) option

  val make : global_declarations -> t
 end
