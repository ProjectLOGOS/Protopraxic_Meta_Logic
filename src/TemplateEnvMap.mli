open Ast0
open Datatypes
open Kernames
open List0
open Monad_utils

module GlobalEnvMap :
 sig
  type t = { env : Env.global_env; map : Env.global_decl EnvMap.EnvMap.t }

  val env : t -> Env.global_env

  val map : t -> Env.global_decl EnvMap.EnvMap.t

  val lookup_env : t -> kername -> Env.global_decl option

  val lookup_minductive : t -> kername -> Env.mutual_inductive_body option

  val lookup_inductive :
    t -> inductive -> (Env.mutual_inductive_body * Env.one_inductive_body)
    option

  val lookup_constructor :
    t -> inductive -> nat ->
    ((Env.mutual_inductive_body * Env.one_inductive_body) * Env.constructor_body)
    option

  val make : Env.global_env -> t
 end
