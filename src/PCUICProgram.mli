open Datatypes
open Kernames
open List0
open PCUICAst
open Universes0

type global_env_map = { trans_env_env : PCUICEnvironment.global_env;
                        trans_env_map : PCUICEnvironment.global_decl
                                        EnvMap.EnvMap.t }

val build_global_env_map : PCUICEnvironment.global_env -> global_env_map

type global_env_ext_map = global_env_map * universes_decl

type pcuic_program = global_env_ext_map * term

val global_env_ext_map_global_env_ext :
  global_env_ext_map -> PCUICEnvironment.global_env_ext

val global_env_ext_map_global_env_map : global_env_ext_map -> global_env_map

module TransLookup :
 sig
  val lookup_minductive :
    global_env_map -> kername -> PCUICEnvironment.mutual_inductive_body option

  val lookup_inductive :
    global_env_map -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option
 end
