open Ast0
open Byte
open Datatypes
open TemplateEnvMap
open Bytestring
open Config0

type template_program = Env.program

type template_program_env = GlobalEnvMap.t * term

val make_template_program_env :
  checker_flags -> template_program -> template_program_env

val build_template_program_env :
  checker_flags -> (Env.global_env, GlobalEnvMap.t, term, term, term, term)
  Transform.Transform.t
