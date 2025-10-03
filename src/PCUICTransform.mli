open Ast0
open Byte
open PCUICAst
open PCUICExpandLets
open PCUICProgram
open TemplateToPCUIC
open Bytestring
open Config0

val template_to_pcuic_transform :
  checker_flags -> (Env.global_env, global_env_ext_map, Ast0.term, term,
  Ast0.term, term) Transform.Transform.t

val pcuic_expand_lets_transform :
  checker_flags -> (global_env_ext_map, term)
  Transform.Transform.self_transform
