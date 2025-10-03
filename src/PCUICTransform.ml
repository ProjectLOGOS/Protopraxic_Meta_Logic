open Ast0
open Byte
open PCUICAst
open PCUICExpandLets
open PCUICProgram
open TemplateToPCUIC
open Bytestring
open Config0

(** val template_to_pcuic_transform :
    checker_flags -> (Env.global_env, global_env_ext_map, Ast0.term, term,
    Ast0.term, term) Transform.Transform.t **)

let template_to_pcuic_transform _ =
  { Transform.Transform.name = (String.String (Coq_x74, (String.String
    (Coq_x65, (String.String (Coq_x6d, (String.String (Coq_x70,
    (String.String (Coq_x6c, (String.String (Coq_x61, (String.String
    (Coq_x74, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x74, (String.String (Coq_x6f, (String.String
    (Coq_x20, (String.String (Coq_x70, (String.String (Coq_x63,
    (String.String (Coq_x75, (String.String (Coq_x69, (String.String
    (Coq_x63, String.EmptyString))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> trans_template_program p) }

(** val pcuic_expand_lets_transform :
    checker_flags -> (global_env_ext_map, term)
    Transform.Transform.self_transform **)

let pcuic_expand_lets_transform _ =
  { Transform.Transform.name = (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x20,
    (String.String (Coq_x65, (String.String (Coq_x78, (String.String
    (Coq_x70, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x69, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x20,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x62, (String.String (Coq_x72,
    (String.String (Coq_x61, (String.String (Coq_x6e, (String.String
    (Coq_x63, (String.String (Coq_x68, (String.String (Coq_x65,
    (String.String (Coq_x73, (String.String (Coq_x2f, (String.String
    (Coq_x63, (String.String (Coq_x6f, (String.String (Coq_x6e,
    (String.String (Coq_x73, (String.String (Coq_x74, (String.String
    (Coq_x72, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x74, (String.String (Coq_x6f, (String.String
    (Coq_x72, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> expand_lets_program p) }
