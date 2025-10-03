
type coq_EPrimitiveFlags = { has_primint : bool; has_primfloat : bool;
                             has_primstring : bool; has_primarray : bool }

type coq_ETermFlags = { has_tBox : bool; has_tRel : bool; has_tVar : 
                        bool; has_tEvar : bool; has_tLambda : bool;
                        has_tLetIn : bool; has_tApp : bool;
                        has_tConst : bool; has_tConstruct : bool;
                        has_tCase : bool; has_tProj : bool; has_tFix : 
                        bool; has_tCoFix : bool;
                        has_tPrim : coq_EPrimitiveFlags;
                        has_tLazy_Force : bool }

type coq_EEnvFlags = { has_axioms : bool; has_cstr_params : bool;
                       term_switches : coq_ETermFlags; cstr_as_blocks : 
                       bool }

(** val all_primitive_flags : coq_EPrimitiveFlags **)

let all_primitive_flags =
  { has_primint = true; has_primfloat = true; has_primstring = true;
    has_primarray = true }

(** val all_term_flags : coq_ETermFlags **)

let all_term_flags =
  { has_tBox = true; has_tRel = true; has_tVar = true; has_tEvar = true;
    has_tLambda = true; has_tLetIn = true; has_tApp = true; has_tConst =
    true; has_tConstruct = true; has_tCase = true; has_tProj = true;
    has_tFix = true; has_tCoFix = true; has_tPrim = all_primitive_flags;
    has_tLazy_Force = true }

(** val all_env_flags : coq_EEnvFlags **)

let all_env_flags =
  { has_axioms = true; has_cstr_params = true; term_switches =
    all_term_flags; cstr_as_blocks = false }
