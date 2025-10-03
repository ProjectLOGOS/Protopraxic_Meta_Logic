
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

val all_primitive_flags : coq_EPrimitiveFlags

val all_term_flags : coq_ETermFlags

val all_env_flags : coq_EEnvFlags
