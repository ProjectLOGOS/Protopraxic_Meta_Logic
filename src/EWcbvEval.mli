
type coq_WcbvFlags = { with_prop_case : bool; with_guarded_fix : bool;
                       with_constructor_as_block : bool }

val disable_prop_cases : coq_WcbvFlags -> coq_WcbvFlags

val switch_unguarded_fix : coq_WcbvFlags -> coq_WcbvFlags

val default_wcbv_flags : coq_WcbvFlags

val opt_wcbv_flags : coq_WcbvFlags

val target_wcbv_flags : coq_WcbvFlags
