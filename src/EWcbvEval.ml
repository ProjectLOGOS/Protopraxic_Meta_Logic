
type coq_WcbvFlags = { with_prop_case : bool; with_guarded_fix : bool;
                       with_constructor_as_block : bool }

(** val disable_prop_cases : coq_WcbvFlags -> coq_WcbvFlags **)

let disable_prop_cases fl =
  { with_prop_case = false; with_guarded_fix = fl.with_guarded_fix;
    with_constructor_as_block = fl.with_constructor_as_block }

(** val switch_unguarded_fix : coq_WcbvFlags -> coq_WcbvFlags **)

let switch_unguarded_fix fl =
  { with_prop_case = fl.with_prop_case; with_guarded_fix = false;
    with_constructor_as_block = fl.with_constructor_as_block }

(** val default_wcbv_flags : coq_WcbvFlags **)

let default_wcbv_flags =
  { with_prop_case = true; with_guarded_fix = true;
    with_constructor_as_block = false }

(** val opt_wcbv_flags : coq_WcbvFlags **)

let opt_wcbv_flags =
  { with_prop_case = false; with_guarded_fix = true;
    with_constructor_as_block = false }

(** val target_wcbv_flags : coq_WcbvFlags **)

let target_wcbv_flags =
  { with_prop_case = false; with_guarded_fix = false;
    with_constructor_as_block = false }
