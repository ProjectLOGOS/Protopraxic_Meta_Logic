
type checker_flags = { check_univs : bool; prop_sub_type : bool;
                       indices_matter : bool;
                       lets_in_constructor_types : bool }

(** val extraction_checker_flags : checker_flags **)

let extraction_checker_flags =
  { check_univs = true; prop_sub_type = false; indices_matter = false;
    lets_in_constructor_types = false }
