open Ast0
open Datatypes
open Kernames
open Universes0

(** val type_of_constructor :
    Env.mutual_inductive_body -> Env.constructor_body -> (inductive * nat) ->
    Level.t list -> term **)

let type_of_constructor mdecl cdecl c u =
  let mind = (fst c).inductive_mind in
  subst (inds mind u (Env.ind_bodies mdecl)) O
    (subst_instance subst_instance_constr u (Env.cstr_type cdecl))
