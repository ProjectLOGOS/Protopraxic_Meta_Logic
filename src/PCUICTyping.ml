open Datatypes
open Kernames
open PCUICAst
open PCUICPrimitive
open Primitive
open Specif
open Universes0

(** val type_of_constructor :
    PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.constructor_body -> (inductive * nat) -> Level.t list ->
    term **)

let type_of_constructor mdecl cdecl c u =
  let mind = (fst c).inductive_mind in
  subst (inds mind u (PCUICEnvironment.ind_bodies mdecl)) O
    (subst_instance subst_instance_constr u
      (PCUICEnvironment.cstr_type cdecl))

type coq_FixCoFix =
| Fix
| CoFix

(** val prim_type : term prim_val -> kername -> term **)

let prim_type p cst =
  let Coq_existT (x, p0) = p in
  (match x with
   | Coq_primArray ->
     (match p0 with
      | Coq_primArrayModel a ->
        Coq_tApp ((Coq_tConst (cst, (a.array_level :: []))), a.array_type)
      | _ -> assert false (* absurd case *))
   | _ -> Coq_tConst (cst, []))
