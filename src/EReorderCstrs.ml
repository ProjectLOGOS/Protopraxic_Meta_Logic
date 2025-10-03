open BasicAst
open Datatypes
open EAst
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCList
open MCOption
open MCProd
open PeanoNat
open ReflectEq
open Monad_utils

(** val lookup_inductive_assoc :
    (inductive * 'a1) list -> inductive -> 'a1 option **)

let rec lookup_inductive_assoc _UU03a3_ kn =
  match _UU03a3_ with
  | [] -> None
  | d :: tl ->
    if reflect_eq_inductive kn (fst d)
    then Some (snd d)
    else lookup_inductive_assoc tl kn

(** val find_tag : nat list -> nat -> nat -> nat option **)

let rec find_tag l idx tag =
  match l with
  | [] -> None
  | tag' :: tags ->
    if reflect_nat tag tag' then Some idx else find_tag tags (S idx) tag

(** val new_tag : nat list -> nat -> nat option **)

let new_tag tags tag =
  find_tag tags O tag

(** val reorder_list_opt : nat list -> 'a1 list -> 'a1 list option **)

let reorder_list_opt tags brs =
  mapopt (nth_error brs) tags

(** val reorder_list : nat list -> 'a1 list -> 'a1 list **)

let reorder_list tags l =
  option_get l (reorder_list_opt tags l)

(** val one_to_one_map : nat -> nat list -> bool **)

let rec one_to_one_map n l =
  match n with
  | O -> reflect_list reflect_nat l []
  | S n0 ->
    (&&) (existsb (fun x -> reflect_nat x n0) l)
      (one_to_one_map n0 (remove Nat.eq_dec n0 l))

(** val wf_tags : nat list -> bool **)

let wf_tags l =
  (&&) (forallb (fun n -> Nat.ltb n (length l)) l)
    (one_to_one_map (length l) l)

(** val lookup_constructor_mapping :
    inductives_mapping -> inductive -> nat -> nat option **)

let lookup_constructor_mapping mapping i c =
  bind (Obj.magic option_monad)
    (lookup_inductive_assoc (Obj.magic mapping) i) (fun x ->
    let (_, tags) = x in new_tag tags c)

(** val lookup_constructor_ordinal :
    inductives_mapping -> inductive -> nat -> nat **)

let lookup_constructor_ordinal mapping i c =
  match lookup_constructor_mapping mapping i c with
  | Some c' -> c'
  | None -> c

(** val reorder_branches :
    inductives_mapping -> inductive -> (name list * term) list -> (name
    list * term) list **)

let reorder_branches mapping i brs =
  match lookup_inductive_assoc mapping i with
  | Some p -> let (_, tags) = p in reorder_list tags brs
  | None -> brs

(** val reorder : inductives_mapping -> term -> term **)

let rec reorder mapping = function
| Coq_tEvar (n, l) -> Coq_tEvar (n, (map (reorder mapping) l))
| Coq_tLambda (na, t0) -> Coq_tLambda (na, (reorder mapping t0))
| Coq_tLetIn (na, b, t0) ->
  Coq_tLetIn (na, (reorder mapping b), (reorder mapping t0))
| Coq_tApp (u, v) -> Coq_tApp ((reorder mapping u), (reorder mapping v))
| Coq_tConstruct (ind, n, args) ->
  Coq_tConstruct (ind, (lookup_constructor_ordinal mapping ind n),
    (map (reorder mapping) args))
| Coq_tCase (indn, c, brs) ->
  Coq_tCase (indn, (reorder mapping c),
    (reorder_branches mapping (fst indn) (map (on_snd (reorder mapping)) brs)))
| Coq_tProj (p, c) -> Coq_tProj (p, (reorder mapping c))
| Coq_tFix (mfix, idx) ->
  Coq_tFix ((map (map_def (reorder mapping)) mfix), idx)
| Coq_tCoFix (mfix, idx) ->
  Coq_tCoFix ((map (map_def (reorder mapping)) mfix), idx)
| Coq_tPrim prim -> Coq_tPrim (map_prim (reorder mapping) prim)
| Coq_tLazy t0 -> Coq_tLazy (reorder mapping t0)
| Coq_tForce t0 -> Coq_tForce (reorder mapping t0)
| x -> x

(** val reorder_constant_decl :
    inductives_mapping -> constant_body -> E.constant_body **)

let reorder_constant_decl mapping cb =
  option_map (reorder mapping) cb

(** val reorder_one_ind :
    inductives_mapping -> kername -> nat -> one_inductive_body ->
    one_inductive_body **)

let reorder_one_ind mapping kn i oib =
  match lookup_inductive_assoc mapping { inductive_mind = kn; inductive_ind =
          i } with
  | Some p ->
    let (_, tags) = p in
    { E.ind_name = oib.ind_name; E.ind_propositional = oib.ind_propositional;
    E.ind_kelim = oib.ind_kelim; E.ind_ctors =
    (reorder_list tags oib.ind_ctors); E.ind_projs = oib.ind_projs }
  | None -> oib

(** val reorder_inductive_decl :
    inductives_mapping -> kername -> mutual_inductive_body ->
    E.mutual_inductive_body **)

let reorder_inductive_decl mapping kn idecl =
  { E.ind_finite = idecl.ind_finite; E.ind_npars = idecl.ind_npars;
    E.ind_bodies = (mapi (reorder_one_ind mapping kn) idecl.ind_bodies) }

(** val reorder_decl :
    inductives_mapping -> (kername * global_decl) -> kername * global_decl **)

let reorder_decl mapping d =
  let d' =
    match snd d with
    | ConstantDecl cb -> ConstantDecl (reorder_constant_decl mapping cb)
    | InductiveDecl idecl ->
      InductiveDecl (reorder_inductive_decl mapping (fst d) idecl)
  in
  ((fst d), d')

(** val reorder_env :
    inductives_mapping -> (kername * global_decl) list ->
    (kername * global_decl) list **)

let reorder_env mapping _UU03a3_ =
  map (reorder_decl mapping) _UU03a3_

(** val reorder_program : inductives_mapping -> program -> program **)

let reorder_program mapping p =
  ((reorder_env mapping (fst p)), (reorder mapping (snd p)))

(** val wf_tags_list : nat list -> nat -> bool **)

let wf_tags_list tags n =
  (&&) (reflect_nat (length tags) n) (wf_tags tags)
