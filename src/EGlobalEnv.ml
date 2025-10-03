open BasicAst
open Datatypes
open EAst
open EAstUtils
open ECSubst
open ELiftSubst
open Kernames
open List0
open MCOption
open MCProd
open Specif
open Monad_utils

type __ = Obj.t

(** val lookup_env : global_declarations -> kername -> global_decl option **)

let rec lookup_env _UU03a3_ id =
  match _UU03a3_ with
  | [] -> None
  | hd :: tl ->
    if Kername.reflect_kername id (fst hd)
    then Some (snd hd)
    else lookup_env tl id

(** val lookup_constant :
    global_declarations -> kername -> constant_body option **)

let lookup_constant _UU03a3_ kn =
  bind (Obj.magic option_monad) (Obj.magic lookup_env _UU03a3_ kn)
    (fun decl ->
    match decl with
    | ConstantDecl cdecl -> ret (Obj.magic option_monad) cdecl
    | InductiveDecl _ -> None)

(** val lookup_minductive :
    global_declarations -> kername -> mutual_inductive_body option **)

let lookup_minductive _UU03a3_ kn =
  bind (Obj.magic option_monad) (Obj.magic lookup_env _UU03a3_ kn)
    (fun decl ->
    match decl with
    | ConstantDecl _ -> None
    | InductiveDecl mdecl -> ret (Obj.magic option_monad) mdecl)

(** val lookup_inductive :
    global_declarations -> inductive ->
    (mutual_inductive_body * one_inductive_body) option **)

let lookup_inductive _UU03a3_ kn =
  bind (Obj.magic option_monad)
    (Obj.magic lookup_minductive _UU03a3_ kn.inductive_mind) (fun mdecl ->
    bind (Obj.magic option_monad)
      (nth_error (Obj.magic mdecl.ind_bodies) kn.inductive_ind) (fun idecl ->
      ret (Obj.magic option_monad) (mdecl, idecl)))

(** val lookup_inductive_pars :
    global_declarations -> kername -> nat option **)

let lookup_inductive_pars _UU03a3_ kn =
  bind (Obj.magic option_monad) (Obj.magic lookup_minductive _UU03a3_ kn)
    (fun mdecl -> ret (Obj.magic option_monad) mdecl.ind_npars)

(** val lookup_inductive_kind :
    global_declarations -> kername -> recursivity_kind option **)

let lookup_inductive_kind _UU03a3_ kn =
  bind (Obj.magic option_monad) (Obj.magic lookup_minductive _UU03a3_ kn)
    (fun mdecl -> ret (Obj.magic option_monad) mdecl.ind_finite)

(** val lookup_constructor :
    global_declarations -> inductive -> nat ->
    ((mutual_inductive_body * one_inductive_body) * constructor_body) option **)

let lookup_constructor _UU03a3_ kn c =
  bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ kn)
    (fun x ->
    let (mdecl, idecl) = x in
    bind (Obj.magic option_monad) (nth_error (Obj.magic idecl.ind_ctors) c)
      (fun cdecl -> ret (Obj.magic option_monad) ((mdecl, idecl), cdecl)))

(** val lookup_constructor_pars_args :
    global_declarations -> inductive -> nat -> (nat * nat) option **)

let lookup_constructor_pars_args _UU03a3_ kn c =
  bind (Obj.magic option_monad) (Obj.magic lookup_constructor _UU03a3_ kn c)
    (fun x ->
    let (y, cdecl) = x in
    let (mdecl, _) = y in
    ret (Obj.magic option_monad) (mdecl.ind_npars, cdecl.cstr_nargs))

(** val lookup_projection :
    global_declarations -> projection ->
    (((mutual_inductive_body * one_inductive_body) * constructor_body) * projection_body)
    option **)

let lookup_projection _UU03a3_ p =
  bind (Obj.magic option_monad)
    (Obj.magic lookup_constructor _UU03a3_ p.proj_ind O) (fun x ->
    let (y, cdecl) = x in
    let (mdecl, idecl) = y in
    bind (Obj.magic option_monad)
      (nth_error (Obj.magic idecl.ind_projs) p.proj_arg) (fun pdecl ->
      ret (Obj.magic option_monad) (((mdecl, idecl), cdecl), pdecl)))

(** val inductive_isprop_and_pars :
    global_declarations -> inductive -> (bool * nat) option **)

let inductive_isprop_and_pars _UU03a3_ ind =
  bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ ind)
    (fun x ->
    let (mdecl, idecl) = x in
    ret (Obj.magic option_monad) (idecl.ind_propositional, mdecl.ind_npars))

(** val constructor_isprop_pars_decl :
    global_declarations -> inductive -> nat ->
    ((bool * nat) * constructor_body) option **)

let constructor_isprop_pars_decl _UU03a3_ ind c =
  bind (Obj.magic option_monad) (Obj.magic lookup_constructor _UU03a3_ ind c)
    (fun x ->
    let (y, cdecl) = x in
    let (mdecl, idecl) = y in
    ret (Obj.magic option_monad) ((idecl.ind_propositional, mdecl.ind_npars),
      cdecl))

(** val closed_decl : global_decl -> bool **)

let closed_decl = function
| ConstantDecl cb -> option_default (closedn O) cb true
| InductiveDecl _ -> true

(** val closed_env : global_declarations -> bool **)

let closed_env _UU03a3_ =
  forallb (test_snd closed_decl) _UU03a3_

type extends_prefix = ((kername * global_decl) list, __) sigT

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (fix_subst mfix) O d.dbody))
  | None -> None

(** val cofix_subst : term mfixpoint -> term list **)

let cofix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tCoFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_cofix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_cofix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (cofix_subst mfix) O d.dbody))
  | None -> None

(** val cunfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let cunfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (substl (fix_subst mfix) d.dbody))
  | None -> None

(** val cunfold_cofix : term mfixpoint -> nat -> (nat * term) option **)

let cunfold_cofix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (substl (cofix_subst mfix) d.dbody))
  | None -> None

(** val is_constructor_app_or_box : term -> bool **)

let is_constructor_app_or_box t = match t with
| Coq_tBox -> true
| _ ->
  let (f, _) = decompose_app t in
  (match f with
   | Coq_tConstruct (_, _, _) -> true
   | _ -> false)

(** val is_nth_constructor_app_or_box : nat -> term list -> bool **)

let is_nth_constructor_app_or_box n ts =
  match nth_error ts n with
  | Some a -> is_constructor_app_or_box a
  | None -> false

(** val iota_red : nat -> term list -> (name list * term) -> term **)

let iota_red npar args br =
  substl (rev (skipn npar args)) (snd br)
