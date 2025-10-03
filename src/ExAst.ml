open BasicAst
open Basics
open Datatypes
open EAst
open EPretty
open Kernames
open List0
open Universes0
open Bytestring

type box_type =
| TBox
| TAny
| TArr of box_type * box_type
| TApp of box_type * box_type
| TVar of nat
| TInd of inductive
| TConst of kername

(** val box_type_rect :
    'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
    'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
    (kername -> 'a1) -> box_type -> 'a1 **)

let rec box_type_rect f f0 f1 f2 f3 f4 f5 = function
| TBox -> f
| TAny -> f0
| TArr (dom, codom) ->
  f1 dom (box_type_rect f f0 f1 f2 f3 f4 f5 dom) codom
    (box_type_rect f f0 f1 f2 f3 f4 f5 codom)
| TApp (b0, b1) ->
  f2 b0 (box_type_rect f f0 f1 f2 f3 f4 f5 b0) b1
    (box_type_rect f f0 f1 f2 f3 f4 f5 b1)
| TVar n -> f3 n
| TInd i -> f4 i
| TConst k -> f5 k

(** val box_type_rec :
    'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
    'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
    (kername -> 'a1) -> box_type -> 'a1 **)

let rec box_type_rec f f0 f1 f2 f3 f4 f5 = function
| TBox -> f
| TAny -> f0
| TArr (dom, codom) ->
  f1 dom (box_type_rec f f0 f1 f2 f3 f4 f5 dom) codom
    (box_type_rec f f0 f1 f2 f3 f4 f5 codom)
| TApp (b0, b1) ->
  f2 b0 (box_type_rec f f0 f1 f2 f3 f4 f5 b0) b1
    (box_type_rec f f0 f1 f2 f3 f4 f5 b1)
| TVar n -> f3 n
| TInd i -> f4 i
| TConst k -> f5 k

(** val decompose_arr : box_type -> box_type list * box_type **)

let rec decompose_arr bt = match bt with
| TArr (dom, cod) ->
  let (args, res) = decompose_arr cod in ((dom :: args), res)
| _ -> ([], bt)

(** val can_have_args : box_type -> bool **)

let can_have_args = function
| TInd _ -> true
| TConst _ -> true
| _ -> false

(** val mkTApps : box_type -> box_type list -> box_type **)

let rec mkTApps hd = function
| [] -> hd
| a :: args0 -> mkTApps (TApp (hd, a)) args0

type constant_body = { cst_type : (name list * box_type);
                       cst_body : term option }

(** val cst_type : constant_body -> name list * box_type **)

let cst_type c =
  c.cst_type

(** val cst_body : constant_body -> term option **)

let cst_body c =
  c.cst_body

type type_var_info = { tvar_name : name; tvar_is_logical : bool;
                       tvar_is_arity : bool; tvar_is_sort : bool }

(** val tvar_name : type_var_info -> name **)

let tvar_name t0 =
  t0.tvar_name

(** val tvar_is_logical : type_var_info -> bool **)

let tvar_is_logical t0 =
  t0.tvar_is_logical

(** val tvar_is_arity : type_var_info -> bool **)

let tvar_is_arity t0 =
  t0.tvar_is_arity

(** val tvar_is_sort : type_var_info -> bool **)

let tvar_is_sort t0 =
  t0.tvar_is_sort

type one_inductive_body = { ind_name : ident; ind_propositional : bool;
                            ind_kelim : allowed_eliminations;
                            ind_type_vars : type_var_info list;
                            ind_ctors : ((ident * (name * box_type)
                                        list) * nat) list;
                            ind_projs : (ident * box_type) list }

(** val ind_name : one_inductive_body -> ident **)

let ind_name o =
  o.ind_name

(** val ind_propositional : one_inductive_body -> bool **)

let ind_propositional o =
  o.ind_propositional

(** val ind_kelim : one_inductive_body -> allowed_eliminations **)

let ind_kelim o =
  o.ind_kelim

(** val ind_type_vars : one_inductive_body -> type_var_info list **)

let ind_type_vars o =
  o.ind_type_vars

(** val ind_ctors :
    one_inductive_body -> ((ident * (name * box_type) list) * nat) list **)

let ind_ctors o =
  o.ind_ctors

(** val ind_projs : one_inductive_body -> (ident * box_type) list **)

let ind_projs o =
  o.ind_projs

type mutual_inductive_body = { ind_finite : recursivity_kind;
                               ind_npars : nat;
                               ind_bodies : one_inductive_body list }

(** val ind_finite : mutual_inductive_body -> recursivity_kind **)

let ind_finite m =
  m.ind_finite

(** val ind_npars : mutual_inductive_body -> nat **)

let ind_npars m =
  m.ind_npars

(** val ind_bodies : mutual_inductive_body -> one_inductive_body list **)

let ind_bodies m =
  m.ind_bodies

type global_decl =
| ConstantDecl of constant_body
| InductiveDecl of mutual_inductive_body
| TypeAliasDecl of (type_var_info list * box_type) option

(** val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) ->
    ((type_var_info list * box_type) option -> 'a1) -> global_decl -> 'a1 **)

let global_decl_rect f f0 f1 = function
| ConstantDecl c -> f c
| InductiveDecl m -> f0 m
| TypeAliasDecl o -> f1 o

(** val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) ->
    ((type_var_info list * box_type) option -> 'a1) -> global_decl -> 'a1 **)

let global_decl_rec f f0 f1 = function
| ConstantDecl c -> f c
| InductiveDecl m -> f0 m
| TypeAliasDecl o -> f1 o

type global_env = ((kername * bool) * global_decl) list

(** val lookup_env : global_env -> kername -> global_decl option **)

let lookup_env _UU03a3_ id =
  option_map snd
    (find (fun pat ->
      let (y, _) = pat in
      let (name0, _) = y in Kername.reflect_kername id name0) _UU03a3_)

(** val lookup_constant : global_env -> kername -> constant_body option **)

let lookup_constant _UU03a3_ kn =
  match lookup_env _UU03a3_ kn with
  | Some g -> (match g with
               | ConstantDecl cst -> Some cst
               | _ -> None)
  | None -> None

(** val lookup_minductive :
    global_env -> kername -> mutual_inductive_body option **)

let lookup_minductive _UU03a3_ kn =
  match lookup_env _UU03a3_ kn with
  | Some g -> (match g with
               | InductiveDecl mib -> Some mib
               | _ -> None)
  | None -> None

(** val lookup_inductive :
    global_env -> inductive -> one_inductive_body option **)

let lookup_inductive _UU03a3_ ind =
  match lookup_minductive _UU03a3_ ind.inductive_mind with
  | Some mib -> nth_error mib.ind_bodies ind.inductive_ind
  | None -> None

(** val lookup_constructor :
    global_env -> inductive -> nat -> ((ident * (name * box_type)
    list) * nat) option **)

let lookup_constructor _UU03a3_ ind c =
  match lookup_inductive _UU03a3_ ind with
  | Some oib -> nth_error oib.ind_ctors c
  | None -> None

(** val lookup_constructor_full :
    global_env -> inductive -> nat ->
    ((mutual_inductive_body * one_inductive_body) * ((ident * (name * box_type)
    list) * nat)) option **)

let lookup_constructor_full _UU03a3_ ind c =
  match lookup_minductive _UU03a3_ ind.inductive_mind with
  | Some mib ->
    (match nth_error mib.ind_bodies ind.inductive_ind with
     | Some oib ->
       (match nth_error oib.ind_ctors c with
        | Some c0 -> Some ((mib, oib), c0)
        | None -> None)
     | None -> None)
  | None -> None

(** val trans_cst : constant_body -> EAst.constant_body **)

let trans_cst cst =
  cst.cst_body

(** val trans_ctors :
    ((ident * (name * box_type) list) * nat) list -> constructor_body list **)

let trans_ctors ctors =
  map (fun pat ->
    let (y, nargs) = pat in
    let (nm, _) = y in { cstr_name = nm; cstr_nargs = nargs }) ctors

(** val trans_oib : one_inductive_body -> EAst.one_inductive_body **)

let trans_oib oib =
  { EAst.ind_name = oib.ind_name; EAst.ind_propositional =
    oib.ind_propositional; EAst.ind_kelim = oib.ind_kelim; EAst.ind_ctors =
    (trans_ctors oib.ind_ctors); EAst.ind_projs =
    (map (compose (fun x -> x) fst) oib.ind_projs) }

(** val trans_mib : mutual_inductive_body -> EAst.mutual_inductive_body **)

let trans_mib mib =
  { EAst.ind_finite = mib.ind_finite; EAst.ind_npars = mib.ind_npars;
    EAst.ind_bodies = (map trans_oib mib.ind_bodies) }

(** val trans_global_decl : global_decl -> EAst.global_decl **)

let trans_global_decl = function
| ConstantDecl cst -> EAst.ConstantDecl (trans_cst cst)
| InductiveDecl mib -> EAst.InductiveDecl (trans_mib mib)
| TypeAliasDecl o -> EAst.ConstantDecl (option_map (fun _ -> Coq_tBox) o)

(** val trans_env : global_env -> global_declarations **)

let trans_env _UU03a3_ =
  map (fun d -> ((fst (fst d)), (trans_global_decl (snd d)))) _UU03a3_

(** val print_term : global_env -> term -> String.t **)

let print_term _UU03a3_ t0 =
  print_program ((trans_env _UU03a3_), t0)
