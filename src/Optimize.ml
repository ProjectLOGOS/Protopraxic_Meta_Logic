open All_Forall
open BasicAst
open Datatypes
open EAst
open ELiftSubst
open EPrimitive
open ExAst
open Kernames
open List0
open MCList
open MCOption
open MCProd
open Nat0
open PeanoNat
open ReflectEq
open ResultMonad
open Utils
open Bytestring

(** val map_subterms : (term -> term) -> term -> term **)

let map_subterms f t0 = match t0 with
| Coq_tEvar (n, ts) -> Coq_tEvar (n, (map f ts))
| Coq_tLambda (na, body) -> Coq_tLambda (na, (f body))
| Coq_tLetIn (na, val0, body) -> Coq_tLetIn (na, (f val0), (f body))
| Coq_tApp (hd0, arg) -> Coq_tApp ((f hd0), (f arg))
| Coq_tCase (p, disc, brs) -> Coq_tCase (p, (f disc), (map (on_snd f) brs))
| Coq_tProj (p, t1) -> Coq_tProj (p, (f t1))
| Coq_tFix (def, i) -> Coq_tFix ((map (map_def f) def), i)
| Coq_tCoFix (def, i) -> Coq_tCoFix ((map (map_def f) def), i)
| Coq_tPrim p -> Coq_tPrim (map_prim f p)
| Coq_tLazy t1 -> Coq_tLazy (f t1)
| Coq_tForce t1 -> Coq_tForce (f t1)
| _ -> t0

type bitmask = bool list

(** val count_zeros : bitmask -> nat **)

let count_zeros bs =
  length (filter negb bs)

(** val count_ones : bitmask -> nat **)

let count_ones bs =
  length (filter (Obj.magic id) bs)

(** val trim_start : bool -> bitmask -> bitmask **)

let rec trim_start b = function
| [] -> []
| b' :: bs0 -> if reflect_bool b' b then trim_start b bs0 else b' :: bs0

(** val trim_end : bool -> bitmask -> bitmask **)

let trim_end b bs =
  List0.rev (trim_start b (List0.rev bs))

type mib_masks = { param_mask : bitmask;
                   ctor_masks : ((nat * nat) * bitmask) list }

(** val get_mib_masks :
    (kername * mib_masks) list -> kername -> mib_masks option **)

let get_mib_masks ind_masks0 kn =
  option_map snd
    (find (fun pat -> let (kn', _) = pat in Kername.reflect_kername kn' kn)
      ind_masks0)

(** val dearg_single : bitmask -> term -> term list -> term **)

let rec dearg_single mask t0 args =
  match mask with
  | [] -> mkApps t0 args
  | b :: mask0 ->
    if b
    then (match args with
          | [] ->
            Coq_tLambda (Coq_nAnon, (dearg_single mask0 (lift (S O) O t0) []))
          | _ :: args0 -> dearg_single mask0 t0 args0)
    else (match args with
          | [] ->
            Coq_tLambda (Coq_nAnon,
              (dearg_single mask0 (Coq_tApp ((lift (S O) O t0), (Coq_tRel
                O))) []))
          | arg :: args0 -> dearg_single mask0 (Coq_tApp (t0, arg)) args0)

(** val get_branch_mask : mib_masks -> nat -> nat -> bitmask **)

let get_branch_mask mm ind_index c =
  match find (fun pat ->
          let (y, _) = pat in
          let (ind', c') = y in (&&) (Nat.eqb ind' ind_index) (Nat.eqb c' c))
          mm.ctor_masks with
  | Some p -> let (_, mask) = p in mask
  | None -> []

(** val get_ctor_mask :
    (kername * mib_masks) list -> inductive -> nat -> bitmask **)

let get_ctor_mask ind_masks0 ind c =
  match get_mib_masks ind_masks0 ind.inductive_mind with
  | Some mm -> app mm.param_mask (get_branch_mask mm ind.inductive_ind c)
  | None -> []

(** val get_const_mask : (kername * bitmask) list -> kername -> bitmask **)

let get_const_mask const_masks0 kn =
  match find (fun pat ->
          let (kn', _) = pat in Kername.reflect_kername kn' kn) const_masks0 with
  | Some p -> let (_, mask) = p in mask
  | None -> []

(** val masked : bitmask -> 'a1 list -> 'a1 list **)

let rec masked mask xs =
  match mask with
  | [] -> xs
  | b :: mask0 ->
    (match xs with
     | [] -> []
     | x :: xs0 -> if b then masked mask0 xs0 else x :: (masked mask0 xs0))

(** val dearg_lambdas : bitmask -> term -> term **)

let rec dearg_lambdas mask body = match body with
| Coq_tLambda (na, lam_body) ->
  (match mask with
   | [] -> body
   | b :: mask0 ->
     if b
     then subst1 Coq_tBox O (dearg_lambdas mask0 lam_body)
     else Coq_tLambda (na, (dearg_lambdas mask0 lam_body)))
| Coq_tLetIn (na, val0, body0) ->
  Coq_tLetIn (na, val0, (dearg_lambdas mask body0))
| _ -> body

(** val dearg_branch_body_rec : nat -> bitmask -> term -> nat * term **)

let dearg_branch_body_rec i mask t0 =
  fold_left (fun pat bit ->
    let (i0, t1) = pat in
    if bit then (i0, (subst1 Coq_tBox i0 t1)) else ((S i0), t1)) mask (i, t0)

(** val complete_ctx_mask : bitmask -> name list -> bitmask **)

let complete_ctx_mask mask ctx =
  app (repeat false (sub (length ctx) (length mask))) (List0.rev mask)

(** val dearg_branch_body :
    bitmask -> name list -> term -> name list * term **)

let dearg_branch_body mask bctx t0 =
  let bctx_mask = complete_ctx_mask mask bctx in
  ((masked bctx_mask bctx), (snd (dearg_branch_body_rec O bctx_mask t0)))

(** val dearged_npars : mib_masks option -> nat -> nat **)

let dearged_npars mm npars =
  match mm with
  | Some mm0 -> count_zeros mm0.param_mask
  | None -> npars

(** val dearg_case_branch :
    mib_masks -> inductive -> nat -> (name list * term) -> name list * term **)

let dearg_case_branch mm ind c br =
  let mask = get_branch_mask mm ind.inductive_ind c in
  if Nat.leb (length mask) (length (fst br))
  then dearg_branch_body mask (fst br) (snd br)
  else br

(** val dearg_case_branches :
    mib_masks option -> inductive -> (name list * term) list -> (name
    list * term) list **)

let dearg_case_branches mm ind brs =
  match mm with
  | Some mm0 -> mapi (dearg_case_branch mm0 ind) brs
  | None -> brs

(** val dearged_proj_arg : mib_masks option -> inductive -> nat -> nat **)

let dearged_proj_arg mm ind arg =
  match mm with
  | Some mm0 ->
    let mask = get_branch_mask mm0 ind.inductive_ind O in
    sub arg (count_ones (firstn arg mask))
  | None -> arg

(** val dearg_case :
    (kername * mib_masks) list -> inductive -> nat -> term -> (name
    list * term) list -> term **)

let dearg_case ind_masks0 ind npars discr brs =
  let mm = get_mib_masks ind_masks0 ind.inductive_mind in
  Coq_tCase ((ind, (dearged_npars mm npars)), discr,
  (dearg_case_branches mm ind brs))

(** val dearg_proj :
    (kername * mib_masks) list -> inductive -> nat -> nat -> term -> term **)

let dearg_proj ind_masks0 ind npars arg discr =
  let mm = get_mib_masks ind_masks0 ind.inductive_mind in
  Coq_tProj ({ proj_ind = ind; proj_npars = (dearged_npars mm npars);
  proj_arg = (dearged_proj_arg mm ind arg) }, discr)

(** val dearg_aux :
    (kername * mib_masks) list -> (kername * bitmask) list -> term list ->
    term -> term **)

let rec dearg_aux ind_masks0 const_masks0 args t0 = match t0 with
| Coq_tBox ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tRel _ ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tVar _ ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tEvar (_, _) ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tLambda (_, _) ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tLetIn (_, _, _) ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tApp (hd0, arg) ->
  dearg_aux ind_masks0 const_masks0
    ((dearg_aux ind_masks0 const_masks0 [] arg) :: args) hd0
| Coq_tConst kn -> dearg_single (get_const_mask const_masks0 kn) t0 args
| Coq_tConstruct (ind, c, _) ->
  dearg_single (get_ctor_mask ind_masks0 ind c) t0 args
| Coq_tCase (indn, discr, brs) ->
  let (ind, npars) = indn in
  let discr0 = dearg_aux ind_masks0 const_masks0 [] discr in
  let brs0 = map (on_snd (dearg_aux ind_masks0 const_masks0 [])) brs in
  mkApps (dearg_case ind_masks0 ind npars discr0 brs0) args
| Coq_tProj (p, t1) ->
  let { proj_ind = ind; proj_npars = npars; proj_arg = arg } = p in
  mkApps
    (dearg_proj ind_masks0 ind npars arg
      (dearg_aux ind_masks0 const_masks0 [] t1)) args
| Coq_tFix (_, _) ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tCoFix (_, _) ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tPrim _ ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tLazy _ ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args
| Coq_tForce _ ->
  mkApps (map_subterms (dearg_aux ind_masks0 const_masks0 []) t0) args

(** val dearg :
    (kername * mib_masks) list -> (kername * bitmask) list -> term -> term **)

let dearg ind_masks0 const_masks0 t0 =
  dearg_aux ind_masks0 const_masks0 [] t0

(** val dearg_cst_type_top : bitmask -> box_type -> box_type **)

let rec dearg_cst_type_top mask type0 =
  match mask with
  | [] -> type0
  | b :: mask0 ->
    if b
    then (match type0 with
          | TArr (_, cod) -> dearg_cst_type_top mask0 cod
          | _ -> type0)
    else (match type0 with
          | TArr (dom, cod) -> TArr (dom, (dearg_cst_type_top mask0 cod))
          | _ -> type0)

(** val dearg_cst :
    (kername * mib_masks) list -> (kername * bitmask) list -> kername ->
    constant_body -> constant_body **)

let dearg_cst ind_masks0 const_masks0 kn cst =
  let mask = get_const_mask const_masks0 kn in
  { cst_type = (on_snd (dearg_cst_type_top mask) cst.cst_type); cst_body =
  (option_map
    (let g0 = dearg ind_masks0 const_masks0 in
     let f0 = dearg_lambdas mask in (fun x -> g0 (f0 x))) cst.cst_body) }

(** val dearg_ctor :
    bitmask -> bitmask -> ((ident * (name * box_type) list) * nat) ->
    (ident * (name * box_type) list) * nat **)

let dearg_ctor par_mask ctor_mask = function
| (p, orig_arity) ->
  let (name0, fields) = p in
  ((name0, (masked (app par_mask ctor_mask) fields)),
  (sub orig_arity (count_ones ctor_mask)))

(** val dearg_oib :
    mib_masks -> nat -> one_inductive_body -> one_inductive_body **)

let dearg_oib mib_masks0 oib_index oib =
  { ind_name = oib.ind_name; ind_propositional = oib.ind_propositional;
    ind_kelim = oib.ind_kelim; ind_type_vars = oib.ind_type_vars; ind_ctors =
    (mapi (fun c ctor ->
      let ctor_mask = get_branch_mask mib_masks0 oib_index c in
      dearg_ctor mib_masks0.param_mask ctor_mask ctor) oib.ind_ctors);
    ind_projs =
    (let ctor_mask = get_branch_mask mib_masks0 oib_index O in
     masked ctor_mask oib.ind_projs) }

(** val dearg_mib :
    (kername * mib_masks) list -> kername -> mutual_inductive_body ->
    mutual_inductive_body **)

let dearg_mib ind_masks0 kn mib =
  match get_mib_masks ind_masks0 kn with
  | Some mib_masks0 ->
    { ind_finite = mib.ind_finite; ind_npars =
      (count_zeros mib_masks0.param_mask); ind_bodies =
      (mapi (dearg_oib mib_masks0) mib.ind_bodies) }
  | None -> mib

(** val dearg_decl :
    (kername * mib_masks) list -> (kername * bitmask) list -> kername ->
    global_decl -> global_decl **)

let dearg_decl ind_masks0 const_masks0 kn decl = match decl with
| ConstantDecl cst -> ConstantDecl (dearg_cst ind_masks0 const_masks0 kn cst)
| InductiveDecl mib -> InductiveDecl (dearg_mib ind_masks0 kn mib)
| TypeAliasDecl _ -> decl

(** val dearg_env :
    (kername * mib_masks) list -> (kername * bitmask) list -> global_env ->
    global_env **)

let dearg_env ind_masks0 const_masks0 _UU03a3_ =
  map (fun pat ->
    let (y, decl) = pat in
    let (kn, has_deps) = y in
    ((kn, has_deps), (dearg_decl ind_masks0 const_masks0 kn decl))) _UU03a3_

(** val is_dead : nat -> term -> bool **)

let rec is_dead rel = function
| Coq_tRel i -> negb (Nat.eqb i rel)
| Coq_tEvar (_, ts) -> forallb (is_dead rel) ts
| Coq_tLambda (_, body) -> is_dead (S rel) body
| Coq_tLetIn (_, val0, body) -> (&&) (is_dead rel val0) (is_dead (S rel) body)
| Coq_tApp (hd0, arg) -> (&&) (is_dead rel hd0) (is_dead rel arg)
| Coq_tConstruct (_, _, args) -> forallb (is_dead rel) args
| Coq_tCase (_, discr, brs) ->
  (&&) (is_dead rel discr)
    (forallb (fun pat ->
      let (ctx, t1) = pat in is_dead (add (length ctx) rel) t1) brs)
| Coq_tProj (_, t1) -> is_dead rel t1
| Coq_tFix (defs, _) ->
  forallb
    (let g0 = is_dead (add (length defs) rel) in
     let f0 = fun d -> d.dbody in (fun x -> g0 (f0 x))) defs
| Coq_tCoFix (defs, _) ->
  forallb
    (let g0 = is_dead (add (length defs) rel) in
     let f0 = fun d -> d.dbody in (fun x -> g0 (f0 x))) defs
| Coq_tPrim p -> test_prim (is_dead rel) p
| Coq_tLazy t1 -> is_dead rel t1
| Coq_tForce t1 -> is_dead rel t1
| _ -> true

(** val valid_dearg_mask : bitmask -> term -> bool **)

let rec valid_dearg_mask mask = function
| Coq_tEvar (_, _) -> (match mask with
                       | [] -> true
                       | _ :: _ -> false)
| Coq_tLambda (_, body0) ->
  (match mask with
   | [] -> true
   | b :: mask0 ->
     (&&) (if b then is_dead O body0 else true) (valid_dearg_mask mask0 body0))
| Coq_tLetIn (_, _, body0) -> valid_dearg_mask mask body0
| _ -> (match mask with
        | [] -> true
        | _ :: _ -> false)

(** val valid_dearg_mask_branch : nat -> bitmask -> term -> bool **)

let rec valid_dearg_mask_branch i mask body =
  match mask with
  | [] -> true
  | b :: mask0 ->
    (&&) (if b then is_dead i body else true)
      (valid_dearg_mask_branch (S i) mask0 body)

(** val valid_case_masks :
    (kername * mib_masks) list -> inductive -> nat -> (name list * term) list
    -> bool **)

let valid_case_masks ind_masks0 ind npars brs =
  match get_mib_masks ind_masks0 ind.inductive_mind with
  | Some mm ->
    (&&) (Nat.eqb (length mm.param_mask) npars)
      (alli (fun c pat ->
        let (ctx, br) = pat in
        let ar = length ctx in
        (&&) (Nat.leb (length (get_branch_mask mm ind.inductive_ind c)) ar)
          (valid_dearg_mask_branch O
            (complete_ctx_mask (get_branch_mask mm ind.inductive_ind c) ctx)
            br)) O brs)
  | None -> true

(** val valid_proj :
    (kername * mib_masks) list -> inductive -> nat -> nat -> bool **)

let valid_proj ind_masks0 ind npars arg =
  match get_mib_masks ind_masks0 ind.inductive_mind with
  | Some mm ->
    (&&) (Nat.eqb (length mm.param_mask) npars)
      (negb (nth arg (get_branch_mask mm ind.inductive_ind O) false))
  | None -> true

(** val valid_cases : (kername * mib_masks) list -> term -> bool **)

let rec valid_cases ind_masks0 = function
| Coq_tEvar (_, ts) -> forallb (valid_cases ind_masks0) ts
| Coq_tLambda (_, body) -> valid_cases ind_masks0 body
| Coq_tLetIn (_, val0, body) ->
  (&&) (valid_cases ind_masks0 val0) (valid_cases ind_masks0 body)
| Coq_tApp (hd0, arg) ->
  (&&) (valid_cases ind_masks0 hd0) (valid_cases ind_masks0 arg)
| Coq_tConstruct (_, _, args) ->
  (match args with
   | [] -> true
   | _ :: _ -> false)
| Coq_tCase (indn, discr, brs) ->
  let (ind, npars) = indn in
  (&&)
    ((&&) (valid_cases ind_masks0 discr)
      (forallb (fun x -> valid_cases ind_masks0 (snd x)) brs))
    (valid_case_masks ind_masks0 ind npars brs)
| Coq_tProj (p, t1) ->
  let { proj_ind = ind; proj_npars = npars; proj_arg = arg } = p in
  (&&) (valid_cases ind_masks0 t1) (valid_proj ind_masks0 ind npars arg)
| Coq_tFix (defs, _) ->
  forallb
    (let f0 = fun d -> d.dbody in fun x -> valid_cases ind_masks0 (f0 x)) defs
| Coq_tCoFix (defs, _) ->
  forallb
    (let f0 = fun d -> d.dbody in fun x -> valid_cases ind_masks0 (f0 x)) defs
| Coq_tPrim p -> test_prim (valid_cases ind_masks0) p
| Coq_tLazy t1 -> valid_cases ind_masks0 t1
| Coq_tForce t1 -> valid_cases ind_masks0 t1
| _ -> true

(** val forallbi : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool **)

let rec forallbi f n = function
| [] -> true
| hd0 :: tl0 -> (&&) (f n hd0) (forallbi f (S n) tl0)

(** val check_oib_masks : mib_masks -> nat -> one_inductive_body -> bool **)

let check_oib_masks masks i oib =
  (&&)
    (forallbi (fun c cb ->
      reflect_nat (length (get_branch_mask masks i c)) (snd cb)) O
      oib.ind_ctors)
    (match oib.ind_projs with
     | [] -> true
     | _ :: _ ->
       let mask = get_branch_mask masks i O in
       reflect_nat (length mask) (length oib.ind_projs))

(** val valid_masks_decl :
    (kername * mib_masks) list -> (kername * bitmask) list ->
    ((kername * bool) * global_decl) -> bool **)

let valid_masks_decl ind_masks0 const_masks0 = function
| (p0, g) ->
  let (kn, _) = p0 in
  (match g with
   | ConstantDecl c ->
     let { cst_type = _; cst_body = cst_body0 } = c in
     (match cst_body0 with
      | Some body ->
        (&&) (valid_dearg_mask (get_const_mask const_masks0 kn) body)
          (valid_cases ind_masks0 body)
      | None -> true)
   | InductiveDecl mib ->
     (match get_mib_masks ind_masks0 kn with
      | Some mask ->
        (&&) (Nat.eqb (length mask.param_mask) mib.ind_npars)
          (forallbi (check_oib_masks mask) O mib.ind_bodies)
      | None -> false)
   | TypeAliasDecl _ -> Nat.eqb (length (get_const_mask const_masks0 kn)) O)

(** val valid_masks_env :
    (kername * mib_masks) list -> (kername * bitmask) list -> global_env ->
    bool **)

let valid_masks_env ind_masks0 const_masks0 _UU03a3_ =
  forallb (valid_masks_decl ind_masks0 const_masks0) _UU03a3_

(** val is_expanded_aux :
    (kername * mib_masks) list -> (kername * bitmask) list -> nat -> term ->
    bool **)

let rec is_expanded_aux ind_masks0 const_masks0 nargs = function
| Coq_tEvar (_, ts) -> forallb (is_expanded_aux ind_masks0 const_masks0 O) ts
| Coq_tLambda (_, body) -> is_expanded_aux ind_masks0 const_masks0 O body
| Coq_tLetIn (_, val0, body) ->
  (&&) (is_expanded_aux ind_masks0 const_masks0 O val0)
    (is_expanded_aux ind_masks0 const_masks0 O body)
| Coq_tApp (hd0, arg) ->
  (&&) (is_expanded_aux ind_masks0 const_masks0 O arg)
    (is_expanded_aux ind_masks0 const_masks0 (S nargs) hd0)
| Coq_tConst kn -> Nat.leb (length (get_const_mask const_masks0 kn)) nargs
| Coq_tConstruct (ind, c, _) ->
  Nat.leb (length (get_ctor_mask ind_masks0 ind c)) nargs
| Coq_tCase (_, discr, brs) ->
  (&&) (is_expanded_aux ind_masks0 const_masks0 O discr)
    (forallb
      (let g0 = is_expanded_aux ind_masks0 const_masks0 O in
       fun x -> g0 (snd x)) brs)
| Coq_tProj (_, t1) -> is_expanded_aux ind_masks0 const_masks0 O t1
| Coq_tFix (defs, _) ->
  forallb
    (let g0 = is_expanded_aux ind_masks0 const_masks0 O in
     let f0 = fun d -> d.dbody in (fun x -> g0 (f0 x))) defs
| Coq_tCoFix (defs, _) ->
  forallb
    (let g0 = is_expanded_aux ind_masks0 const_masks0 O in
     let f0 = fun d -> d.dbody in (fun x -> g0 (f0 x))) defs
| Coq_tPrim p -> test_prim (is_expanded_aux ind_masks0 const_masks0 O) p
| Coq_tLazy t1 -> is_expanded_aux ind_masks0 const_masks0 O t1
| Coq_tForce t1 -> is_expanded_aux ind_masks0 const_masks0 O t1
| _ -> true

(** val is_expanded :
    (kername * mib_masks) list -> (kername * bitmask) list -> term -> bool **)

let is_expanded ind_masks0 const_masks0 t0 =
  is_expanded_aux ind_masks0 const_masks0 O t0

(** val is_expanded_env :
    (kername * mib_masks) list -> (kername * bitmask) list -> global_env ->
    bool **)

let is_expanded_env ind_masks0 const_masks0 _UU03a3_ =
  forallb (fun pat ->
    let (_, decl) = pat in
    (match decl with
     | ConstantDecl c ->
       let { cst_type = _; cst_body = cst_body0 } = c in
       (match cst_body0 with
        | Some body -> is_expanded ind_masks0 const_masks0 body
        | None -> true)
     | _ -> true)) _UU03a3_

(** val keep_tvar : type_var_info -> bool **)

let keep_tvar tvar =
  (&&) tvar.tvar_is_arity (negb tvar.tvar_is_logical)

(** val dearg_single_bt :
    type_var_info list -> box_type -> box_type list -> box_type **)

let rec dearg_single_bt tvars t0 args =
  match tvars with
  | [] -> mkTApps t0 args
  | tvar :: tvars0 ->
    (match args with
     | [] -> mkTApps t0 args
     | arg :: args0 ->
       if keep_tvar tvar
       then dearg_single_bt tvars0 (TApp (t0, arg)) args0
       else dearg_single_bt tvars0 t0 args0)

(** val get_inductive_tvars :
    global_env -> inductive -> type_var_info list **)

let get_inductive_tvars _UU03a3_ ind =
  match lookup_inductive _UU03a3_ ind with
  | Some oib -> oib.ind_type_vars
  | None -> []

(** val debox_box_type_aux :
    global_env -> box_type list -> box_type -> box_type **)

let rec debox_box_type_aux _UU03a3_ args bt = match bt with
| TArr (dom, codom) ->
  TArr ((debox_box_type_aux _UU03a3_ [] dom),
    (debox_box_type_aux _UU03a3_ [] codom))
| TApp (ty1, ty2) ->
  debox_box_type_aux _UU03a3_ ((debox_box_type_aux _UU03a3_ [] ty2) :: args)
    ty1
| TInd ind -> dearg_single_bt (get_inductive_tvars _UU03a3_ ind) bt args
| TConst kn ->
  (match lookup_env _UU03a3_ kn with
   | Some g ->
     (match g with
      | TypeAliasDecl o ->
        (match o with
         | Some p -> let (vs, _) = p in dearg_single_bt vs bt args
         | None -> bt)
      | _ -> bt)
   | None -> bt)
| _ -> mkTApps bt args

(** val debox_box_type : global_env -> box_type -> box_type **)

let debox_box_type _UU03a3_ bt =
  debox_box_type_aux _UU03a3_ [] bt

(** val debox_type_constant : global_env -> constant_body -> constant_body **)

let debox_type_constant _UU03a3_ cst =
  { cst_type = (on_snd (debox_box_type _UU03a3_) cst.cst_type); cst_body =
    cst.cst_body }

(** val reindex : type_var_info list -> box_type -> box_type **)

let rec reindex tvars bt = match bt with
| TArr (dom, cod) -> TArr ((reindex tvars dom), (reindex tvars cod))
| TApp (hd0, arg) -> TApp ((reindex tvars hd0), (reindex tvars arg))
| TVar i -> TVar (length (filter keep_tvar (firstn i tvars)))
| _ -> bt

(** val debox_type_oib :
    global_env -> one_inductive_body -> one_inductive_body **)

let debox_type_oib _UU03a3_ oib =
  let debox =
    let g0 = reindex oib.ind_type_vars in
    let f0 = debox_box_type _UU03a3_ in (fun x -> g0 (f0 x))
  in
  { ind_name = oib.ind_name; ind_propositional = oib.ind_propositional;
  ind_kelim = oib.ind_kelim; ind_type_vars =
  (filter keep_tvar oib.ind_type_vars); ind_ctors =
  (map (fun pat ->
    let (y, orig_arity) = pat in
    let (nm, fields) = y in ((nm, (map (on_snd debox) fields)), orig_arity))
    oib.ind_ctors); ind_projs = (map (on_snd debox) oib.ind_projs) }

(** val debox_type_mib :
    global_env -> mutual_inductive_body -> mutual_inductive_body **)

let debox_type_mib _UU03a3_ mib =
  { ind_finite = mib.ind_finite; ind_npars = mib.ind_npars; ind_bodies =
    (map (debox_type_oib _UU03a3_) mib.ind_bodies) }

(** val debox_type_decl : global_env -> global_decl -> global_decl **)

let debox_type_decl _UU03a3_ = function
| ConstantDecl cst -> ConstantDecl (debox_type_constant _UU03a3_ cst)
| InductiveDecl mib -> InductiveDecl (debox_type_mib _UU03a3_ mib)
| TypeAliasDecl ta ->
  (match ta with
   | Some p ->
     let (ty_vars, ty) = p in
     TypeAliasDecl (Some ((filter keep_tvar ty_vars),
     (reindex ty_vars (debox_box_type _UU03a3_ ty))))
   | None -> TypeAliasDecl None)

(** val debox_env_types : global_env -> global_env **)

let debox_env_types _UU03a3_ =
  map (on_snd (debox_type_decl _UU03a3_)) _UU03a3_

(** val clear_bit : nat -> bitmask -> bitmask **)

let rec clear_bit n bs =
  match n with
  | O -> (match bs with
          | [] -> []
          | _ :: bs0 -> false :: bs0)
  | S n0 -> (match bs with
             | [] -> []
             | b :: bs0 -> b :: (clear_bit n0 bs0))

type analyze_state = bitmask * (kername * mib_masks) list

(** val set_used : analyze_state -> nat -> analyze_state **)

let set_used s n =
  ((clear_bit n (fst s)), (snd s))

(** val new_vars : analyze_state -> nat -> analyze_state **)

let new_vars s n =
  ((app (repeat true n) (fst s)), (snd s))

(** val new_var : analyze_state -> analyze_state **)

let new_var s =
  ((true :: (fst s)), (snd s))

(** val remove_vars : analyze_state -> nat -> analyze_state **)

let remove_vars s n =
  ((skipn n (fst s)), (snd s))

(** val remove_var : analyze_state -> analyze_state **)

let remove_var s =
  ((tl (fst s)), (snd s))

(** val update_mib_masks :
    analyze_state -> kername -> mib_masks -> analyze_state **)

let update_mib_masks s kn mm =
  let update_list =
    let rec update_list = function
    | [] -> []
    | y :: l0 ->
      let (kn', mm') = y in
      if Kername.reflect_kername kn' kn
      then (kn, mm) :: l0
      else (kn', mm') :: (update_list l0)
    in update_list
  in
  ((fst s), (update_list (snd s)))

(** val update_ind_ctor_mask :
    nat -> nat -> ((nat * nat) * bitmask) list -> (bitmask -> bitmask) ->
    ((nat * nat) * bitmask) list **)

let rec update_ind_ctor_mask ind c ctor_masks0 f =
  match ctor_masks0 with
  | [] -> []
  | p :: ctor_masks1 ->
    let (p0, mask') = p in
    let (ind', c') = p0 in
    if (&&) (Nat.eqb ind' ind) (Nat.eqb c' c)
    then ((ind', c'), (f mask')) :: ctor_masks1
    else ((ind', c'), mask') :: (update_ind_ctor_mask ind c ctor_masks1 f)

(** val fold_lefti :
    (nat -> 'a1 -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_lefti f n l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_lefti f (S n) t0 (f n a0 b)

(** val analyze_top_level :
    (analyze_state -> term -> analyze_state) -> analyze_state -> nat -> term
    -> bitmask * analyze_state **)

let rec analyze_top_level analyze0 state max_lams t0 = match t0 with
| Coq_tLambda (_, body) ->
  (match max_lams with
   | O -> ([], (analyze0 state t0))
   | S max_lams0 ->
     let (mask, state0) =
       analyze_top_level analyze0 (new_var state) max_lams0 body
     in
     (((hd true (fst state0)) :: mask), (remove_var state0)))
| Coq_tLetIn (_, val0, body) ->
  let state0 = analyze0 state val0 in
  let (mask, state1) =
    analyze_top_level analyze0 (new_var state0) max_lams body
  in
  (mask, (remove_var state1))
| _ -> ([], (analyze0 state t0))

(** val analyze : analyze_state -> term -> analyze_state **)

let rec analyze state = function
| Coq_tRel i -> set_used state i
| Coq_tEvar (_, ts) -> fold_left analyze ts state
| Coq_tLambda (_, cod) -> remove_var (analyze (new_var state) cod)
| Coq_tLetIn (_, val0, body) ->
  remove_var (analyze (new_var (analyze state val0)) body)
| Coq_tApp (hd0, arg) -> analyze (analyze state hd0) arg
| Coq_tCase (indn, discr, brs) ->
  let (ind, _) = indn in
  let state0 = analyze state discr in
  (match get_mib_masks (snd state0) ind.inductive_mind with
   | Some mm ->
     let analyze_case = fun _ pat brs0 ->
       let (state1, ctor_masks0) = pat in
       let state2 = analyze (new_vars state1 (length (fst brs0))) (snd brs0)
       in
       ((remove_vars state2 (length (fst brs0))), ctor_masks0)
     in
     let (state1, ctor_masks0) =
       fold_lefti analyze_case O brs (state0, mm.ctor_masks)
     in
     let mm0 = { param_mask = mm.param_mask; ctor_masks = ctor_masks0 } in
     update_mib_masks state1 ind.inductive_mind mm0
   | None -> state0)
| Coq_tProj (p, t1) ->
  let { proj_ind = ind; proj_npars = _; proj_arg = arg } = p in
  let state0 = analyze state t1 in
  (match get_mib_masks (snd state0) ind.inductive_mind with
   | Some mm ->
     let ctor_masks0 =
       update_ind_ctor_mask ind.inductive_ind O mm.ctor_masks (clear_bit arg)
     in
     let mm0 = { param_mask = mm.param_mask; ctor_masks = ctor_masks0 } in
     update_mib_masks state0 ind.inductive_mind mm0
   | None -> state0)
| Coq_tFix (defs, _) ->
  let state0 = new_vars state (length defs) in
  let state1 = fold_left (fun state1 d -> analyze state1 d.dbody) defs state0
  in
  remove_vars state1 (length defs)
| Coq_tCoFix (defs, _) ->
  let state0 = new_vars state (length defs) in
  let state1 = fold_left (fun state1 d -> analyze state1 d.dbody) defs state0
  in
  remove_vars state1 (length defs)
| Coq_tPrim p -> fold_prim analyze p state
| Coq_tLazy t1 -> analyze state t1
| Coq_tForce t1 -> analyze state t1
| _ -> state

(** val decompose_TArr : box_type -> box_type list * box_type **)

let rec decompose_TArr bt = match bt with
| TArr (dom, cod) -> map_fst (fun x -> dom :: x) (decompose_TArr cod)
| _ -> ([], bt)

(** val is_box_or_any : box_type -> bool **)

let is_box_or_any = function
| TBox -> true
| TAny -> true
| _ -> false

(** val analyze_constant :
    constant_body -> (kername * mib_masks) list ->
    bitmask * (kername * mib_masks) list **)

let analyze_constant cst inds =
  let (doms, _) = decompose_TArr (snd cst.cst_type) in
  (match cst.cst_body with
   | Some body ->
     let max_lams = length doms in
     let (mask, a) = analyze_top_level analyze ([], inds) max_lams body in
     let (_, inds0) = a in
     if forallb is_box_or_any doms
     then ((clear_bit O mask), inds0)
     else (mask, inds0)
   | None -> ((map is_box_or_any doms), inds))

type dearg_set = { const_masks : (kername * bitmask) list;
                   ind_masks : (kername * mib_masks) list }

(** val analyze_env :
    (kername -> bitmask option) -> global_env -> dearg_set **)

let rec analyze_env overridden_masks = function
| [] -> { const_masks = []; ind_masks = [] }
| p :: _UU03a3_0 ->
  let (p0, decl) = p in
  let (kn, _) = p0 in
  let { const_masks = consts; ind_masks = inds } =
    analyze_env overridden_masks _UU03a3_0
  in
  let (consts0, inds0) =
    match decl with
    | ConstantDecl cst ->
      let (mask, inds0) = analyze_constant cst inds in
      let mask0 = option_get mask (overridden_masks kn) in
      (((kn, mask0) :: consts), inds0)
    | InductiveDecl mib ->
      let ctor_masks0 =
        concat
          (mapi (fun ind oib ->
            mapi (fun c pat ->
              let (y, _) = pat in
              let (_, args) = y in
              ((ind, c),
              (map (fun x -> is_box_or_any (snd x))
                (skipn mib.ind_npars args)))) oib.ind_ctors) mib.ind_bodies)
      in
      let mm = { param_mask = (repeat true mib.ind_npars); ctor_masks =
        ctor_masks0 }
      in
      (consts, ((kn, mm) :: inds))
    | TypeAliasDecl _ -> (consts, inds)
  in
  { const_masks = consts0; ind_masks = inds0 }

(** val trim_const_masks :
    (kername * bitmask) list -> (kername * bitmask) list **)

let trim_const_masks cm =
  map (on_snd (trim_end false)) cm

(** val trim_ctor_masks :
    ((nat * nat) * bitmask) list -> ((nat * nat) * bitmask) list **)

let trim_ctor_masks cm =
  map (fun pat -> let (y, mask) = pat in (y, (trim_end false mask))) cm

(** val trim_mib_masks : mib_masks -> mib_masks **)

let trim_mib_masks mm =
  { param_mask = mm.param_mask; ctor_masks = (trim_ctor_masks mm.ctor_masks) }

(** val trim_ind_masks :
    (kername * mib_masks) list -> (kername * mib_masks) list **)

let trim_ind_masks im =
  map (on_snd trim_mib_masks) im

(** val throwIf : bool -> String.t -> (unit, String.t) result **)

let throwIf b err =
  if b then Err err else Ok ()
