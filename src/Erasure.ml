open All_Forall
open BasicAst
open Basics
open CRelationClasses
open Classes0
open Datatypes
open EAst
open EAstUtils
open ErasureFunction
open ExAst
open Kernames
open List0
open MCList
open MCProd
open MCReflect
open PCUICAst
open PCUICAstUtils
open PCUICErrors
open PCUICNormal
open PCUICPrimitive
open PCUICSafeReduce
open PCUICSafeRetyping
open PCUICTyping
open PCUICWfEnv
open PCUICWfEnvImpl
open Primitive
open ReflectEq
open Signature
open Specif
open Universes0
open Vector
open VectorDef
open Bytestring
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module P = PCUICAst

module Ex = ExAst

type fot_view =
| Coq_fot_view_prod of aname * term * term
| Coq_fot_view_sort of Sort.t
| Coq_fot_view_other of term

(** val fot_viewc : term -> fot_view **)

let fot_viewc = function
| Coq_tSort u -> Coq_fot_view_sort u
| Coq_tProd (na, a, b) -> Coq_fot_view_prod (na, a, b)
| x -> Coq_fot_view_other x

type arity_ass = aname * term

type conv_arity = { conv_ar_context : arity_ass list; conv_ar_univ : Sort.t }

type conv_arity_or_not = (conv_arity, __) sum

(** val is_sort :
    PCUICEnvironment.global_env_ext -> term BasicAst.context_decl list ->
    term -> conv_arity_or_not -> __ option **)

let is_sort _ _ _ = function
| Coq_inl c0 ->
  let { conv_ar_context = conv_ar_context0; conv_ar_univ = _ } = c0 in
  (match conv_ar_context0 with
   | [] -> Some __
   | _ :: _ -> None)
| Coq_inr _ -> None

(** val is_arity :
    PCUICEnvironment.global_env_ext -> term BasicAst.context_decl list ->
    term -> conv_arity_or_not -> bool **)

let is_arity _ _ _ = function
| Coq_inl _ -> true
| Coq_inr _ -> false

type type_flag = { is_logical : bool; conv_ar : conv_arity_or_not }

(** val flag_of_type :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> term -> type_flag **)

let flag_of_type x_type x _ a a0 =
  let rec fix_F x0 =
    let _UU0393_ = let pr1,_ = x0 in pr1 in
    (match fot_viewc
             (ErasureFunction.inspect
               (hnf extraction_checker_flags x_type x _UU0393_
                 (let pr1,_ = let _,pr2 = x0 in pr2 in pr1))) with
     | Coq_fot_view_prod (na, a1, b) ->
       let flag_cod =
         let y = (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a1)),(b,__)
         in
         fix_F y
       in
       { is_logical = flag_cod.is_logical; conv_ar =
       (match flag_cod.conv_ar with
        | Coq_inl car ->
          Coq_inl { conv_ar_context = ((na, a1) :: car.conv_ar_context);
            conv_ar_univ = car.conv_ar_univ }
        | Coq_inr _ -> Coq_inr __) }
     | Coq_fot_view_sort univ ->
       { is_logical = (Sort.is_prop univ); conv_ar = (Coq_inl
         { conv_ar_context = []; conv_ar_univ = univ }) }
     | Coq_fot_view_other t0 ->
       let Coq_existT (x1, _) =
         infer extraction_checker_flags x_type x _UU0393_ t0
       in
       (match ErasureFunction.inspect
                (reduce_to_sort extraction_checker_flags x_type x _UU0393_ x1) with
        | Checked_comp a1 ->
          let Coq_existT (x2, _) = a1 in
          { is_logical = (Sort.is_prop x2); conv_ar = (Coq_inr __) }
        | TypeError_comp _ -> assert false (* absurd case *)))
  in fix_F (a,(a0,__))

type erase_type_view =
| Coq_et_view_rel of nat
| Coq_et_view_sort of Sort.t
| Coq_et_view_prod of aname * term * term
| Coq_et_view_app of term * term
| Coq_et_view_const of kername * Instance.t
| Coq_et_view_ind of inductive * Instance.t
| Coq_et_view_other of term

(** val erase_type_viewc : term -> erase_type_view **)

let erase_type_viewc = function
| Coq_tRel n -> Coq_et_view_rel n
| Coq_tSort u -> Coq_et_view_sort u
| Coq_tProd (na, a, b) -> Coq_et_view_prod (na, a, b)
| Coq_tApp (u, v) -> Coq_et_view_app (u, v)
| Coq_tConst (k, ui) -> Coq_et_view_const (k, ui)
| Coq_tInd (ind, ui) -> Coq_et_view_ind (ind, ui)
| x -> Coq_et_view_other x

type tRel_kind =
| RelTypeVar of nat
| RelInductive of inductive
| RelOther

(** val erase_type_aux :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> tRel_kind Vector.t -> term -> nat option ->
    name list * box_type **)

let erase_type_aux x_type x r_UU03a3_ a a0 a1 b =
  let rec fix_F x0 =
    let _UU0393_ = let pr1,_ = x0 in pr1 in
    let er_UU0393_ = let pr1,_ = let _,pr2 = x0 in pr2 in pr1 in
    let next_tvar =
      let _,pr2 = let _,pr2 = let _,pr2 = let _,pr2 = x0 in pr2 in pr2 in pr2
      in
      pr2
    in
    let erase_type_aux0 = fun a2 a3 a4 b0 ->
      let y = a2,(a3,(a4,(__,b0))) in (fun _ -> fix_F y)
    in
    let refine =
      ErasureFunction.inspect
        (reduce_term extraction_checker_flags RedFlags.nodelta x_type x
          _UU0393_
          (let pr1,_ = let _,pr2 = let _,pr2 = x0 in pr2 in pr2 in pr1))
    in
    if (flag_of_type x_type x r_UU03a3_ _UU0393_ refine).is_logical
    then ([], TBox)
    else (match erase_type_viewc refine with
          | Coq_et_view_rel i ->
            (match nth_order (length _UU0393_) er_UU0393_ i with
             | RelTypeVar n -> ([], (TVar n))
             | RelInductive ind -> ([], (TInd ind))
             | RelOther -> ([], TAny))
          | Coq_et_view_sort _ -> ([], TBox)
          | Coq_et_view_prod (na, a2, b0) ->
            let { is_logical = is_logical0; conv_ar = conv_ar0 } =
              flag_of_type x_type x r_UU03a3_ _UU0393_ a2
            in
            if is_logical0
            then on_snd (fun x1 -> TArr (TBox, x1))
                   (erase_type_aux0
                     (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a2))
                     (Coq_cons (RelOther, (length _UU0393_), er_UU0393_)) b0
                     next_tvar __)
            else (match conv_ar0 with
                  | Coq_inl _ ->
                    let var =
                      match next_tvar with
                      | Some i -> RelTypeVar i
                      | None -> RelOther
                    in
                    let (tvars, cod) =
                      erase_type_aux0
                        (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a2))
                        (Coq_cons (var, (length _UU0393_), er_UU0393_)) b0
                        (option_map (fun x1 -> S x1) next_tvar) __
                    in
                    ((match next_tvar with
                      | Some _ -> na.binder_name :: tvars
                      | None -> tvars), (TArr (TBox, cod)))
                  | Coq_inr _ ->
                    let (_, dom) =
                      erase_type_aux0 _UU0393_ er_UU0393_ a2 None __
                    in
                    on_snd (fun x1 -> TArr (dom, x1))
                      (erase_type_aux0
                        (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a2))
                        (Coq_cons (RelOther, (length _UU0393_), er_UU0393_))
                        b0 next_tvar __))
          | Coq_et_view_app (hd, arg) ->
            let (t0, l) =
              ErasureFunction.inspect (decompose_app (Coq_tApp (hd, arg)))
            in
            let hdbt =
              match t0 with
              | Coq_tRel i ->
                (match nth_order (length _UU0393_) er_UU0393_ i with
                 | RelTypeVar i0 -> TVar i0
                 | RelInductive ind -> TInd ind
                 | RelOther -> TAny)
              | Coq_tConst (kn, _) -> TConst kn
              | Coq_tInd (ind, _) -> TInd ind
              | _ -> TAny
            in
            if can_have_args hdbt
            then let erase_arg = fun a2 ->
                   let Coq_existT (aT, _) =
                     infer extraction_checker_flags x_type x _UU0393_ a2
                   in
                   let { is_logical = is_logical0; conv_ar = car } =
                     flag_of_type x_type x r_UU03a3_ _UU0393_ aT
                   in
                   if is_logical0
                   then TBox
                   else (match is_sort r_UU03a3_ _UU0393_ aT car with
                         | Some _ ->
                           snd
                             (erase_type_aux0 _UU0393_ er_UU0393_ a2 None __)
                         | None -> TAny)
                 in
                 ([], (mkTApps hdbt (map_In l (fun a2 _ -> erase_arg a2))))
            else ([], hdbt)
          | Coq_et_view_const (kn, _) -> ([], (TConst kn))
          | Coq_et_view_ind (ind, _) -> ([], (TInd ind))
          | Coq_et_view_other _ -> ([], TAny))
  in fix_F (a,(a0,(a1,(__,b))))

(** val erase_type :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> term ->
    name list * box_type **)

let erase_type x_type x r_UU03a3_ t0 =
  erase_type_aux x_type x r_UU03a3_ [] Coq_nil t0 (Some O)

type erase_type_scheme_view =
| Coq_erase_type_scheme_view_lam of aname * term * term
| Coq_erase_type_scheme_view_other of term

(** val erase_type_scheme_viewc : term -> erase_type_scheme_view **)

let erase_type_scheme_viewc = function
| Coq_tLambda (na, a, t1) -> Coq_erase_type_scheme_view_lam (na, a, t1)
| x -> Coq_erase_type_scheme_view_other x

(** val type_var_info_of_flag :
    aname -> PCUICEnvironment.global_env_ext -> term BasicAst.context_decl
    list -> term -> type_flag -> type_var_info **)

let type_var_info_of_flag na _UU03a3_ _UU0393_ t0 f =
  { Ex.tvar_name = na.binder_name; Ex.tvar_is_logical = f.is_logical;
    Ex.tvar_is_arity =
    (if is_arity _UU03a3_ _UU0393_ t0 f.conv_ar then true else false);
    Ex.tvar_is_sort =
    (match is_sort _UU03a3_ _UU0393_ t0 f.conv_ar with
     | Some _ -> true
     | None -> false) }

(** val erase_type_scheme_eta :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> tRel_kind Vector.t -> term -> arity_ass list
    -> Sort.t -> nat -> type_var_info list * box_type **)

let rec erase_type_scheme_eta x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 ar_ctx ar_univ next_tvar =
  match ar_ctx with
  | [] ->
    ([],
      (snd (erase_type_aux x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 None)))
  | a :: l ->
    let (a0, t1) = a in
    let inf =
      type_var_info_of_flag a0 r_UU03a3_ _UU0393_ t1
        (flag_of_type x_type x r_UU03a3_ _UU0393_ t1)
    in
    if inf.tvar_is_arity
    then let kind = RelTypeVar next_tvar in
         let new_next_tvar = S next_tvar in
         let (infs, bt) =
           erase_type_scheme_eta x_type x r_UU03a3_
             (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass a0 t1)) (Coq_cons
             (kind, (length _UU0393_), er_UU0393_)) (Coq_tApp
             ((lift (S O) O t0), (Coq_tRel O))) l ar_univ new_next_tvar
         in
         ((inf :: infs), bt)
    else let kind = RelOther in
         let (infs, bt) =
           erase_type_scheme_eta x_type x r_UU03a3_
             (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass a0 t1)) (Coq_cons
             (kind, (length _UU0393_), er_UU0393_)) (Coq_tApp
             ((lift (S O) O t0), (Coq_tRel O))) l ar_univ next_tvar
         in
         ((inf :: infs), bt)

(** val erase_type_scheme :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> tRel_kind Vector.t -> term -> arity_ass list
    -> Sort.t -> nat -> type_var_info list * box_type **)

let rec erase_type_scheme x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 ar_ctx ar_univ next_tvar =
  match ar_ctx with
  | [] ->
    ([],
      (snd (erase_type_aux x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 None)))
  | a :: l ->
    (match erase_type_scheme_viewc
             (ErasureFunction.inspect
               (reduce_term extraction_checker_flags RedFlags.nodelta x_type
                 x _UU0393_ t0)) with
     | Coq_erase_type_scheme_view_lam (na, a0, b) ->
       let inf =
         type_var_info_of_flag na r_UU03a3_ _UU0393_ a0
           (flag_of_type x_type x r_UU03a3_ _UU0393_ a0)
       in
       if inf.tvar_is_arity
       then let kind = RelTypeVar next_tvar in
            let new_next_tvar = S next_tvar in
            let (infs, bt) =
              erase_type_scheme x_type x r_UU03a3_
                (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a0))
                (Coq_cons (kind, (length _UU0393_), er_UU0393_)) b l ar_univ
                new_next_tvar
            in
            ((inf :: infs), bt)
       else let kind = RelOther in
            let (infs, bt) =
              erase_type_scheme x_type x r_UU03a3_
                (BasicAst.snoc _UU0393_ (PCUICEnvironment.vass na a0))
                (Coq_cons (kind, (length _UU0393_), er_UU0393_)) b l ar_univ
                next_tvar
            in
            ((inf :: infs), bt)
     | Coq_erase_type_scheme_view_other _ ->
       erase_type_scheme_eta x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0
         (a :: l) ar_univ next_tvar)

(** val erase_arity :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.constant_body -> conv_arity -> (type_var_info
    list * box_type) option **)

let erase_arity x_type x r_UU03a3_ cst car =
  match ErasureFunction.inspect (PCUICEnvironment.cst_body cst) with
  | Some t0 ->
    Some
      (erase_type_scheme x_type x r_UU03a3_ [] Coq_nil t0 car.conv_ar_context
        car.conv_ar_univ O)
  | None -> None

(** val erase_constant_decl :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.constant_body -> (constant_body, (type_var_info
    list * box_type) option) sum **)

let erase_constant_decl x_type x r_UU03a3_ cst =
  let { is_logical = _; conv_ar = conv_ar0 } =
    flag_of_type x_type x r_UU03a3_ [] (PCUICEnvironment.cst_type cst)
  in
  (match conv_ar0 with
   | Coq_inl c -> Coq_inr (erase_arity x_type x r_UU03a3_ cst c)
   | Coq_inr _ ->
     let erased_body = erase_constant_body x_type x cst in
     Coq_inl { Ex.cst_type =
     (erase_type x_type x r_UU03a3_ (PCUICEnvironment.cst_type cst));
     Ex.cst_body = (fst erased_body) })

(** val erase_ind_arity :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    P.PCUICEnvironment.context -> P.term -> type_var_info list **)

let erase_ind_arity x_type x r_UU03a3_ a a0 =
  let rec fix_F x0 =
    let _UU0393_ = let pr1,_ = x0 in pr1 in
    (match ErasureFunction.inspect
             (hnf extraction_checker_flags x_type x _UU0393_
               (let pr1,_ = let _,pr2 = x0 in pr2 in pr1)) with
     | Coq_tProd (na, a1, b) ->
       let hd =
         type_var_info_of_flag na r_UU03a3_ _UU0393_ a1
           (flag_of_type x_type x r_UU03a3_ _UU0393_ a1)
       in
       let tl =
         let y =
           (BasicAst.snoc _UU0393_ (P.PCUICEnvironment.vass na a1)),(b,__)
         in
         fix_F y
       in
       hd :: tl
     | _ -> [])
  in fix_F (a,(a0,__))

(** val ind_aname :
    P.PCUICEnvironment.one_inductive_body -> name binder_annot **)

let ind_aname oib =
  { binder_name = (Coq_nNamed (P.PCUICEnvironment.ind_name oib));
    binder_relevance = (P.PCUICEnvironment.ind_relevance oib) }

(** val arities_contexts :
    kername -> P.PCUICEnvironment.one_inductive_body list -> (P.term
    BasicAst.context_decl list, tRel_kind Vector.t) sigT **)

let arities_contexts mind oibs =
  let rec f oibs0 i _UU0393_ er_UU0393_ =
    match oibs0 with
    | [] -> Coq_existT (_UU0393_, er_UU0393_)
    | oib :: oibs1 ->
      f oibs1 (S i)
        (BasicAst.snoc _UU0393_
          (P.PCUICEnvironment.vass (ind_aname oib)
            (P.PCUICEnvironment.ind_type oib))) (Coq_cons ((RelInductive
        { inductive_mind = mind; inductive_ind = i }), (length _UU0393_),
        er_UU0393_))
  in f oibs O [] Coq_nil

type view_prod =
| Coq_view_prod_prod of aname * P.term * P.term
| Coq_view_prod_other of term

(** val view_prodc : P.term -> view_prod **)

let view_prodc = function
| P.Coq_tProd (na, a, b) -> Coq_view_prod_prod (na, a, b)
| x -> Coq_view_prod_other x

(** val erase_ind_ctor :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
    P.PCUICEnvironment.context -> tRel_kind Vector.t -> P.term -> nat ->
    type_var_info list -> box_type **)

let rec erase_ind_ctor x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 next_par = function
| [] -> snd (erase_type_aux x_type x r_UU03a3_ _UU0393_ er_UU0393_ t0 None)
| t1 :: l ->
  (match view_prodc
           (ErasureFunction.inspect
             (reduce_term extraction_checker_flags RedFlags.nodelta x_type x
               _UU0393_ t0)) with
   | Coq_view_prod_prod (na, a, b) ->
     let rel_kind = if t1.tvar_is_arity then RelTypeVar next_par else RelOther
     in
     let (_, dom) =
       erase_type_aux x_type x r_UU03a3_ _UU0393_ er_UU0393_ a None
     in
     let cod =
       erase_ind_ctor x_type x r_UU03a3_
         (BasicAst.snoc _UU0393_ (P.PCUICEnvironment.vass na a)) (Coq_cons
         (rel_kind, (length _UU0393_), er_UU0393_)) b (S next_par) l
     in
     TArr (dom, cod)
   | Coq_view_prod_other _ -> TAny)

(** val erase_ind_body :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> kername ->
    P.PCUICEnvironment.mutual_inductive_body ->
    P.PCUICEnvironment.one_inductive_body -> one_inductive_body **)

let erase_ind_body x_type x r_UU03a3_ mind mib oib =
  let is_propositional0 =
    match P.destArity [] (P.PCUICEnvironment.ind_type oib) with
    | Some p -> let (_, u) = p in Sort.is_propositional u
    | None -> false
  in
  let oib_tvars =
    erase_ind_arity x_type x r_UU03a3_ [] (P.PCUICEnvironment.ind_type oib)
  in
  let ctx =
    ErasureFunction.inspect
      (arities_contexts mind (P.PCUICEnvironment.ind_bodies mib))
  in
  let ind_params0 = firstn (P.PCUICEnvironment.ind_npars mib) oib_tvars in
  let erase_ind_ctor0 = fun p ->
    let bt =
      erase_ind_ctor x_type x r_UU03a3_ (projT1 ctx) (projT2 ctx)
        (P.PCUICEnvironment.cstr_type p) O ind_params0
    in
    let (ctor_args, _) = decompose_arr bt in
    let decomp_names =
      let rec decomp_names = function
      | P.Coq_tRel _ -> []
      | P.Coq_tVar _ -> []
      | P.Coq_tEvar (_, _) -> []
      | P.Coq_tSort _ -> []
      | P.Coq_tProd (na, _, b) -> na.binder_name :: (decomp_names b)
      | P.Coq_tLetIn (_, _, _, b) -> decomp_names b
      | _ -> []
      in decomp_names
    in
    (((P.PCUICEnvironment.cstr_name p),
    (combine (decomp_names (P.PCUICEnvironment.cstr_type p)) ctor_args)),
    (P.PCUICEnvironment.cstr_arity p))
  in
  let ctors =
    map_In (P.PCUICEnvironment.ind_ctors oib) (fun p _ -> erase_ind_ctor0 p)
  in
  let erase_ind_proj = fun p -> ((P.PCUICEnvironment.proj_name p), TBox) in
  let projs0 =
    map_In (P.PCUICEnvironment.ind_projs oib) (fun p _ -> erase_ind_proj p)
  in
  { Ex.ind_name = (P.PCUICEnvironment.ind_name oib); Ex.ind_propositional =
  is_propositional0; Ex.ind_kelim = (P.PCUICEnvironment.ind_kelim oib);
  Ex.ind_type_vars = oib_tvars; Ex.ind_ctors = ctors; Ex.ind_projs = projs0 }

(** val erase_ind :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> kername ->
    P.PCUICEnvironment.mutual_inductive_body -> mutual_inductive_body **)

let erase_ind x_type x r_UU03a3_ kn mib =
  let inds0 =
    map_In (P.PCUICEnvironment.ind_bodies mib) (fun oib _ ->
      erase_ind_body x_type x r_UU03a3_ kn mib oib)
  in
  { Ex.ind_finite = (P.PCUICEnvironment.ind_finite mib); Ex.ind_npars =
  (P.PCUICEnvironment.ind_npars mib); Ex.ind_bodies = inds0 }

(** val fake_guard_impl :
    coq_FixCoFix -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> term BasicAst.mfixpoint -> bool **)

let fake_guard_impl _ _ _ _ =
  true

(** val fake_guard_impl_instance : abstract_guard_impl **)

let fake_guard_impl_instance =
  fake_guard_impl

(** val erase_global_decl :
    abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.global_decl -> global_decl **)

let erase_global_decl x_type x _UU03a3_ext kn = function
| PCUICEnvironment.ConstantDecl cst ->
  let filtered_var = erase_constant_decl x_type x _UU03a3_ext cst in
  (match filtered_var with
   | Coq_inl cst0 -> ConstantDecl cst0
   | Coq_inr ta -> TypeAliasDecl ta)
| PCUICEnvironment.InductiveDecl mib ->
  InductiveDecl (erase_ind x_type x _UU03a3_ext kn mib)

(** val box_type_deps : box_type -> KernameSet.t **)

let rec box_type_deps = function
| TArr (t1, t2) -> KernameSet.union (box_type_deps t1) (box_type_deps t2)
| TApp (t1, t2) -> KernameSet.union (box_type_deps t1) (box_type_deps t2)
| TInd ind -> KernameSet.singleton ind.inductive_mind
| TConst kn -> KernameSet.singleton kn
| _ -> KernameSet.empty

(** val decl_deps : global_decl -> KernameSet.t **)

let decl_deps = function
| ConstantDecl body ->
  let seen =
    match body.cst_body with
    | Some body0 -> term_global_deps body0
    | None -> KernameSet.empty
  in
  KernameSet.union (box_type_deps (snd body.cst_type)) seen
| InductiveDecl mib ->
  let one_inductive_body_deps = fun oib ->
    let seen =
      fold_left (fun seen pat ->
        let (_, bt) = pat in KernameSet.union seen (box_type_deps bt))
        (flat_map (compose snd fst) oib.ind_ctors) KernameSet.empty
    in
    fold_left (fun seen0 bt -> KernameSet.union seen0 (box_type_deps bt))
      (map snd oib.ind_projs) seen
  in
  fold_left (fun seen oib ->
    KernameSet.union seen (one_inductive_body_deps oib)) mib.ind_bodies
    KernameSet.empty
| TypeAliasDecl o ->
  (match o with
   | Some p -> let (_, ty) = p in box_type_deps ty
   | None -> KernameSet.empty)

(** val erase_global_decls_deps_recursive :
    abstract_env_impl -> __ -> PCUICEnvironment.global_declarations ->
    ContextSet.t -> Environment.Retroknowledge.t -> KernameSet.t -> (kername
    -> bool) -> global_env **)

let rec erase_global_decls_deps_recursive x_type x decls univs retro include0 ignore_deps =
  match decls with
  | [] -> []
  | p :: _UU03a3_ ->
    let (kn, decl) = p in
    let x' =
      (abstract_env_impl_abstract_env_struct extraction_checker_flags x_type).abstract_pop_decls
        x
    in
    let xext =
      abstract_make_wf_env_ext extraction_checker_flags x_type x'
        (universes_decl_of_decl decl)
    in
    let env = ({ PCUICEnvironment.universes = univs;
      PCUICEnvironment.declarations = _UU03a3_;
      PCUICEnvironment.retroknowledge = retro },
      (universes_decl_of_decl decl))
    in
    if KernameSet.mem kn include0
    then let decl0 = erase_global_decl x_type xext env kn decl in
         let with_deps = negb (ignore_deps kn) in
         let new_deps =
           if with_deps then decl_deps decl0 else KernameSet.empty
         in
         let _UU03a3_er =
           erase_global_decls_deps_recursive x_type x' _UU03a3_ univs retro
             (KernameSet.union new_deps include0) ignore_deps
         in
         ((kn, with_deps), decl0) :: _UU03a3_er
    else erase_global_decls_deps_recursive x_type x' _UU03a3_ univs retro
           include0 ignore_deps
