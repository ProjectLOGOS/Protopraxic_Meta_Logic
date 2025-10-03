open BasicAst
open Datatypes
open Kernames
open List0
open PCUICAst
open PCUICCases
open PCUICErrors
open PCUICSafeReduce
open PCUICTyping
open PCUICWfEnv
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type principal_type = (term, __) sigT

type principal_sort = (Sort.t, __) sigT

(** val principal_type_type :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> principal_type -> term **)

let principal_type_type _ _ _ _ _ =
  projT1

(** val principal_sort_sort :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> principal_sort -> Sort.t **)

let principal_sort_sort _ _ _ _ _ =
  projT1

(** val infer_as_sort :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> principal_type -> principal_sort **)

let infer_as_sort cf x_type x _UU0393_ t0 tx =
  let filtered_var =
    reduce_to_sort cf x_type x _UU0393_
      (principal_type_type cf x_type x _UU0393_ t0 tx)
  in
  (match filtered_var with
   | Checked_comp a -> let Coq_existT (u, _) = a in Coq_existT (u, __)
   | TypeError_comp _ -> assert false (* absurd case *))

(** val infer_as_prod :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (aname, (term, (term, __) sigT) sigT) sigT **)

let infer_as_prod cf x_type x _UU0393_ t0 =
  let filtered_var = reduce_to_prod cf x_type x _UU0393_ t0 in
  (match filtered_var with
   | Checked_comp p -> p
   | TypeError_comp _ -> assert false (* absurd case *))

(** val lookup_ind_decl :
    checker_flags -> abstract_env_impl -> __ -> inductive ->
    (PCUICEnvironment.mutual_inductive_body,
    (PCUICEnvironment.one_inductive_body, __) sigT) sigT typing_result **)

let lookup_ind_decl cf x_type x ind =
  match inspect
          ((abstract_env_impl_abstract_env_struct cf x_type).abstract_env_lookup
            x ind.inductive_mind) with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl _ ->
       raise (Obj.magic monad_exc) (UndeclaredInductive ind)
     | PCUICEnvironment.InductiveDecl m ->
       (match inspect
                (nth_error (PCUICEnvironment.ind_bodies m) ind.inductive_ind) with
        | Some o -> Checked (Coq_existT (m, (Coq_existT (o, __))))
        | None -> raise (Obj.magic monad_exc) (UndeclaredInductive ind)))
  | None -> raise (Obj.magic monad_exc) (UndeclaredInductive ind)

(** val infer :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> principal_type **)

let rec infer cf x_type x _UU0393_ = function
| Coq_tRel n ->
  (match inspect
           (option_map
             (let g0 = lift (S n) O in
              let f0 = fun c -> c.decl_type in (fun x0 -> g0 (f0 x0)))
             (nth_error _UU0393_ n)) with
   | Some t1 -> Coq_existT (t1, __)
   | None -> assert false (* absurd case *))
| Coq_tSort u -> Coq_existT ((Coq_tSort (Sort.super u)), __)
| Coq_tProd (na, a, b) ->
  let ty1 = infer cf x_type x _UU0393_ a in
  let s1 = infer_as_sort cf x_type x _UU0393_ a ty1 in
  let ty2 = infer cf x_type x (snoc _UU0393_ (PCUICEnvironment.vass na a)) b
  in
  let s2 =
    infer_as_sort cf x_type x (snoc _UU0393_ (PCUICEnvironment.vass na a)) b
      ty2
  in
  Coq_existT ((Coq_tSort
  (Sort.sort_of_product (principal_sort_sort cf x_type x _UU0393_ a s1)
    (principal_sort_sort cf x_type x
      (snoc _UU0393_ (PCUICEnvironment.vass na a)) b s2))), __)
| Coq_tLambda (na, a, t1) ->
  let t2 = infer cf x_type x (snoc _UU0393_ (PCUICEnvironment.vass na a)) t1
  in
  Coq_existT ((Coq_tProd (na, a,
  (principal_type_type cf x_type x
    (snoc _UU0393_ (PCUICEnvironment.vass na a)) t1 t2))), __)
| Coq_tLetIn (na, b, b0, t1) ->
  let b'_ty =
    infer cf x_type x (snoc _UU0393_ (PCUICEnvironment.vdef na b b0)) t1
  in
  Coq_existT ((Coq_tLetIn (na, b, b0,
  (principal_type_type cf x_type x
    (snoc _UU0393_ (PCUICEnvironment.vdef na b b0)) t1 b'_ty))), __)
| Coq_tApp (u, v) ->
  let ty = infer cf x_type x _UU0393_ u in
  let pi =
    infer_as_prod cf x_type x _UU0393_
      (principal_type_type cf x_type x _UU0393_ u ty)
  in
  Coq_existT ((subst1 v O (projT1 (projT2 (projT2 pi)))), __)
| Coq_tConst (k, ui) ->
  (match inspect
           ((abstract_env_impl_abstract_env_struct cf x_type).abstract_env_lookup
             x k) with
   | Some g ->
     (match g with
      | PCUICEnvironment.ConstantDecl c ->
        Coq_existT
          ((subst_instance subst_instance_constr ui
             (PCUICEnvironment.cst_type c)), __)
      | PCUICEnvironment.InductiveDecl _ -> assert false (* absurd case *))
   | None -> assert false (* absurd case *))
| Coq_tInd (ind, ui) ->
  (match inspect (lookup_ind_decl cf x_type x ind) with
   | Checked a ->
     Coq_existT
       ((subst_instance subst_instance_constr ui
          (PCUICEnvironment.ind_type (projT1 (projT2 a)))), __)
   | TypeError _ -> assert false (* absurd case *))
| Coq_tConstruct (ind, n, ui) ->
  (match inspect (lookup_ind_decl cf x_type x ind) with
   | Checked a ->
     (match inspect
              (nth_error (PCUICEnvironment.ind_ctors (projT1 (projT2 a))) n) with
      | Some c ->
        Coq_existT ((type_of_constructor (projT1 a) c (ind, n) ui), __)
      | None -> assert false (* absurd case *))
   | TypeError _ -> assert false (* absurd case *))
| Coq_tCase (indn, p, c, _) ->
  (match inspect
           (reduce_to_ind cf x_type x _UU0393_
             (principal_type_type cf x_type x _UU0393_ c
               (infer cf x_type x _UU0393_ c))) with
   | Checked_comp a ->
     let ptm =
       PCUICEnvironment.it_mkLambda_or_LetIn (inst_case_predicate_context p)
         p.preturn
     in
     Coq_existT
     ((mkApps ptm
        (app (skipn indn.ci_npar (projT1 (projT2 (projT2 a)))) (c :: []))),
     __)
   | TypeError_comp _ -> assert false (* absurd case *))
| Coq_tProj (p, c) ->
  (match inspect (lookup_ind_decl cf x_type x p.proj_ind) with
   | Checked a ->
     (match inspect
              (nth_error (PCUICEnvironment.ind_projs (projT1 (projT2 a)))
                p.proj_arg) with
      | Some p0 ->
        (match inspect
                 (reduce_to_ind cf x_type x _UU0393_
                   (principal_type_type cf x_type x _UU0393_ c
                     (infer cf x_type x _UU0393_ c))) with
         | Checked_comp a0 ->
           let ty = PCUICEnvironment.proj_type p0 in
           Coq_existT
           ((subst (c :: (rev (projT1 (projT2 (projT2 a0))))) O
              (subst_instance subst_instance_constr (projT1 (projT2 a0)) ty)),
           __)
         | TypeError_comp _ -> assert false (* absurd case *))
      | None -> assert false (* absurd case *))
   | TypeError _ -> assert false (* absurd case *))
| Coq_tFix (mfix, idx) ->
  (match inspect (nth_error mfix idx) with
   | Some d -> Coq_existT (d.dtype, __)
   | None -> assert false (* absurd case *))
| Coq_tCoFix (mfix, idx) ->
  (match inspect (nth_error mfix idx) with
   | Some d -> Coq_existT (d.dtype, __)
   | None -> assert false (* absurd case *))
| Coq_tPrim prim ->
  (match inspect
           ((abstract_env_impl_abstract_env_struct cf x_type).abstract_primitive_constant
             x (projT1 prim)) with
   | Some k -> Coq_existT ((prim_type prim k), __)
   | None -> assert false (* absurd case *))
| _ -> assert false (* absurd case *)

(** val type_of_typing :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (term, __) sigT **)

let type_of_typing cf x_type x _UU0393_ t0 =
  let it = infer cf x_type x _UU0393_ t0 in Coq_existT ((projT1 it), __)

(** val sort_of_type :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (Sort.t, __) sigT **)

let sort_of_type cf x_type x _UU0393_ t0 =
  match inspect
          (reduce_to_sort cf x_type x _UU0393_
            (projT1 (type_of_typing cf x_type x _UU0393_ t0))) with
  | Checked_comp a -> let Coq_existT (x0, _) = a in Coq_existT (x0, __)
  | TypeError_comp _ -> assert false (* absurd case *)
