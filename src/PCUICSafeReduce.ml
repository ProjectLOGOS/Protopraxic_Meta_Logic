open BasicAst
open Datatypes
open Kernames
open List0
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICCases
open PCUICErrors
open PCUICNormal
open PCUICPosition
open PCUICWfEnv
open Specif
open Universes0
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val inspect : 'a1 -> 'a1 **)

let inspect x =
  x

type construct_view =
| Coq_view_construct of inductive * nat * Instance.t
| Coq_view_other of term

(** val construct_viewc : term -> construct_view **)

let construct_viewc = function
| Coq_tConstruct (ind, n, ui) -> Coq_view_construct (ind, n, ui)
| x -> Coq_view_other x

type red_view =
| Coq_red_view_Rel of nat * stack
| Coq_red_view_LetIn of aname * term * term * term * stack
| Coq_red_view_Const of kername * Instance.t * stack
| Coq_red_view_App of term * term * stack
| Coq_red_view_Lambda of aname * term * term * term * stack_entry list
| Coq_red_view_Fix of term mfixpoint * nat * stack
| Coq_red_view_Case of case_info * term predicate * term * term branch list
   * stack
| Coq_red_view_Proj of projection * term * stack
| Coq_red_view_other of term * stack

(** val red_viewc : term -> stack -> red_view **)

let red_viewc t0 _UU03c0_ =
  match t0 with
  | Coq_tRel n -> Coq_red_view_Rel (n, _UU03c0_)
  | Coq_tLambda (na, a, t1) ->
    (match _UU03c0_ with
     | [] -> Coq_red_view_other ((Coq_tLambda (na, a, t1)), [])
     | s :: l ->
       (match s with
        | App_l v -> Coq_red_view_Lambda (na, a, t1, v, l)
        | x -> Coq_red_view_other ((Coq_tLambda (na, a, t1)), (x :: l))))
  | Coq_tLetIn (na, b, b0, t1) -> Coq_red_view_LetIn (na, b, b0, t1, _UU03c0_)
  | Coq_tApp (u, v) -> Coq_red_view_App (u, v, _UU03c0_)
  | Coq_tConst (k, ui) -> Coq_red_view_Const (k, ui, _UU03c0_)
  | Coq_tCase (indn, p, c, brs) ->
    Coq_red_view_Case (indn, p, c, brs, _UU03c0_)
  | Coq_tProj (p, c) -> Coq_red_view_Proj (p, c, _UU03c0_)
  | Coq_tFix (mfix, idx) -> Coq_red_view_Fix (mfix, idx, _UU03c0_)
  | x -> Coq_red_view_other (x, _UU03c0_)

type construct_cofix_view =
| Coq_ccview_construct of inductive * nat * Instance.t
| Coq_ccview_cofix of term mfixpoint * nat
| Coq_ccview_other of term

(** val cc_viewc : term -> construct_cofix_view **)

let cc_viewc = function
| Coq_tConstruct (ind, n, ui) -> Coq_ccview_construct (ind, n, ui)
| Coq_tCoFix (mfix, idx) -> Coq_ccview_cofix (mfix, idx)
| x -> Coq_ccview_other x

type construct0_cofix_view =
| Coq_cc0view_construct of inductive * Instance.t
| Coq_cc0view_cofix of term mfixpoint * nat
| Coq_cc0view_other of term

(** val cc0_viewc : term -> construct0_cofix_view **)

let cc0_viewc = function
| Coq_tConstruct (ind, n, ui) ->
  (match n with
   | O -> Coq_cc0view_construct (ind, ui)
   | S n0 -> Coq_cc0view_other (Coq_tConstruct (ind, (S n0), ui)))
| Coq_tCoFix (mfix, idx) -> Coq_cc0view_cofix (mfix, idx)
| x -> Coq_cc0view_other x

(** val _reduce_stack :
    checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
    PCUICEnvironment.context -> term -> stack -> (term -> stack -> __ ->
    (term * stack)) -> (term * stack) **)

let _reduce_stack cf flags x_type x _UU0393_ t0 _UU03c0_ reduce =
  match red_viewc t0 _UU03c0_ with
  | Coq_red_view_Rel (c, _UU03c0_0) ->
    if flags.RedFlags.zeta
    then (match inspect
                  (nth_error (app_context _UU0393_ (stack_context _UU03c0_0))
                    c) with
          | Some c0 ->
            (match inspect c0.decl_body with
             | Some t1 -> reduce (lift (S c) O t1) _UU03c0_0 __
             | None -> ((Coq_tRel c), _UU03c0_0))
          | None -> assert false (* absurd case *))
    else ((Coq_tRel c), _UU03c0_0)
  | Coq_red_view_LetIn (a, b, b0, c, _UU03c0_0) ->
    if flags.RedFlags.zeta
    then reduce (subst1 b O c) _UU03c0_0 __
    else ((Coq_tLetIn (a, b, b0, c)), _UU03c0_0)
  | Coq_red_view_Const (c, u, _UU03c0_0) ->
    if flags.RedFlags.delta
    then (match inspect
                  ((abstract_env_impl_abstract_env_struct cf x_type).abstract_env_lookup
                    x c) with
          | Some g ->
            (match g with
             | PCUICEnvironment.ConstantDecl c0 ->
               let { PCUICEnvironment.cst_type = _;
                 PCUICEnvironment.cst_body = cst_body0;
                 PCUICEnvironment.cst_universes = _;
                 PCUICEnvironment.cst_relevance = _ } = c0
               in
               (match cst_body0 with
                | Some t1 ->
                  let body' = subst_instance subst_instance_constr u t1 in
                  reduce body' _UU03c0_0 __
                | None -> ((Coq_tConst (c, u)), _UU03c0_0))
             | PCUICEnvironment.InductiveDecl _ ->
               assert false (* absurd case *))
          | None -> assert false (* absurd case *))
    else ((Coq_tConst (c, u)), _UU03c0_0)
  | Coq_red_view_App (f, a, _UU03c0_0) -> reduce f ((App_l a) :: _UU03c0_0) __
  | Coq_red_view_Lambda (na, a, t1, a0, args) ->
    if inspect flags.RedFlags.beta
    then reduce (subst1 a0 O t1) args __
    else ((Coq_tLambda (na, a, t1)), ((App_l a0) :: args))
  | Coq_red_view_Fix (mfix, idx, _UU03c0_0) ->
    if flags.RedFlags.fix_
    then (match inspect (unfold_fix mfix idx) with
          | Some p ->
            let (n, t1) = p in
            (match inspect (decompose_stack_at _UU03c0_0 n) with
             | Some p0 ->
               let (p1, s) = p0 in
               let (l, t2) = p1 in
               let (t3, s0) =
                 inspect (reduce t2 ((Fix_app (mfix, idx, l)) :: s) __)
               in
               (match construct_viewc t3 with
                | Coq_view_construct (ind, n0, ui) ->
                  let (l0, _) = inspect (decompose_stack s0) in
                  reduce t1
                    (appstack l ((App_l
                      (mkApps (Coq_tConstruct (ind, n0, ui)) l0)) :: s)) __
                | Coq_view_other t4 ->
                  let (l0, _) = inspect (decompose_stack s0) in
                  ((Coq_tFix (mfix, idx)),
                  (appstack l ((App_l (mkApps t4 l0)) :: s))))
             | None -> ((Coq_tFix (mfix, idx)), _UU03c0_0))
          | None -> ((Coq_tFix (mfix, idx)), _UU03c0_0))
    else ((Coq_tFix (mfix, idx)), _UU03c0_0)
  | Coq_red_view_Case (ci, p, c, brs, _UU03c0_0) ->
    if flags.RedFlags.iota
    then let (t1, s) =
           inspect (reduce c ((Case_discr (ci, p, brs)) :: _UU03c0_0) __)
         in
         let (l, _) = inspect (decompose_stack s) in
         (match cc_viewc t1 with
          | Coq_ccview_construct (_, n, _) ->
            (match inspect (nth_error brs n) with
             | Some b -> reduce (iota_red ci.ci_npar p l b) _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_ccview_cofix (mfix, idx) ->
            (match inspect (unfold_cofix mfix idx) with
             | Some p0 ->
               let (_, t2) = p0 in
               reduce (Coq_tCase (ci, p, (mkApps t2 l), brs)) _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_ccview_other t2 ->
            ((Coq_tCase (ci, p, (mkApps t2 l), brs)), _UU03c0_0))
    else ((Coq_tCase (ci, p, c, brs)), _UU03c0_0)
  | Coq_red_view_Proj (p, c, _UU03c0_0) ->
    if flags.RedFlags.iota
    then let (t1, s) = inspect (reduce c ((Proj p) :: _UU03c0_0) __) in
         let (l, _) = inspect (decompose_stack s) in
         (match cc0_viewc t1 with
          | Coq_cc0view_construct (_, _) ->
            (match inspect (nth_error l (add p.proj_npars p.proj_arg)) with
             | Some t2 -> reduce t2 _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_cc0view_cofix (mfix, idx) ->
            (match inspect (unfold_cofix mfix idx) with
             | Some p0 ->
               let (_, t2) = p0 in
               reduce (Coq_tProj (p, (mkApps t2 l))) _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_cc0view_other t2 ->
            ((Coq_tProj (p, (mkApps t2 l))), _UU03c0_0))
    else ((Coq_tProj (p, c)), _UU03c0_0)
  | Coq_red_view_other (t1, _UU03c0_0) -> (t1, _UU03c0_0)

(** val reduce_stack_full :
    checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
    PCUICEnvironment.context -> term -> stack -> (term * stack) **)

let reduce_stack_full cf flags x_type x _UU0393_ a a0 =
  let rec fix_F x0 =
    _reduce_stack cf flags x_type x _UU0393_ (let pr1,_ = x0 in pr1)
      (let pr1,_ = let _,pr2 = x0 in pr2 in pr1) (fun t' _UU03c0_' _ ->
      let y = t',(_UU03c0_',__) in fix_F y)
  in fix_F (a,(a0,__))

(** val reduce_stack :
    checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
    PCUICEnvironment.context -> term -> stack -> term * stack **)

let reduce_stack =
  reduce_stack_full

(** val reduce_term :
    checker_flags -> RedFlags.t -> abstract_env_impl -> __ ->
    PCUICEnvironment.context -> term -> term **)

let reduce_term cf flags x_type x _UU0393_ t0 =
  zip (reduce_stack cf flags x_type x _UU0393_ t0 [])

(** val hnf :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> term **)

let hnf cf x_type x _UU0393_ t0 =
  reduce_term cf RedFlags.default x_type x _UU0393_ t0

(** val reduce_to_sort :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (Sort.t, __) sigT typing_result_comp **)

let reduce_to_sort cf x_type x _UU0393_ t0 =
  match view_sortc t0 with
  | Coq_view_sort_sort s -> Checked_comp (Coq_existT (s, __))
  | Coq_view_sort_other t1 ->
    (match view_sortc (inspect (hnf cf x_type x _UU0393_ t1)) with
     | Coq_view_sort_sort s -> Checked_comp (Coq_existT (s, __))
     | Coq_view_sort_other t2 -> TypeError_comp (NotASort t2))

(** val reduce_to_prod :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (aname, (term, (term, __) sigT) sigT) sigT typing_result_comp **)

let reduce_to_prod cf x_type x _UU0393_ t0 =
  match view_prodc t0 with
  | Coq_view_prod_prod (na, a, b) ->
    Checked_comp (Coq_existT (na, (Coq_existT (a, (Coq_existT (b, __))))))
  | Coq_view_prod_other t1 ->
    (match view_prodc (inspect (hnf cf x_type x _UU0393_ t1)) with
     | Coq_view_prod_prod (na, a, b) ->
       Checked_comp (Coq_existT (na, (Coq_existT (a, (Coq_existT (b, __))))))
     | Coq_view_prod_other t2 -> TypeError_comp (NotAProduct (t1, t2)))

(** val reduce_to_ind :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> (inductive, (Instance.t, (term list, __) sigT) sigT) sigT
    typing_result_comp **)

let reduce_to_ind cf x_type x _UU0393_ t0 =
  let (t1, l) = inspect (decompose_app t0) in
  (match view_indc t1 with
   | Coq_view_ind_tInd (ind, u) ->
     Checked_comp (Coq_existT (ind, (Coq_existT (u, (Coq_existT (l, __))))))
   | Coq_view_ind_other _ ->
     let (t2, s) =
       inspect (reduce_stack cf RedFlags.default x_type x _UU0393_ t0 [])
     in
     (match view_indc t2 with
      | Coq_view_ind_tInd (ind, u) ->
        let (l0, _) = inspect (decompose_stack s) in
        Checked_comp (Coq_existT (ind, (Coq_existT (u, (Coq_existT (l0,
        __))))))
      | Coq_view_ind_other _ -> TypeError_comp (NotAnInductive t0)))
