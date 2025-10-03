open BasicAst
open Datatypes
open Kernames
open List0
open MCList
open PCUICAst
open PCUICCases
open PCUICPrimitive
open Primitive
open Specif
open Universes0
open Monad_utils

type def_hole =
| Coq_def_hole_type of aname * term * nat
| Coq_def_hole_body of aname * term * nat

type mfix_hole = (term mfixpoint * def_hole) * term mfixpoint

type predicate_hole =
| Coq_pred_hole_params of term list * term list * Instance.t
   * PCUICEnvironment.context * term
| Coq_pred_hole_return of term list * Instance.t * PCUICEnvironment.context

type branch_hole =
  PCUICEnvironment.context
  (* singleton inductive, whose constructor was branch_hole_body *)

type branches_hole = (term branch list * branch_hole) * term branch list

type stack_entry =
| App_l of term
| App_r of term
| Fix_app of term mfixpoint * nat * term list
| Fix of mfix_hole * nat
| CoFix_app of term mfixpoint * nat * term list
| CoFix of mfix_hole * nat
| Case_pred of case_info * predicate_hole * term * term branch list
| Case_discr of case_info * term predicate * term branch list
| Case_branch of case_info * term predicate * term * branches_hole
| Proj of projection
| Prod_l of aname * term
| Prod_r of aname * term
| Lambda_ty of aname * term
| Lambda_bd of aname * term
| LetIn_bd of aname * term * term
| LetIn_ty of aname * term * term
| LetIn_in of aname * term * term
| PrimArray_ty of Level.t * term list * term
| PrimArray_def of Level.t * term list * term
| PrimArray_val of Level.t * term list * term list * term * term

type stack = stack_entry list

(** val fill_mfix_hole : mfix_hole -> term -> term mfixpoint **)

let fill_mfix_hole pat t0 =
  let (p, mfix2) = pat in
  let (mfix1, m) = p in
  let def0 =
    match m with
    | Coq_def_hole_type (dname0, dbody0, rarg0) ->
      { dname = dname0; dtype = t0; dbody = dbody0; rarg = rarg0 }
    | Coq_def_hole_body (dname0, dtype0, rarg0) ->
      { dname = dname0; dtype = dtype0; dbody = t0; rarg = rarg0 }
  in
  app mfix1 (def0 :: mfix2)

(** val fill_predicate_hole : predicate_hole -> term -> term predicate **)

let fill_predicate_hole p t0 =
  match p with
  | Coq_pred_hole_params (params1, params2, puinst0, pcontext0, preturn0) ->
    { pparams = (app params1 (t0 :: params2)); puinst = puinst0; pcontext =
      pcontext0; preturn = preturn0 }
  | Coq_pred_hole_return (pparams0, puinst0, pcontext0) ->
    { pparams = pparams0; puinst = puinst0; pcontext = pcontext0; preturn =
      t0 }

(** val fill_branches_hole : branches_hole -> term -> term branch list **)

let fill_branches_hole pat t0 =
  let (p, brs2) = pat in
  let (brs1, br) = p in
  let br0 = { bcontext = br; bbody = t0 } in app brs1 (br0 :: brs2)

(** val fill_hole : term -> stack_entry -> term **)

let fill_hole t0 = function
| App_l v -> Coq_tApp (t0, v)
| App_r u -> Coq_tApp (u, t0)
| Fix_app (mfix, idx, args) ->
  Coq_tApp ((mkApps (Coq_tFix (mfix, idx)) args), t0)
| Fix (mfix, idx) -> Coq_tFix ((fill_mfix_hole mfix t0), idx)
| CoFix_app (mfix, idx, args) ->
  Coq_tApp ((mkApps (Coq_tCoFix (mfix, idx)) args), t0)
| CoFix (mfix, idx) -> Coq_tCoFix ((fill_mfix_hole mfix t0), idx)
| Case_pred (ci, p, c, brs) ->
  Coq_tCase (ci, (fill_predicate_hole p t0), c, brs)
| Case_discr (ci, p, brs) -> Coq_tCase (ci, p, t0, brs)
| Case_branch (ci, p, c, brs) ->
  Coq_tCase (ci, p, c, (fill_branches_hole brs t0))
| Proj p -> Coq_tProj (p, t0)
| Prod_l (na, b) -> Coq_tProd (na, t0, b)
| Prod_r (na, a) -> Coq_tProd (na, a, t0)
| Lambda_ty (na, b) -> Coq_tLambda (na, t0, b)
| Lambda_bd (na, a) -> Coq_tLambda (na, a, t0)
| LetIn_bd (na, b, u) -> Coq_tLetIn (na, t0, b, u)
| LetIn_ty (na, b, u) -> Coq_tLetIn (na, b, t0, u)
| LetIn_in (na, b, b0) -> Coq_tLetIn (na, b, b0, t0)
| PrimArray_ty (l, v, def0) ->
  Coq_tPrim (Coq_existT (Coq_primArray, (Coq_primArrayModel { array_level =
    l; array_type = t0; array_default = def0; array_value = v })))
| PrimArray_def (l, v, ty) ->
  Coq_tPrim (Coq_existT (Coq_primArray, (Coq_primArrayModel { array_level =
    l; array_type = ty; array_default = t0; array_value = v })))
| PrimArray_val (l, bef, after, def0, ty) ->
  Coq_tPrim (Coq_existT (Coq_primArray, (Coq_primArrayModel { array_level =
    l; array_type = ty; array_default = def0; array_value =
    (app bef (t0 :: after)) })))

(** val zipc : term -> stack -> term **)

let rec zipc t0 = function
| [] -> t0
| se :: stack1 -> zipc (fill_hole t0 se) stack1

(** val zip : (term * stack) -> term **)

let zip t0 =
  zipc (fst t0) (snd t0)

(** val decompose_stack : stack -> term list * stack **)

let rec decompose_stack _UU03c0_ = match _UU03c0_ with
| [] -> ([], _UU03c0_)
| s :: _UU03c0_0 ->
  (match s with
   | App_l u ->
     let (l, _UU03c0_1) = decompose_stack _UU03c0_0 in ((u :: l), _UU03c0_1)
   | _ -> ([], _UU03c0_))

(** val appstack : term list -> stack -> stack **)

let appstack l _UU03c0_ =
  app (map (fun x -> App_l x) l) _UU03c0_

(** val decompose_stack_at :
    stack_entry list -> nat -> ((term list * term) * stack) option **)

let rec decompose_stack_at _UU03c0_ n =
  match _UU03c0_ with
  | [] -> None
  | y :: _UU03c0_0 ->
    (match y with
     | App_l u ->
       (match n with
        | O -> ret (Obj.magic option_monad) (([], u), _UU03c0_0)
        | S n0 ->
          bind (Obj.magic option_monad) (decompose_stack_at _UU03c0_0 n0)
            (fun r ->
            let (y0, _UU03c0_1) = r in
            let (l, v) = y0 in
            ret (Obj.magic option_monad) (((u :: l), v), _UU03c0_1)))
     | _ -> None)

(** val fix_context_alt : (aname * term) list -> PCUICEnvironment.context **)

let fix_context_alt l =
  List0.rev
    (mapi (fun i d -> PCUICEnvironment.vass (fst d) (lift i O (snd d))) l)

(** val def_sig : term def -> aname * term **)

let def_sig d =
  (d.dname, d.dtype)

(** val mfix_hole_context : mfix_hole -> PCUICEnvironment.context **)

let mfix_hole_context = function
| (p, mfix2) ->
  let (mfix1, def0) = p in
  (match def0 with
   | Coq_def_hole_type (_, _, _) -> []
   | Coq_def_hole_body (na, ty, _) ->
     fix_context_alt
       (app (map def_sig mfix1) ((na, ty) :: (map def_sig mfix2))))

(** val predicate_hole_context :
    predicate_hole -> PCUICEnvironment.context **)

let predicate_hole_context = function
| Coq_pred_hole_params (_, _, _, _, _) -> []
| Coq_pred_hole_return (pparams0, puinst0, pcontext0) ->
  inst_case_context pparams0 puinst0 pcontext0

(** val branches_hole_context :
    term predicate -> branches_hole -> PCUICEnvironment.context **)

let branches_hole_context p = function
| (p0, _) -> let (_, br) = p0 in inst_case_context p.pparams p.puinst br

(** val stack_entry_context : stack_entry -> PCUICEnvironment.context **)

let stack_entry_context = function
| Fix (mfix, _) -> mfix_hole_context mfix
| CoFix (mfix, _) -> mfix_hole_context mfix
| Case_pred (_, p, _, _) -> predicate_hole_context p
| Case_branch (_, p, _, brs) -> branches_hole_context p brs
| Prod_r (na, a) -> (PCUICEnvironment.vass na a) :: []
| Lambda_bd (na, a) -> (PCUICEnvironment.vass na a) :: []
| LetIn_in (na, b, b0) -> (PCUICEnvironment.vdef na b b0) :: []
| _ -> []

(** val stack_context : stack -> PCUICEnvironment.context **)

let stack_context =
  flat_map stack_entry_context
