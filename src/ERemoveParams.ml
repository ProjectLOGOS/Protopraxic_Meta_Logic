open Datatypes
open EAst
open EEnvMap
open EEtaExpanded
open EPrimitive
open EProgram
open ESpineView
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd

(** val strip : GlobalContextMap.t -> term -> term **)

let rec strip _UU03a3_ x =
  match TermSpineView.view x with
  | TermSpineView.Coq_tBox -> Coq_tBox
  | TermSpineView.Coq_tRel n -> Coq_tRel n
  | TermSpineView.Coq_tVar n -> Coq_tVar n
  | TermSpineView.Coq_tEvar (n, e) ->
    Coq_tEvar (n, (map_InP e (fun x0 _ -> strip _UU03a3_ x0)))
  | TermSpineView.Coq_tLambda (n, b) -> Coq_tLambda (n, (strip _UU03a3_ b))
  | TermSpineView.Coq_tLetIn (n, b, b') ->
    Coq_tLetIn (n, (strip _UU03a3_ b), (strip _UU03a3_ b'))
  | TermSpineView.Coq_tApp (f, l) ->
    (match construct_viewc f with
     | Coq_view_construct (ind, n, block_args) ->
       (match GlobalContextMap.lookup_inductive_pars _UU03a3_
                ind.inductive_mind with
        | Some n0 ->
          mkApps (Coq_tConstruct (ind, n, block_args))
            (skipn n0 (map_InP l (fun x0 _ -> strip _UU03a3_ x0)))
        | None ->
          mkApps (Coq_tConstruct (ind, n, block_args))
            (map_InP l (fun x0 _ -> strip _UU03a3_ x0)))
     | Coq_view_other t0 ->
       mkApps (strip _UU03a3_ t0) (map_InP l (fun x0 _ -> strip _UU03a3_ x0)))
  | TermSpineView.Coq_tConst kn -> Coq_tConst kn
  | TermSpineView.Coq_tConstruct (i, n, args) -> Coq_tConstruct (i, n, args)
  | TermSpineView.Coq_tCase (ci, p, brs) ->
    let brs' = map_InP brs (fun x0 _ -> ((fst x0), (strip _UU03a3_ (snd x0))))
    in
    Coq_tCase (((fst ci), O), (strip _UU03a3_ p), brs')
  | TermSpineView.Coq_tProj (p, c) ->
    Coq_tProj ({ proj_ind = p.proj_ind; proj_npars = O; proj_arg =
      p.proj_arg }, (strip _UU03a3_ c))
  | TermSpineView.Coq_tFix (mfix, idx) ->
    let mfix' =
      map_InP mfix (fun d _ -> { E.dname = d.dname; E.dbody =
        (strip _UU03a3_ d.dbody); E.rarg = d.rarg })
    in
    Coq_tFix (mfix', idx)
  | TermSpineView.Coq_tCoFix (mfix, idx) ->
    let mfix' =
      map_InP mfix (fun d _ -> { E.dname = d.dname; E.dbody =
        (strip _UU03a3_ d.dbody); E.rarg = d.rarg })
    in
    Coq_tCoFix (mfix', idx)
  | TermSpineView.Coq_tPrim p ->
    Coq_tPrim (map_primIn p (fun x0 _ -> strip _UU03a3_ x0))
  | TermSpineView.Coq_tLazy p -> Coq_tLazy (strip _UU03a3_ p)
  | TermSpineView.Coq_tForce p -> Coq_tForce (strip _UU03a3_ p)

(** val strip_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let strip_constant_decl _UU03a3_ cb =
  option_map (strip _UU03a3_) cb

(** val strip_inductive_decl :
    mutual_inductive_body -> E.mutual_inductive_body **)

let strip_inductive_decl idecl =
  { E.ind_finite = idecl.ind_finite; E.ind_npars = O; E.ind_bodies =
    idecl.ind_bodies }

(** val strip_decl : GlobalContextMap.t -> global_decl -> global_decl **)

let strip_decl _UU03a3_ = function
| ConstantDecl cb -> ConstantDecl (strip_constant_decl _UU03a3_ cb)
| InductiveDecl idecl -> InductiveDecl (strip_inductive_decl idecl)

(** val strip_env : GlobalContextMap.t -> (kername * global_decl) list **)

let strip_env _UU03a3_ =
  map (on_snd (strip_decl _UU03a3_)) _UU03a3_.GlobalContextMap.global_decls

(** val strip_program : eprogram_env -> eprogram **)

let strip_program p =
  ((strip_env (fst p)), (strip (fst p) (snd p)))

(** val switch_no_params : coq_EEnvFlags -> coq_EEnvFlags **)

let switch_no_params efl =
  { has_axioms = efl.has_axioms; has_cstr_params = false; term_switches =
    efl.term_switches; cstr_as_blocks = efl.cstr_as_blocks }
