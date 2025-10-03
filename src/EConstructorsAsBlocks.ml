open Datatypes
open EAst
open EEnvMap
open EEtaExpanded
open EPrimitive
open EProgram
open ESpineView
open EWcbvEval
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd

(** val transform_blocks : GlobalContextMap.t -> term -> term **)

let rec transform_blocks _UU03a3_ x =
  match TermSpineView.view x with
  | TermSpineView.Coq_tBox -> Coq_tBox
  | TermSpineView.Coq_tRel n -> Coq_tRel n
  | TermSpineView.Coq_tVar n -> Coq_tVar n
  | TermSpineView.Coq_tEvar (n, e) ->
    Coq_tEvar (n, (map_InP e (fun x0 _ -> transform_blocks _UU03a3_ x0)))
  | TermSpineView.Coq_tLambda (n, b) ->
    Coq_tLambda (n, (transform_blocks _UU03a3_ b))
  | TermSpineView.Coq_tLetIn (n, b, b') ->
    Coq_tLetIn (n, (transform_blocks _UU03a3_ b),
      (transform_blocks _UU03a3_ b'))
  | TermSpineView.Coq_tApp (f, l) ->
    (match construct_viewc f with
     | Coq_view_construct (ind, n, _) ->
       (match GlobalContextMap.lookup_constructor_pars_args _UU03a3_ ind n with
        | Some p ->
          let (_, n0) = p in
          let args = map_InP l (fun x0 _ -> transform_blocks _UU03a3_ x0) in
          let (args0, rest) = chop n0 args in
          mkApps (Coq_tConstruct (ind, n, args0)) rest
        | None ->
          let args = map_InP l (fun x0 _ -> transform_blocks _UU03a3_ x0) in
          Coq_tConstruct (ind, n, args))
     | Coq_view_other t0 ->
       mkApps (transform_blocks _UU03a3_ t0)
         (map_InP l (fun x0 _ -> transform_blocks _UU03a3_ x0)))
  | TermSpineView.Coq_tConst kn -> Coq_tConst kn
  | TermSpineView.Coq_tConstruct (i, n, _) -> Coq_tConstruct (i, n, [])
  | TermSpineView.Coq_tCase (ci, p, brs) ->
    let brs' =
      map_InP brs (fun x0 _ -> ((fst x0),
        (transform_blocks _UU03a3_ (snd x0))))
    in
    Coq_tCase (((fst ci), O), (transform_blocks _UU03a3_ p), brs')
  | TermSpineView.Coq_tProj (p, c) ->
    Coq_tProj ({ proj_ind = p.proj_ind; proj_npars = O; proj_arg =
      p.proj_arg }, (transform_blocks _UU03a3_ c))
  | TermSpineView.Coq_tFix (mfix, idx) ->
    let mfix' =
      map_InP mfix (fun d _ -> { E.dname = d.dname; E.dbody =
        (transform_blocks _UU03a3_ d.dbody); E.rarg = d.rarg })
    in
    Coq_tFix (mfix', idx)
  | TermSpineView.Coq_tCoFix (mfix, idx) ->
    let mfix' =
      map_InP mfix (fun d _ -> { E.dname = d.dname; E.dbody =
        (transform_blocks _UU03a3_ d.dbody); E.rarg = d.rarg })
    in
    Coq_tCoFix (mfix', idx)
  | TermSpineView.Coq_tPrim p ->
    Coq_tPrim (map_primIn p (fun x0 _ -> transform_blocks _UU03a3_ x0))
  | TermSpineView.Coq_tLazy p -> Coq_tLazy (transform_blocks _UU03a3_ p)
  | TermSpineView.Coq_tForce p -> Coq_tForce (transform_blocks _UU03a3_ p)

(** val transform_blocks_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let transform_blocks_constant_decl _UU03a3_ cb =
  option_map (transform_blocks _UU03a3_) cb

(** val transform_blocks_decl :
    GlobalContextMap.t -> global_decl -> global_decl **)

let transform_blocks_decl _UU03a3_ = function
| ConstantDecl cb -> ConstantDecl (transform_blocks_constant_decl _UU03a3_ cb)
| InductiveDecl idecl -> InductiveDecl idecl

(** val transform_blocks_env :
    GlobalContextMap.t -> (kername * global_decl) list **)

let transform_blocks_env _UU03a3_ =
  map (on_snd (transform_blocks_decl _UU03a3_))
    _UU03a3_.GlobalContextMap.global_decls

(** val transform_blocks_program :
    eprogram_env -> (kername * global_decl) list * term **)

let transform_blocks_program p =
  ((transform_blocks_env (fst p)), (transform_blocks (fst p) (snd p)))

(** val switch_cstr_as_blocks : coq_EEnvFlags -> coq_EEnvFlags **)

let switch_cstr_as_blocks fl =
  { has_axioms = fl.has_axioms; has_cstr_params = fl.has_cstr_params;
    term_switches = fl.term_switches; cstr_as_blocks = true }

(** val block_wcbv_flags : coq_WcbvFlags **)

let block_wcbv_flags =
  { with_prop_case = false; with_guarded_fix = false;
    with_constructor_as_block = true }
