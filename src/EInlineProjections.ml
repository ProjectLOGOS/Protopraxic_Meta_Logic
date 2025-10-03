open BasicAst
open Datatypes
open EAst
open EEnvMap
open EPrimitive
open EProgram
open EWellformed
open Extract
open Kernames
open List0
open MCList
open MCProd
open Nat0

(** val disable_projections_term_flags : coq_ETermFlags -> coq_ETermFlags **)

let disable_projections_term_flags et =
  { has_tBox = et.has_tBox; has_tRel = et.has_tRel; has_tVar = et.has_tVar;
    has_tEvar = et.has_tEvar; has_tLambda = et.has_tLambda; has_tLetIn =
    et.has_tLetIn; has_tApp = et.has_tApp; has_tConst = et.has_tConst;
    has_tConstruct = et.has_tConstruct; has_tCase = true; has_tProj = false;
    has_tFix = et.has_tFix; has_tCoFix = et.has_tCoFix; has_tPrim =
    et.has_tPrim; has_tLazy_Force = et.has_tLazy_Force }

(** val disable_projections_env_flag : coq_EEnvFlags -> coq_EEnvFlags **)

let disable_projections_env_flag efl =
  { has_axioms = efl.has_axioms; has_cstr_params = efl.has_cstr_params;
    term_switches = (disable_projections_term_flags efl.term_switches);
    cstr_as_blocks = efl.cstr_as_blocks }

(** val optimize : GlobalContextMap.t -> term -> term **)

let rec optimize _UU03a3_ t0 = match t0 with
| Coq_tRel i -> Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (optimize _UU03a3_) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (optimize _UU03a3_ m))
| Coq_tLetIn (na, b, b') ->
  Coq_tLetIn (na, (optimize _UU03a3_ b), (optimize _UU03a3_ b'))
| Coq_tApp (u, v) -> Coq_tApp ((optimize _UU03a3_ u), (optimize _UU03a3_ v))
| Coq_tConstruct (ind, n, args) ->
  Coq_tConstruct (ind, n, (map (optimize _UU03a3_) args))
| Coq_tCase (ind, c, brs) ->
  Coq_tCase (ind, (optimize _UU03a3_ c),
    (map (on_snd (optimize _UU03a3_)) brs))
| Coq_tProj (p, c) ->
  (match GlobalContextMap.lookup_projection _UU03a3_ p with
   | Some p0 ->
     let (p1, _) = p0 in
     let (_, cdecl) = p1 in
     Coq_tCase ((p.proj_ind, p.proj_npars), (optimize _UU03a3_ c),
     (((unfold cdecl.cstr_nargs (fun _ -> Coq_nAnon)), (Coq_tRel
     (sub cdecl.cstr_nargs (S p.proj_arg)))) :: []))
   | None -> Coq_tProj (p, (optimize _UU03a3_ c)))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (optimize _UU03a3_)) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (optimize _UU03a3_)) mfix in
  Coq_tCoFix (mfix', idx)
| Coq_tPrim p -> Coq_tPrim (map_prim (optimize _UU03a3_) p)
| Coq_tLazy t1 -> Coq_tLazy (optimize _UU03a3_ t1)
| Coq_tForce t1 -> Coq_tForce (optimize _UU03a3_ t1)
| _ -> t0

(** val optimize_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let optimize_constant_decl _UU03a3_ cb =
  option_map (optimize _UU03a3_) cb

(** val optimize_decl : GlobalContextMap.t -> global_decl -> global_decl **)

let optimize_decl _UU03a3_ = function
| ConstantDecl cb -> ConstantDecl (optimize_constant_decl _UU03a3_ cb)
| InductiveDecl idecl -> InductiveDecl idecl

(** val optimize_env : GlobalContextMap.t -> (kername * global_decl) list **)

let optimize_env _UU03a3_ =
  map (on_snd (optimize_decl _UU03a3_)) _UU03a3_.GlobalContextMap.global_decls

(** val optimize_program :
    eprogram_env -> (kername * global_decl) list * term **)

let optimize_program p =
  ((optimize_env (fst p)), (optimize (fst p) (snd p)))
