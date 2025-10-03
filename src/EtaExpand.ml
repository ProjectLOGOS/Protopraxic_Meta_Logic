open Ast0
open AstUtils
open BasicAst
open Byte
open Datatypes
open Kernames
open List0
open MCList
open MCProd
open Nat0
open TemplateEnvMap
open TemplateProgram
open Typing0
open Universes0
open Bytestring

(** val eta_single : term -> term list -> term -> nat -> term **)

let eta_single t0 args ty count =
  let needed = sub count (length args) in
  let prev_args = map (lift needed O) args in
  let eta_args = rev_map (fun x -> Coq_tRel x) (seq O needed) in
  let remaining =
    firstn needed
      (skipn (length args)
        (rev (Env.smash_context [] (fst (decompose_prod_assum [] ty)))))
  in
  let remaining_subst = Env.subst_context (rev args) O remaining in
  fold_right (fun d b -> Coq_tLambda (d.decl_name, d.decl_type, b))
    (mkApps (lift needed O t0) (app prev_args eta_args)) remaining_subst

(** val eta_constructor :
    GlobalEnvMap.t -> inductive -> nat -> Level.t list -> term list -> term
    option **)

let eta_constructor _UU03a3_ ind c u args =
  match GlobalEnvMap.lookup_constructor _UU03a3_ ind c with
  | Some p ->
    let (p0, cdecl) = p in
    let (mdecl, _) = p0 in
    let ty = type_of_constructor mdecl cdecl (ind, c) u in
    let n =
      add (Env.ind_npars mdecl)
        (Env.context_assumptions (Env.cstr_args cdecl))
    in
    Some (eta_single (Coq_tConstruct (ind, c, u)) args ty n)
  | None -> None

(** val eta_fixpoint :
    term mfixpoint -> nat -> term def -> term list -> term **)

let eta_fixpoint def0 i d args =
  eta_single (Coq_tFix (def0, i)) args d.dtype (add (S O) d.rarg)

(** val up : (nat * term) option list -> (nat * term) option list **)

let up _UU0393_ =
  None :: _UU0393_

(** val eta_expand :
    GlobalEnvMap.t -> (nat * term) option list -> term -> term **)

let rec eta_expand _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tRel n ->
  (match nth_error _UU0393_ n with
   | Some o ->
     (match o with
      | Some p ->
        let (c, ty) = p in eta_single (Coq_tRel n) [] (lift (S n) O ty) c
      | None -> Coq_tRel n)
   | None -> Coq_tRel n)
| Coq_tEvar (n, ts) -> Coq_tEvar (n, (map (eta_expand _UU03a3_ _UU0393_) ts))
| Coq_tCast (t1, k, t2) ->
  Coq_tCast ((eta_expand _UU03a3_ _UU0393_ t1), k,
    (eta_expand _UU03a3_ _UU0393_ t2))
| Coq_tLambda (na, ty, body) ->
  Coq_tLambda (na, ty, (eta_expand _UU03a3_ (up _UU0393_) body))
| Coq_tLetIn (na, val0, ty, body) ->
  Coq_tLetIn (na, (eta_expand _UU03a3_ _UU0393_ val0), ty,
    (eta_expand _UU03a3_ (up _UU0393_) body))
| Coq_tApp (hd, args) ->
  (match hd with
   | Coq_tRel n ->
     (match nth_error _UU0393_ n with
      | Some o ->
        (match o with
         | Some p ->
           let (c, ty) = p in
           eta_single (Coq_tRel n) (map (eta_expand _UU03a3_ _UU0393_) args)
             (lift (S n) O ty) c
         | None ->
           mkApps (Coq_tRel n) (map (eta_expand _UU03a3_ _UU0393_) args))
      | None -> Coq_tRel n)
   | Coq_tConstruct (ind, c, u) ->
     (match eta_constructor _UU03a3_ ind c u
              (map (eta_expand _UU03a3_ _UU0393_) args) with
      | Some res -> res
      | None ->
        Coq_tVar
          (String.append (String.String (Coq_x45, (String.String (Coq_x72,
            (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
            (Coq_x72, (String.String (Coq_x3a, (String.String (Coq_x20,
            (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
            (Coq_x6f, (String.String (Coq_x6b, (String.String (Coq_x75,
            (String.String (Coq_x70, (String.String (Coq_x20, (String.String
            (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x20,
            (String.String (Coq_x61, (String.String (Coq_x6e, (String.String
            (Coq_x20, (String.String (Coq_x69, (String.String (Coq_x6e,
            (String.String (Coq_x64, (String.String (Coq_x75, (String.String
            (Coq_x63, (String.String (Coq_x74, (String.String (Coq_x69,
            (String.String (Coq_x76, (String.String (Coq_x65, (String.String
            (Coq_x20, (String.String (Coq_x66, (String.String (Coq_x61,
            (String.String (Coq_x69, (String.String (Coq_x6c, (String.String
            (Coq_x65, (String.String (Coq_x64, (String.String (Coq_x20,
            (String.String (Coq_x66, (String.String (Coq_x6f, (String.String
            (Coq_x72, (String.String (Coq_x20,
            String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (string_of_kername ind.inductive_mind)))
   | Coq_tFix (def0, i) ->
     let def' =
       map (fun d ->
         let ctx =
           List0.rev
             (mapi (fun i0 d0 -> Some ((add (S O) d0.rarg),
               (lift i0 O d0.dtype))) def0)
         in
         { dname = d.dname; dtype = d.dtype; dbody =
         (eta_expand _UU03a3_ (app ctx _UU0393_) d.dbody); rarg = d.rarg })
         def0
     in
     (match nth_error def' i with
      | Some d ->
        eta_fixpoint def' i d (map (eta_expand _UU03a3_ _UU0393_) args)
      | None ->
        Coq_tVar (String.String (Coq_x45, (String.String (Coq_x72,
          (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
          (Coq_x72, (String.String (Coq_x3a, (String.String (Coq_x20,
          (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
          (Coq_x6f, (String.String (Coq_x6b, (String.String (Coq_x75,
          (String.String (Coq_x70, (String.String (Coq_x20, (String.String
          (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x20,
          (String.String (Coq_x61, (String.String (Coq_x20, (String.String
          (Coq_x66, (String.String (Coq_x69, (String.String (Coq_x78,
          (String.String (Coq_x70, (String.String (Coq_x6f, (String.String
          (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
          (String.String (Coq_x20, (String.String (Coq_x66, (String.String
          (Coq_x61, (String.String (Coq_x69, (String.String (Coq_x6c,
          (String.String (Coq_x65, (String.String (Coq_x64,
          String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | _ ->
     mkApps (eta_expand _UU03a3_ _UU0393_ hd)
       (map (eta_expand _UU03a3_ _UU0393_) args))
| Coq_tConstruct (ind, c, u) ->
  (match eta_constructor _UU03a3_ ind c u [] with
   | Some res -> res
   | None ->
     Coq_tVar
       (String.append (String.String (Coq_x45, (String.String (Coq_x72,
         (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
         (Coq_x72, (String.String (Coq_x3a, (String.String (Coq_x20,
         (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
         (Coq_x6f, (String.String (Coq_x6b, (String.String (Coq_x75,
         (String.String (Coq_x70, (String.String (Coq_x20, (String.String
         (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x20,
         (String.String (Coq_x61, (String.String (Coq_x6e, (String.String
         (Coq_x20, (String.String (Coq_x69, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x75, (String.String
         (Coq_x63, (String.String (Coq_x74, (String.String (Coq_x69,
         (String.String (Coq_x76, (String.String (Coq_x65, (String.String
         (Coq_x20, (String.String (Coq_x66, (String.String (Coq_x61,
         (String.String (Coq_x69, (String.String (Coq_x6c, (String.String
         (Coq_x65, (String.String (Coq_x64, (String.String (Coq_x20,
         (String.String (Coq_x66, (String.String (Coq_x6f, (String.String
         (Coq_x72, (String.String (Coq_x20,
         String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (string_of_kername ind.inductive_mind)))
| Coq_tCase (ci, p, disc, brs) ->
  let p' =
    map_predicate (Obj.magic id) (eta_expand _UU03a3_ _UU0393_)
      (Obj.magic id) p
  in
  let brs' =
    map (fun b -> { bcontext = b.bcontext; bbody =
      (eta_expand _UU03a3_ (app (repeat None (length b.bcontext)) _UU0393_)
        b.bbody) }) brs
  in
  Coq_tCase (ci, p', (eta_expand _UU03a3_ _UU0393_ disc), brs')
| Coq_tProj (p, t1) -> Coq_tProj (p, (eta_expand _UU03a3_ _UU0393_ t1))
| Coq_tFix (def0, i) ->
  let def' =
    map (fun d ->
      let ctx =
        List0.rev
          (mapi (fun i0 d0 -> Some ((add (S O) d0.rarg),
            (lift i0 O d0.dtype))) def0)
      in
      { dname = d.dname; dtype = d.dtype; dbody =
      (eta_expand _UU03a3_ (app ctx _UU0393_) d.dbody); rarg = d.rarg }) def0
  in
  (match nth_error def' i with
   | Some d -> eta_fixpoint def' i d []
   | None ->
     Coq_tVar (String.String (Coq_x45, (String.String (Coq_x72,
       (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
       (Coq_x72, (String.String (Coq_x3a, (String.String (Coq_x20,
       (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
       (Coq_x6f, (String.String (Coq_x6b, (String.String (Coq_x75,
       (String.String (Coq_x70, (String.String (Coq_x20, (String.String
       (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x20,
       (String.String (Coq_x61, (String.String (Coq_x20, (String.String
       (Coq_x66, (String.String (Coq_x69, (String.String (Coq_x78,
       (String.String (Coq_x70, (String.String (Coq_x6f, (String.String
       (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
       (String.String (Coq_x20, (String.String (Coq_x66, (String.String
       (Coq_x61, (String.String (Coq_x69, (String.String (Coq_x6c,
       (String.String (Coq_x65, (String.String (Coq_x64, (String.String
       (Coq_x20,
       String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Coq_tCoFix (def0, i) ->
  Coq_tCoFix
    ((map
       (map_def (Obj.magic id)
         (eta_expand _UU03a3_ (app (repeat None (length def0)) _UU0393_)))
       def0), i)
| Coq_tArray (u, arr, def0, ty) ->
  Coq_tArray (u, (map (eta_expand _UU03a3_ _UU0393_) arr),
    (eta_expand _UU03a3_ _UU0393_ def0), (eta_expand _UU03a3_ _UU0393_ ty))
| _ -> t0

(** val eta_global_decl :
    GlobalEnvMap.t -> Env.constant_body -> Env.constant_body **)

let eta_global_decl _UU03a3_ cb =
  { Env.cst_type = (eta_expand _UU03a3_ [] (Env.cst_type cb)); Env.cst_body =
    (match Env.cst_body cb with
     | Some b -> Some (eta_expand _UU03a3_ [] b)
     | None -> None); Env.cst_universes = (Env.cst_universes cb);
    Env.cst_relevance = (Env.cst_relevance cb) }

(** val map_decl_body :
    ('a1 -> 'a1) -> 'a1 context_decl -> 'a1 context_decl **)

let map_decl_body f decl =
  { decl_name = decl.decl_name; decl_body = (option_map f decl.decl_body);
    decl_type = decl.decl_type }

(** val fold_context_k_defs :
    (nat -> 'a1 -> 'a1) -> 'a1 context_decl list -> 'a1 context_decl list **)

let rec fold_context_k_defs f = function
| [] -> []
| d :: _UU0393_0 ->
  (map_decl_body (f (length _UU0393_0)) d) :: (fold_context_k_defs f
                                                _UU0393_0)

(** val eta_context :
    GlobalEnvMap.t -> nat -> term context_decl list -> term context_decl list **)

let eta_context _UU03a3_ _UU0393_ ctx =
  fold_context_k_defs (fun n ->
    eta_expand _UU03a3_ (repeat None (add n _UU0393_))) ctx

(** val eta_constructor_decl :
    GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.constructor_body ->
    Env.constructor_body **)

let eta_constructor_decl _UU03a3_ mdecl cdecl =
  { Env.cstr_name = (Env.cstr_name cdecl); Env.cstr_args =
    (eta_context _UU03a3_
      (add (length (Env.ind_params mdecl)) (length (Env.ind_bodies mdecl)))
      (Env.cstr_args cdecl)); Env.cstr_indices =
    (map (eta_expand _UU03a3_ []) (Env.cstr_indices cdecl)); Env.cstr_type =
    (eta_expand _UU03a3_ (repeat None (length (Env.ind_bodies mdecl)))
      (Env.cstr_type cdecl)); Env.cstr_arity = (Env.cstr_arity cdecl) }

(** val eta_inductive_decl :
    GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.one_inductive_body **)

let eta_inductive_decl _UU03a3_ mdecl idecl =
  { Env.ind_name = (Env.ind_name idecl); Env.ind_indices =
    (Env.ind_indices idecl); Env.ind_sort = (Env.ind_sort idecl);
    Env.ind_type = (Env.ind_type idecl); Env.ind_kelim =
    (Env.ind_kelim idecl); Env.ind_ctors =
    (map (eta_constructor_decl _UU03a3_ mdecl) (Env.ind_ctors idecl));
    Env.ind_projs = (Env.ind_projs idecl); Env.ind_relevance =
    (Env.ind_relevance idecl) }

(** val eta_minductive_decl :
    GlobalEnvMap.t -> Env.mutual_inductive_body -> Env.mutual_inductive_body **)

let eta_minductive_decl _UU03a3_ mdecl =
  { Env.ind_finite = (Env.ind_finite mdecl); Env.ind_npars =
    (Env.ind_npars mdecl); Env.ind_params =
    (eta_context _UU03a3_ O (Env.ind_params mdecl)); Env.ind_bodies =
    (map (eta_inductive_decl _UU03a3_ mdecl) (Env.ind_bodies mdecl));
    Env.ind_universes = (Env.ind_universes mdecl); Env.ind_variance =
    (Env.ind_variance mdecl) }

(** val eta_global_declaration :
    GlobalEnvMap.t -> Env.global_decl -> Env.global_decl **)

let eta_global_declaration _UU03a3_ = function
| Env.ConstantDecl cb -> Env.ConstantDecl (eta_global_decl _UU03a3_ cb)
| Env.InductiveDecl idecl ->
  Env.InductiveDecl (eta_minductive_decl _UU03a3_ idecl)

(** val eta_global_declarations :
    GlobalEnvMap.t -> Env.global_declarations -> (kername * Env.global_decl)
    list **)

let eta_global_declarations _UU03a3_ decls =
  map (on_snd (eta_global_declaration _UU03a3_)) decls

(** val eta_expand_global_env : GlobalEnvMap.t -> Env.global_env **)

let eta_expand_global_env _UU03a3_ =
  { Env.universes = (Env.universes _UU03a3_.GlobalEnvMap.env);
    Env.declarations =
    (eta_global_declarations _UU03a3_
      (Env.declarations _UU03a3_.GlobalEnvMap.env)); Env.retroknowledge =
    (Env.retroknowledge _UU03a3_.GlobalEnvMap.env) }

(** val eta_expand_program : template_program_env -> Env.program **)

let eta_expand_program p =
  let _UU03a3_' = eta_expand_global_env (fst p) in
  (_UU03a3_', (eta_expand (fst p) [] (snd p)))
