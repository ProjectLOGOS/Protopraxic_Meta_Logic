open BasicAst
open Datatypes
open EAst
open EEnvMap
open EPrimitive
open EProgram
open Extract
open Kernames
open List0
open MCProd
open ReflectEq

(** val inspect : 'a1 -> 'a1 **)

let inspect x =
  x

(** val unboxable : one_inductive_body -> constructor_body -> bool **)

let unboxable idecl cdecl =
  (&&) (reflect_nat (length idecl.ind_ctors) (S O))
    (reflect_nat cdecl.cstr_nargs (S O))

(** val is_unboxable : GlobalContextMap.t -> inductive -> nat -> bool **)

let is_unboxable _UU03a3_ kn = function
| O ->
  (match GlobalContextMap.lookup_constructor _UU03a3_ kn O with
   | Some p -> let (p0, c0) = p in let (_, o) = p0 in unboxable o c0
   | None -> false)
| S _ -> false

(** val get_unboxable_case_branch :
    inductive -> (name list * term) list -> (name * term) option **)

let get_unboxable_case_branch _ = function
| [] -> None
| p :: l ->
  let (l0, t0) = p in
  (match l0 with
   | [] -> None
   | n :: l1 ->
     (match l1 with
      | [] -> (match l with
               | [] -> Some (n, t0)
               | _ :: _ -> None)
      | _ :: _ -> None))

(** val unbox : GlobalContextMap.t -> term -> term **)

let rec unbox _UU03a3_ = function
| Coq_tEvar (n, l) -> Coq_tEvar (n, (map (unbox _UU03a3_) l))
| Coq_tLambda (na, t1) -> Coq_tLambda (na, (unbox _UU03a3_ t1))
| Coq_tLetIn (na, b, t1) ->
  Coq_tLetIn (na, (unbox _UU03a3_ b), (unbox _UU03a3_ t1))
| Coq_tApp (u, v) -> Coq_tApp ((unbox _UU03a3_ u), (unbox _UU03a3_ v))
| Coq_tConstruct (ind, n, args) ->
  if inspect (is_unboxable _UU03a3_ ind n)
  then (match args with
        | [] -> Coq_tConstruct (ind, n, (map (unbox _UU03a3_) []))
        | t1 :: l ->
          (match l with
           | [] -> unbox _UU03a3_ t1
           | t2 :: l0 ->
             Coq_tConstruct (ind, n,
               (map (unbox _UU03a3_) (t1 :: (t2 :: l0))))))
  else Coq_tConstruct (ind, n, (map (unbox _UU03a3_) args))
| Coq_tCase (indn, c, brs) ->
  if inspect (is_unboxable _UU03a3_ (fst indn) O)
  then (match inspect
                (get_unboxable_case_branch (fst indn)
                  (map (on_snd (unbox _UU03a3_)) brs)) with
        | Some p -> let (n, t1) = p in Coq_tLetIn (n, (unbox _UU03a3_ c), t1)
        | None ->
          Coq_tCase (indn, (unbox _UU03a3_ c),
            (map (on_snd (unbox _UU03a3_)) brs)))
  else Coq_tCase (indn, (unbox _UU03a3_ c),
         (map (on_snd (unbox _UU03a3_)) brs))
| Coq_tProj (p, c) ->
  if inspect (is_unboxable _UU03a3_ p.proj_ind O)
  then unbox _UU03a3_ c
  else Coq_tProj (p, (unbox _UU03a3_ c))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (unbox _UU03a3_)) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (unbox _UU03a3_)) mfix in Coq_tCoFix (mfix', idx)
| Coq_tPrim prim -> Coq_tPrim (map_prim (unbox _UU03a3_) prim)
| Coq_tLazy t1 -> Coq_tLazy (unbox _UU03a3_ t1)
| Coq_tForce t1 -> Coq_tForce (unbox _UU03a3_ t1)
| x -> x

(** val unbox_constant_decl :
    GlobalContextMap.t -> constant_body -> E.constant_body **)

let unbox_constant_decl _UU03a3_ cb =
  option_map (unbox _UU03a3_) cb

(** val unbox_inductive_decl :
    mutual_inductive_body -> E.mutual_inductive_body **)

let unbox_inductive_decl idecl =
  { E.ind_finite = idecl.ind_finite; E.ind_npars = O; E.ind_bodies =
    idecl.ind_bodies }

(** val unbox_decl : GlobalContextMap.t -> global_decl -> global_decl **)

let unbox_decl _UU03a3_ = function
| ConstantDecl cb -> ConstantDecl (unbox_constant_decl _UU03a3_ cb)
| InductiveDecl idecl -> InductiveDecl (unbox_inductive_decl idecl)

(** val unbox_env : GlobalContextMap.t -> (kername * global_decl) list **)

let unbox_env _UU03a3_ =
  map (on_snd (unbox_decl _UU03a3_)) _UU03a3_.GlobalContextMap.global_decls

(** val unbox_program : eprogram_env -> eprogram **)

let unbox_program p =
  ((unbox_env (fst p)), (unbox (fst p) (snd p)))
