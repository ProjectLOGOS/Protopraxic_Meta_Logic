open All_Forall
open BasicAst
open BinNums
open Bool
open CRelationClasses
open Classes0
open Datatypes
open Kernames
open List0
open MCList
open MCOption
open MCProd
open Nat0
open Primitive
open ReflectEq
open Signature
open Specif
open Universes0
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Lookup =
 functor (T:Environment.Term) ->
 functor (E:sig
  type judgment = (Sort.t, T.term) judgment_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Sort.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Sort.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
    one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

  type global_declarations = (kername * global_decl) list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Environment.Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Environment.Retroknowledge.t

  val empty_global_env : global_env

  val add_global_decl : global_env -> (kername * global_decl) -> global_env

  val set_declarations : global_env -> global_declarations -> global_env

  val lookup_global : global_declarations -> kername -> global_decl option

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_globals : global_declarations -> kername -> global_decl list

  val lookup_envs : global_env -> kername -> global_decl list

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  val strictly_extends_decls_extends_part_globals :
    (kername * global_decl) list -> (kername * global_decl) list ->
    ((kername * global_decl) list, __) sigT -> kername -> (global_decl list,
    __) sigT

  val strictly_extends_decls_extends_part :
    global_env -> global_env -> ((kername * global_decl) list, __) sigT ->
    kername -> (global_decl list, __) sigT

  val strictly_extends_decls_extends_decls :
    global_env -> global_env -> strictly_extends_decls -> extends_decls

  val strictly_extends_decls_extends_strictly_on_decls :
    global_env -> global_env -> strictly_extends_decls ->
    extends_strictly_on_decls

  val extends_decls_extends :
    global_env -> global_env -> extends_decls -> extends

  val extends_strictly_on_decls_extends :
    global_env -> global_env -> extends_strictly_on_decls -> extends

  val strictly_extends_decls_extends_decls_subrel :
    (global_env, strictly_extends_decls, extends_decls) subrelation

  val strictly_extends_decls_extends_strictly_on_decls_subrel :
    (global_env, strictly_extends_decls, extends_strictly_on_decls)
    subrelation

  val extends_decls_extends_subrel :
    (global_env, extends_decls, extends) subrelation

  val extends_strictly_on_decls_extends_subrel :
    (global_env, extends_strictly_on_decls, extends) subrelation

  val strictly_extends_decls_extends_subrel :
    (global_env, strictly_extends_decls, extends) subrelation

  val strictly_extends_decls_refl :
    (global_env, strictly_extends_decls) coq_Reflexive

  val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

  val extends_strictly_on_decls_refl :
    (global_env, extends_strictly_on_decls) coq_Reflexive

  val extends_refl : (global_env, extends) coq_Reflexive

  val extends_decls_part_globals_refl :
    global_declarations -> kername -> (global_decl list, __) sigT

  val extends_decls_part_refl :
    global_env -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_refl :
    global_declarations -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_refl :
    global_env -> ((kername * global_decl) list, __) sigT

  val extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
    list, __) sigT) -> kername -> (global_decl list, __) sigT

  val extends_decls_part_trans :
    global_env -> global_env -> global_env -> (kername -> (global_decl list,
    __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername ->
    (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    ((kername * global_decl) list, __) sigT -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_trans :
    global_env -> global_env -> global_env -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT ->
    ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_trans :
    (global_env, strictly_extends_decls) coq_Transitive

  val extends_decls_trans : (global_env, extends_decls) coq_Transitive

  val extends_strictly_on_decls_trans :
    (global_env, extends_strictly_on_decls) coq_Transitive

  val extends_trans : (global_env, extends) coq_Transitive

  val declared_kername_set : global_declarations -> KernameSet.t

  val merge_globals :
    global_declarations -> global_declarations -> global_declarations

  val merge_global_envs : global_env -> global_env -> global_env

  val strictly_extends_decls_l_merge_globals :
    global_declarations -> global_declarations -> ((kername * global_decl)
    list, __) sigT

  val extends_l_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_strictly_on_decls_l_merge :
    global_env -> global_env -> extends_strictly_on_decls

  val extends_l_merge : global_env -> global_env -> extends

  val extends_r_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_r_merge : global_env -> global_env -> extends

  val primitive_constant : global_env -> prim_tag -> kername option

  val tImpl : T.term -> T.term -> T.term

  val array_uctx : name list * ConstraintSet.t

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * T.term

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 struct
  (** val lookup_constant_gen :
      (kername -> E.global_decl option) -> kername -> E.constant_body option **)

  let lookup_constant_gen lookup kn =
    match lookup kn with
    | Some g ->
      (match g with
       | E.ConstantDecl d -> Some d
       | E.InductiveDecl _ -> None)
    | None -> None

  (** val lookup_constant :
      E.global_env -> kername -> E.constant_body option **)

  let lookup_constant _UU03a3_ =
    lookup_constant_gen (E.lookup_env _UU03a3_)

  (** val lookup_minductive_gen :
      (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
      option **)

  let lookup_minductive_gen lookup mind =
    match lookup mind with
    | Some g ->
      (match g with
       | E.ConstantDecl _ -> None
       | E.InductiveDecl decl -> Some decl)
    | None -> None

  (** val lookup_minductive :
      E.global_env -> kername -> E.mutual_inductive_body option **)

  let lookup_minductive _UU03a3_ =
    lookup_minductive_gen (E.lookup_env _UU03a3_)

  (** val lookup_inductive_gen :
      (kername -> E.global_decl option) -> inductive ->
      (E.mutual_inductive_body * E.one_inductive_body) option **)

  let lookup_inductive_gen lookup ind =
    match lookup_minductive_gen lookup ind.inductive_mind with
    | Some mdecl ->
      (match nth_error (E.ind_bodies mdecl) ind.inductive_ind with
       | Some idecl -> Some (mdecl, idecl)
       | None -> None)
    | None -> None

  (** val lookup_inductive :
      E.global_env -> inductive ->
      (E.mutual_inductive_body * E.one_inductive_body) option **)

  let lookup_inductive _UU03a3_ =
    lookup_inductive_gen (E.lookup_env _UU03a3_)

  (** val lookup_constructor_gen :
      (kername -> E.global_decl option) -> inductive -> nat ->
      ((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body)
      option **)

  let lookup_constructor_gen lookup ind k =
    match lookup_inductive_gen lookup ind with
    | Some p ->
      let (mdecl, idecl) = p in
      (match nth_error (E.ind_ctors idecl) k with
       | Some cdecl -> Some ((mdecl, idecl), cdecl)
       | None -> None)
    | None -> None

  (** val lookup_constructor :
      E.global_env -> inductive -> nat ->
      ((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body)
      option **)

  let lookup_constructor _UU03a3_ =
    lookup_constructor_gen (E.lookup_env _UU03a3_)

  (** val lookup_projection_gen :
      (kername -> E.global_decl option) -> projection ->
      (((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body) * E.projection_body)
      option **)

  let lookup_projection_gen lookup p =
    match lookup_constructor_gen lookup p.proj_ind O with
    | Some p0 ->
      let (p1, cdecl) = p0 in
      let (mdecl, idecl) = p1 in
      (match nth_error (E.ind_projs idecl) p.proj_arg with
       | Some pdecl -> Some (((mdecl, idecl), cdecl), pdecl)
       | None -> None)
    | None -> None

  (** val lookup_projection :
      E.global_env -> projection ->
      (((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body) * E.projection_body)
      option **)

  let lookup_projection _UU03a3_ =
    lookup_projection_gen (E.lookup_env _UU03a3_)

  (** val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1 **)

  let on_udecl_decl f = function
  | E.ConstantDecl cb -> f (E.cst_universes cb)
  | E.InductiveDecl mb -> f (E.ind_universes mb)

  (** val universes_decl_of_decl : E.global_decl -> universes_decl **)

  let universes_decl_of_decl =
    on_udecl_decl (fun x -> x)

  (** val global_levels : ContextSet.t -> LevelSet.t **)

  let global_levels univs =
    LevelSet.union (ContextSet.levels univs)
      (LevelSet.singleton Level.Coq_lzero)

  (** val global_constraints : E.global_env -> ConstraintSet.t **)

  let global_constraints _UU03a3_ =
    snd (E.universes _UU03a3_)

  (** val global_uctx : E.global_env -> ContextSet.t **)

  let global_uctx _UU03a3_ =
    ((global_levels (E.universes _UU03a3_)), (global_constraints _UU03a3_))

  (** val global_ext_levels : E.global_env_ext -> LevelSet.t **)

  let global_ext_levels _UU03a3_ =
    LevelSet.union (levels_of_udecl (snd _UU03a3_))
      (global_levels (E.universes (fst _UU03a3_)))

  (** val global_ext_constraints : E.global_env_ext -> ConstraintSet.t **)

  let global_ext_constraints _UU03a3_ =
    ConstraintSet.union (constraints_of_udecl (snd _UU03a3_))
      (global_constraints (fst _UU03a3_))

  (** val global_ext_uctx : E.global_env_ext -> ContextSet.t **)

  let global_ext_uctx _UU03a3_ =
    ((global_ext_levels _UU03a3_), (global_ext_constraints _UU03a3_))

  (** val wf_universe_dec : E.global_env_ext -> Universe.t -> bool **)

  let rec wf_universe_dec _UU03a3_ = function
  | [] -> true
  | y :: l ->
    if wf_universe_dec _UU03a3_ l
    then LevelSetProp.coq_In_dec (LevelExpr.get_level y)
           (global_ext_levels _UU03a3_)
    else false

  (** val wf_sort_dec : E.global_env_ext -> Sort.t -> bool **)

  let wf_sort_dec _UU03a3_ = function
  | Sort.Coq_sType t0 -> wf_universe_dec _UU03a3_ t0
  | _ -> true

  (** val declared_ind_declared_constructors :
      checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body
      -> E.one_inductive_body -> (E.constructor_body, __) coq_Alli **)

  let declared_ind_declared_constructors _ _ _ _ oib =
    forall_nth_error_Alli O (E.ind_ctors oib) (Obj.magic __)
 end

module EnvTyping =
 functor (T:Environment.Term) ->
 functor (E:sig
  type judgment = (Sort.t, T.term) judgment_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Sort.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Sort.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
    one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

  type global_declarations = (kername * global_decl) list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Environment.Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Environment.Retroknowledge.t

  val empty_global_env : global_env

  val add_global_decl : global_env -> (kername * global_decl) -> global_env

  val set_declarations : global_env -> global_declarations -> global_env

  val lookup_global : global_declarations -> kername -> global_decl option

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_globals : global_declarations -> kername -> global_decl list

  val lookup_envs : global_env -> kername -> global_decl list

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  val strictly_extends_decls_extends_part_globals :
    (kername * global_decl) list -> (kername * global_decl) list ->
    ((kername * global_decl) list, __) sigT -> kername -> (global_decl list,
    __) sigT

  val strictly_extends_decls_extends_part :
    global_env -> global_env -> ((kername * global_decl) list, __) sigT ->
    kername -> (global_decl list, __) sigT

  val strictly_extends_decls_extends_decls :
    global_env -> global_env -> strictly_extends_decls -> extends_decls

  val strictly_extends_decls_extends_strictly_on_decls :
    global_env -> global_env -> strictly_extends_decls ->
    extends_strictly_on_decls

  val extends_decls_extends :
    global_env -> global_env -> extends_decls -> extends

  val extends_strictly_on_decls_extends :
    global_env -> global_env -> extends_strictly_on_decls -> extends

  val strictly_extends_decls_extends_decls_subrel :
    (global_env, strictly_extends_decls, extends_decls) subrelation

  val strictly_extends_decls_extends_strictly_on_decls_subrel :
    (global_env, strictly_extends_decls, extends_strictly_on_decls)
    subrelation

  val extends_decls_extends_subrel :
    (global_env, extends_decls, extends) subrelation

  val extends_strictly_on_decls_extends_subrel :
    (global_env, extends_strictly_on_decls, extends) subrelation

  val strictly_extends_decls_extends_subrel :
    (global_env, strictly_extends_decls, extends) subrelation

  val strictly_extends_decls_refl :
    (global_env, strictly_extends_decls) coq_Reflexive

  val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

  val extends_strictly_on_decls_refl :
    (global_env, extends_strictly_on_decls) coq_Reflexive

  val extends_refl : (global_env, extends) coq_Reflexive

  val extends_decls_part_globals_refl :
    global_declarations -> kername -> (global_decl list, __) sigT

  val extends_decls_part_refl :
    global_env -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_refl :
    global_declarations -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_refl :
    global_env -> ((kername * global_decl) list, __) sigT

  val extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
    list, __) sigT) -> kername -> (global_decl list, __) sigT

  val extends_decls_part_trans :
    global_env -> global_env -> global_env -> (kername -> (global_decl list,
    __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername ->
    (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    ((kername * global_decl) list, __) sigT -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_trans :
    global_env -> global_env -> global_env -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT ->
    ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_trans :
    (global_env, strictly_extends_decls) coq_Transitive

  val extends_decls_trans : (global_env, extends_decls) coq_Transitive

  val extends_strictly_on_decls_trans :
    (global_env, extends_strictly_on_decls) coq_Transitive

  val extends_trans : (global_env, extends) coq_Transitive

  val declared_kername_set : global_declarations -> KernameSet.t

  val merge_globals :
    global_declarations -> global_declarations -> global_declarations

  val merge_global_envs : global_env -> global_env -> global_env

  val strictly_extends_decls_l_merge_globals :
    global_declarations -> global_declarations -> ((kername * global_decl)
    list, __) sigT

  val extends_l_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_strictly_on_decls_l_merge :
    global_env -> global_env -> extends_strictly_on_decls

  val extends_l_merge : global_env -> global_env -> extends

  val extends_r_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_r_merge : global_env -> global_env -> extends

  val primitive_constant : global_env -> prim_tag -> kername option

  val tImpl : T.term -> T.term -> T.term

  val array_uctx : name list * ConstraintSet.t

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * T.term

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context * Sort.t) option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 struct
  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type 'wf_term lift_wf_term = __ * 'wf_term

  type ('wf_term, 'wf_univ) lift_wfu_term = __ * ('wf_term * __)

  (** val lift_wfb_term : (T.term -> bool) -> E.judgment -> bool **)

  let lift_wfb_term wfb_term j =
    (&&) (option_default wfb_term j.j_term true) (wfb_term j.j_typ)

  (** val lift_wfbu_term :
      (T.term -> bool) -> (Sort.t -> bool) -> E.judgment -> bool **)

  let lift_wfbu_term wfb_term wfb_univ j =
    (&&) ((&&) (option_default wfb_term j.j_term true) (wfb_term j.j_typ))
      (option_default wfb_univ j.j_univ true)

  type ('checking, 'sorting) lift_sorting = __ * (Sort.t, 'sorting * __) sigT

  type 'typing lift_typing0 = ('typing, 'typing) lift_sorting

  type ('p, 'q) lift_typing_conj = ('p * 'q) lift_typing0

  (** val lift_wf_term_it_impl :
      T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
      Sort.t option -> 'a1 lift_wf_term -> __ -> ('a1 -> 'a2) -> 'a2
      lift_wf_term **)

  let lift_wf_term_it_impl tm tm' _ _ _ _ tu hPQc hPQs =
    let (o, p) = tu in
    ((match tm with
      | Some _ -> (match tm' with
                   | Some _ -> Obj.magic hPQc o
                   | None -> hPQc)
      | None ->
        (match tm' with
         | Some _ -> assert false (* absurd case *)
         | None -> hPQc)), (hPQs p))

  (** val lift_wf_term_f_impl :
      T.term option -> T.term -> Sort.t option -> Sort.t option -> (T.term ->
      T.term) -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2
      lift_wf_term **)

  let lift_wf_term_f_impl tm t0 _ _ _ x hPQ =
    let (o, p) = x in
    ((match tm with
      | Some t1 -> Obj.magic hPQ t1 o
      | None -> o), (hPQ t0 p))

  (** val lift_wf_term_impl :
      E.judgment -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2
      lift_wf_term **)

  let lift_wf_term_impl j x hPQ =
    let (o, p) = x in
    ((let o0 = j.j_term in
      match o0 with
      | Some t0 -> Obj.magic hPQ t0 o
      | None -> o), (hPQ j.j_typ p))

  (** val unlift_TermTyp :
      T.term -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting -> 'a1 **)

  let unlift_TermTyp _ _ _ =
    Obj.magic fst

  (** val unlift_TypUniv :
      T.term option -> T.term -> Sort.t -> ('a1, 'a2) lift_sorting -> 'a2 **)

  let unlift_TypUniv _ _ _ h =
    fst (projT2 (snd h))

  (** val lift_sorting_extract :
      T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
      ('a1, 'a2) lift_sorting **)

  let lift_sorting_extract _ _ _ w =
    ((fst w), (Coq_existT ((projT1 (snd w)), ((fst (projT2 (snd w))),
      (Obj.magic __)))))

  (** val lift_sorting_forget_univ :
      T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
      ('a1, 'a2) lift_sorting **)

  let lift_sorting_forget_univ _ _ _ = function
  | (o, s) ->
    let Coq_existT (x0, p) = s in
    let (p0, _) = p in (o, (Coq_existT (x0, (p0, (Obj.magic ())))))

  (** val lift_sorting_forget_body :
      T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
      ('a1, 'a2) lift_sorting **)

  let lift_sorting_forget_body _ _ _ = function
  | (_, s) -> ((Obj.magic ()), s)

  (** val lift_sorting_ex_it_impl_gen :
      T.term option -> T.term option -> T.term -> T.term -> ('a1, 'a3)
      lift_sorting -> __ -> ('a3 -> (Sort.t, 'a4) sigT) -> ('a2, 'a4)
      lift_sorting **)

  let lift_sorting_ex_it_impl_gen tm tm' _ _ tu hPQc hPQs =
    let (o, s) = tu in
    let Coq_existT (_, p) = s in
    let (p0, o0) = p in
    ((match tm with
      | Some _ -> (match tm' with
                   | Some _ -> Obj.magic hPQc o
                   | None -> hPQc)
      | None ->
        (match tm' with
         | Some _ -> assert false (* absurd case *)
         | None -> hPQc)),
    (let x = hPQs p0 in let Coq_existT (x0, q) = x in Coq_existT (x0, (q, o0))))

  (** val lift_sorting_it_impl_gen :
      T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
      ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting **)

  let lift_sorting_it_impl_gen tm tm' _ _ u = function
  | (o, s) ->
    let Coq_existT (x, p) = s in
    let (p0, o0) = p in
    let s0 = projT1 (snd (o, (Coq_existT (x, (p0, o0))))) in
    (fun hPQc hPQs ->
    ((match tm with
      | Some _ -> (match tm' with
                   | Some _ -> Obj.magic hPQc o
                   | None -> hPQc)
      | None ->
        (match tm' with
         | Some _ -> assert false (* absurd case *)
         | None -> hPQc)), (Coq_existT (s0, ((hPQs p0),
    (match u with
     | Some x0 -> Obj.magic __ x0 o p0 o0 hPQs
     | None -> o0))))))

  (** val lift_sorting_fu_it_impl :
      T.term option -> T.term -> Sort.t option -> (T.term -> T.term) ->
      (Sort.t -> Sort.t) -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) ->
      ('a2, 'a4) lift_sorting **)

  let lift_sorting_fu_it_impl tm _ u _ fu = function
  | (o, s) ->
    let Coq_existT (x, p) = s in
    let (p0, o0) = p in
    let s0 = projT1 (snd (o, (Coq_existT (x, (p0, o0))))) in
    (fun hPQc hPQs ->
    ((match tm with
      | Some _ -> Obj.magic hPQc o
      | None -> hPQc), (Coq_existT ((fu s0), ((hPQs p0),
    (match u with
     | Some x0 -> Obj.magic __ x0 o p0 o0 hPQs
     | None -> o0))))))

  (** val lift_sorting_f_it_impl :
      E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> __ ->
      ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting **)

  let lift_sorting_f_it_impl j f =
    lift_sorting_fu_it_impl j.j_term j.j_typ j.j_univ f (Obj.magic id)

  (** val lift_sorting_it_impl :
      E.judgment -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2,
      'a4) lift_sorting **)

  let lift_sorting_it_impl j =
    lift_sorting_f_it_impl j (Obj.magic id)

  (** val lift_sorting_fu_impl :
      T.term option -> T.term -> Sort.t option -> (T.term -> T.term) ->
      (Sort.t -> Sort.t) -> ('a1, 'a3) lift_sorting -> (T.term -> T.term ->
      'a1 -> 'a2) -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4)
      lift_sorting **)

  let lift_sorting_fu_impl tm t0 u f fu tu x x0 =
    lift_sorting_fu_it_impl tm t0 u f fu tu
      (match tm with
       | Some t1 -> Obj.magic (fun x1 -> x t1 t0 x1)
       | None -> Obj.magic ()) (fun x1 -> x0 t0 (projT1 (snd tu)) x1)

  (** val lift_typing_fu_impl :
      T.term option -> T.term -> Sort.t option -> (T.term -> T.term) ->
      (Sort.t -> Sort.t) -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 ->
      'a2) -> 'a2 lift_typing0 **)

  let lift_typing_fu_impl tm t0 u f fu hT hPQ =
    lift_sorting_fu_impl tm t0 u f fu hT hPQ (fun t1 u0 x ->
      hPQ t1 (T.tSort u0) x)

  (** val lift_sorting_f_impl :
      E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> (T.term
      -> T.term -> 'a1 -> 'a2) -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2,
      'a4) lift_sorting **)

  let lift_sorting_f_impl j f tu x x0 =
    lift_sorting_f_it_impl j f tu
      (let o = j.j_term in
       match o with
       | Some t0 -> Obj.magic (fun x1 -> x t0 j.j_typ x1)
       | None -> Obj.magic ()) (fun x1 -> x0 j.j_typ (projT1 (snd tu)) x1)

  (** val lift_typing_f_impl :
      E.judgment -> (T.term -> T.term) -> 'a1 lift_typing0 -> (T.term ->
      T.term -> 'a1 -> 'a2) -> 'a2 lift_typing0 **)

  let lift_typing_f_impl j f hT hPQ =
    lift_sorting_f_impl j f hT hPQ (fun t0 u x -> hPQ t0 (T.tSort u) x)

  (** val lift_typing_map :
      (T.term -> T.term) -> E.judgment -> 'a1 lift_typing0 -> 'a1 lift_typing0 **)

  let lift_typing_map f j hT =
    lift_typing_f_impl j f hT (fun _ _ x -> x)

  (** val lift_typing_mapu :
      (T.term -> T.term) -> (Sort.t -> Sort.t) -> T.term option -> T.term ->
      Sort.t option -> 'a1 lift_typing0 -> 'a1 lift_typing0 **)

  let lift_typing_mapu f fu tm ty u hT =
    lift_typing_fu_impl tm ty u f fu hT (fun _ _ x -> x)

  (** val lift_sorting_impl :
      E.judgment -> ('a1, 'a3) lift_sorting -> (T.term -> T.term -> 'a1 ->
      'a2) -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting **)

  let lift_sorting_impl j tu x x0 =
    lift_sorting_it_impl j tu
      (let o = j.j_term in
       match o with
       | Some t0 -> Obj.magic (fun x1 -> x t0 j.j_typ x1)
       | None -> Obj.magic ()) (fun x1 -> x0 j.j_typ (projT1 (snd tu)) x1)

  (** val lift_typing_impl :
      E.judgment -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 -> 'a2) ->
      'a2 lift_typing0 **)

  let lift_typing_impl j hT hPQ =
    lift_sorting_impl j hT hPQ (fun t0 u x -> hPQ t0 (T.tSort u) x)

  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing

  (** val coq_All_local_env_rect :
      'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
      'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
      coq_All_local_env -> 'a2 **)

  let rec coq_All_local_env_rect f f0 f1 _ = function
  | Coq_localenv_nil -> f
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    f0 _UU0393_ na t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1) ->
    f1 _UU0393_ na b t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1

  (** val coq_All_local_env_rec :
      'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
      'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
      coq_All_local_env -> 'a2 **)

  let rec coq_All_local_env_rec f f0 f1 _ = function
  | Coq_localenv_nil -> f
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    f0 _UU0393_ na t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1) ->
    f1 _UU0393_ na b t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  (** val coq_All_local_env_sig_pack :
      E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env **)

  let coq_All_local_env_sig_pack x all_local_env_var =
    x,all_local_env_var

  (** val coq_All_local_env_Signature :
      E.context -> ('a1 coq_All_local_env, E.context, 'a1
      coq_All_local_env_sig) coq_Signature **)

  let coq_All_local_env_Signature =
    coq_All_local_env_sig_pack

  (** val coq_NoConfusionPackage_All_local_env :
      (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_local_env =
    Build_NoConfusionPackage

  (** val localenv_cons :
      E.context -> aname -> T.term option -> T.term -> 'a1 coq_All_local_env
      -> 'a1 -> 'a1 coq_All_local_env **)

  let localenv_cons _UU0393_ na bo t0 x x0 =
    match bo with
    | Some b -> Coq_localenv_cons_def (_UU0393_, na, b, t0, x, x0)
    | None -> Coq_localenv_cons_abs (_UU0393_, na, t0, x, x0)

  (** val coq_All_local_env_snoc :
      E.context -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1 -> 'a1
      coq_All_local_env **)

  let coq_All_local_env_snoc _UU0393_ decl =
    let { decl_name = na; decl_body = bo; decl_type = t0 } = decl in
    localenv_cons _UU0393_ na bo t0

  (** val coq_All_local_env_tip :
      T.term context_decl list -> T.term context_decl -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_env * 'a1 **)

  let coq_All_local_env_tip _UU0393_ decl wf_UU0393_ =
    let wf_UU0393_0 = (snoc _UU0393_ decl),wf_UU0393_ in
    let wf_UU0393_2 = let _,pr2 = wf_UU0393_0 in pr2 in
    (match wf_UU0393_2 with
     | Coq_localenv_nil -> assert false (* absurd case *)
     | Coq_localenv_cons_abs (_, _, _, a, t0) -> (a, t0)
     | Coq_localenv_cons_def (_, _, _, _, a, t0) -> (a, t0))

  (** val coq_All_local_env_ind1 :
      'a2 -> (T.term context_decl list -> T.term context_decl -> 'a2 -> 'a1
      -> 'a2) -> E.context -> 'a1 coq_All_local_env -> 'a2 **)

  let rec coq_All_local_env_ind1 x x0 _UU0393_ x1 =
    match _UU0393_ with
    | [] -> x
    | y :: l ->
      let __top_assumption_ = coq_All_local_env_tip l y x1 in
      let _evar_0_ = fun _a_ _b_ ->
        x0 l y (coq_All_local_env_ind1 x x0 l _a_) _b_
      in
      let (a, b) = __top_assumption_ in _evar_0_ a b

  (** val coq_All_local_env_map :
      (T.term -> T.term) -> E.context -> 'a1 coq_All_local_env -> 'a1
      coq_All_local_env **)

  let rec coq_All_local_env_map f _ = function
  | Coq_localenv_nil -> Coq_localenv_nil
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a, t1) ->
    Coq_localenv_cons_abs
      ((let rec map0 = function
        | [] -> []
        | a0 :: t2 -> (map_decl f a0) :: (map0 t2)
        in map0 _UU0393_), (E.vass na t0).decl_name,
      (f (E.vass na t0).decl_type), (coq_All_local_env_map f _UU0393_ a), t1)
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a, t1) ->
    Coq_localenv_cons_def
      ((let rec map0 = function
        | [] -> []
        | a0 :: t2 -> (map_decl f a0) :: (map0 t2)
        in map0 _UU0393_), (E.vdef na b t0).decl_name, (f b),
      (f (E.vdef na b t0).decl_type), (coq_All_local_env_map f _UU0393_ a),
      t1)

  (** val coq_All_local_env_fold :
      (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
      coq_All_local_env) iffT **)

  let coq_All_local_env_fold f _UU0393_ =
    ((fun x ->
      let rec f0 _ = function
      | Coq_localenv_nil -> Coq_localenv_nil
      | Coq_localenv_cons_abs (_UU0393_0, na, t0, a0, t1) ->
        Coq_localenv_cons_abs ((fold_context_k f _UU0393_0),
          (E.vass na t0).decl_name,
          (f (length _UU0393_0) (E.vass na t0).decl_type), (f0 _UU0393_0 a0),
          t1)
      | Coq_localenv_cons_def (_UU0393_0, na, b, t0, a0, t1) ->
        Coq_localenv_cons_def ((fold_context_k f _UU0393_0),
          (E.vdef na b t0).decl_name, (f (length _UU0393_0) b),
          (f (length _UU0393_0) (E.vdef na b t0).decl_type),
          (f0 _UU0393_0 a0), t1)
      in f0 _UU0393_ x),
      (let rec f0 l h =
         match l with
         | [] -> Coq_localenv_nil
         | y :: l0 ->
           let { decl_name = decl_name0; decl_body = decl_body0; decl_type =
             decl_type0 } = y
           in
           (match decl_body0 with
            | Some t0 ->
              let h0 =
                (snoc (fold_context_k f l0)
                  (map_decl (f (length l0)) { decl_name = decl_name0;
                    decl_body = (Some t0); decl_type = decl_type0 })),h
              in
              let h2 = let _,pr2 = h0 in pr2 in
              (match h2 with
               | Coq_localenv_cons_def (_, _, _, _, a, p) ->
                 let iH_UU0393_ = f0 l0 a in
                 Coq_localenv_cons_def (l0, decl_name0, t0, decl_type0,
                 iH_UU0393_, p)
               | _ -> assert false (* absurd case *))
            | None ->
              let h0 =
                (snoc (fold_context_k f l0)
                  (map_decl (f (length l0)) { decl_name = decl_name0;
                    decl_body = None; decl_type = decl_type0 })),h
              in
              let h2 = let _,pr2 = h0 in pr2 in
              (match h2 with
               | Coq_localenv_cons_abs (_, _, _, a, p) ->
                 let iH_UU0393_ = f0 l0 a in
                 Coq_localenv_cons_abs (l0, decl_name0, decl_type0,
                 iH_UU0393_, p)
               | _ -> assert false (* absurd case *)))
       in f0 _UU0393_))

  (** val coq_All_local_env_impl_gen :
      E.context -> 'a1 coq_All_local_env -> (E.context -> T.term context_decl
      -> 'a1 -> 'a2) -> 'a2 coq_All_local_env **)

  let coq_All_local_env_impl_gen l h x =
    coq_All_local_env_ind1 Coq_localenv_nil
      (fun _UU0393_ decl iHAll_local_env x0 ->
      coq_All_local_env_snoc _UU0393_ decl iHAll_local_env
        (x _UU0393_ decl x0)) l h

  (** val coq_All_local_env_impl :
      E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a1
      -> 'a2) -> 'a2 coq_All_local_env **)

  let rec coq_All_local_env_impl _ a x =
    match a with
    | Coq_localenv_nil -> Coq_localenv_nil
    | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
      Coq_localenv_cons_abs (_UU0393_, na, t0,
        (coq_All_local_env_impl _UU0393_ a0 x),
        (x _UU0393_ { j_term = None; j_typ = t0; j_univ = None } t1))
    | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1) ->
      Coq_localenv_cons_def (_UU0393_, na, b, t0,
        (coq_All_local_env_impl _UU0393_ a0 x),
        (x _UU0393_ { j_term = (Some b); j_typ = t0; j_univ = None } t1))

  (** val coq_All_local_env_impl_ind :
      E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a2
      coq_All_local_env -> 'a1 -> 'a2) -> 'a2 coq_All_local_env **)

  let rec coq_All_local_env_impl_ind _ = function
  | Coq_localenv_nil -> (fun _ -> Coq_localenv_nil)
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    let iHX = coq_All_local_env_impl_ind _UU0393_ a0 in
    (fun x -> Coq_localenv_cons_abs (_UU0393_, na, t0, (iHX x),
    (x _UU0393_ { j_term = None; j_typ = t0; j_univ = None } (iHX x) t1)))
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1) ->
    let iHX = coq_All_local_env_impl_ind _UU0393_ a0 in
    (fun x -> Coq_localenv_cons_def (_UU0393_, na, b, t0, (iHX x),
    (x _UU0393_ { j_term = (Some b); j_typ = t0; j_univ = None } (iHX x) t1)))

  (** val coq_All_local_env_skipn :
      E.context -> nat -> 'a1 coq_All_local_env -> 'a1 coq_All_local_env **)

  let rec coq_All_local_env_skipn _UU0393_ n h_UU0393_ =
    match n with
    | O -> h_UU0393_
    | S n0 ->
      (match _UU0393_ with
       | [] -> h_UU0393_
       | c :: l ->
         let h_UU0393_0 = coq_All_local_env_tip l c h_UU0393_ in
         let (a, _) = h_UU0393_0 in coq_All_local_env_skipn l n0 a)

  (** val coq_All_local_env_app_skipn :
      T.term context_decl list -> T.term context_decl list -> nat -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_env **)

  let rec coq_All_local_env_app_skipn _UU0393_ _UU0394_ n h_UU0393_ =
    match n with
    | O -> h_UU0393_
    | S n0 ->
      (match _UU0394_ with
       | [] -> h_UU0393_
       | c :: l ->
         let h_UU0393_0 =
           coq_All_local_env_tip
             (let rec app0 l0 m =
                match l0 with
                | [] -> m
                | a :: l1 -> a :: (app0 l1 m)
              in app0 l _UU0393_) c h_UU0393_
         in
         let (a, _) = h_UU0393_0 in
         coq_All_local_env_app_skipn _UU0393_ l n0 a)

  (** val coq_All_local_env_nth_error :
      E.context -> nat -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1 **)

  let coq_All_local_env_nth_error _UU0393_ n _ x =
    let rec f l n0 x0 =
      match l with
      | [] -> (fun _ -> assert false (* absurd case *))
      | y :: l0 ->
        (match n0 with
         | O ->
           let __top_assumption_ = coq_All_local_env_tip l0 y x0 in
           let _evar_0_ = fun _ ondecl -> ondecl in
           (fun _ -> let (a, b) = __top_assumption_ in _evar_0_ a b)
         | S n1 ->
           let __top_assumption_ = coq_All_local_env_tip l0 y x0 in
           let _evar_0_ = fun wf_UU0393_ _ -> f l0 n1 wf_UU0393_ __ in
           (fun _ -> let (a, b) = __top_assumption_ in _evar_0_ a b))
    in f _UU0393_ n x __

  (** val coq_All_local_env_cst :
      E.context -> ('a1 coq_All_local_env, (T.term context_decl, 'a1)
      coq_All) iffT **)

  let coq_All_local_env_cst _UU0393_ =
    ((fun x ->
      coq_All_local_env_ind1 All_nil (fun _UU0393_0 decl iHX x0 -> All_cons
        (decl, _UU0393_0, x0, iHX)) _UU0393_ x), (fun x ->
      let rec f _ = function
      | All_nil -> Coq_localenv_nil
      | All_cons (x0, l, y, a0) -> coq_All_local_env_snoc l x0 (f l a0) y
      in f _UU0393_ x))

  type 'p coq_All_local_rel = 'p coq_All_local_env

  (** val coq_All_local_rel_nil :
      T.term context_decl list -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_nil _ =
    Coq_localenv_nil

  (** val coq_All_local_rel_snoc :
      T.term context_decl list -> E.context -> T.term context_decl -> 'a1
      coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_snoc _ =
    coq_All_local_env_snoc

  (** val coq_All_local_rel_abs :
      T.term context_decl list -> E.context -> T.term -> aname -> 'a1
      coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_abs _ _UU0393_' a na =
    localenv_cons _UU0393_' na None a

  (** val coq_All_local_rel_def :
      T.term context_decl list -> E.context -> T.term -> T.term -> aname ->
      'a1 coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_def _ _UU0393_' t0 a na =
    localenv_cons _UU0393_' na (Some t0) a

  (** val coq_All_local_rel_tip :
      T.term context_decl list -> T.term context_decl list -> T.term
      context_decl -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1 **)

  let coq_All_local_rel_tip _ =
    coq_All_local_env_tip

  (** val coq_All_local_rel_ind1 :
      T.term context_decl list -> 'a2 -> (T.term context_decl list -> T.term
      context_decl -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
      coq_All_local_rel -> 'a2 **)

  let coq_All_local_rel_ind1 _ =
    coq_All_local_env_ind1

  (** val coq_All_local_rel_local :
      E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_local _UU0393_ h =
    coq_All_local_env_impl _UU0393_ h (fun _ _ x -> x)

  (** val coq_All_local_local_rel :
      E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env **)

  let coq_All_local_local_rel _UU0393_ x =
    coq_All_local_env_impl _UU0393_ x (fun _ _ xX -> xX)

  (** val coq_All_local_app_rel :
      T.term context_decl list -> T.term context_decl list -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel **)

  let rec coq_All_local_app_rel _UU0393_ _UU0393_' h_UU0393_ =
    match _UU0393_' with
    | [] -> (h_UU0393_, Coq_localenv_nil)
    | y :: l ->
      let __top_assumption_ =
        coq_All_local_env_tip (app_context _UU0393_ l) y h_UU0393_
      in
      let _evar_0_ = fun h_UU0393_0 ona ->
        let p = coq_All_local_app_rel _UU0393_ l h_UU0393_0 in
        let (a, a0) = p in (a, (coq_All_local_rel_snoc _UU0393_ l y a0 ona))
      in
      let (a, b) = __top_assumption_ in _evar_0_ a b

  (** val coq_All_local_env_app_inv :
      T.term context_decl list -> T.term context_decl list -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel **)

  let coq_All_local_env_app_inv =
    coq_All_local_app_rel

  (** val coq_All_local_rel_app_inv :
      T.term context_decl list -> T.term context_decl list -> T.term
      context_decl list -> 'a1 coq_All_local_rel -> 'a1
      coq_All_local_rel * 'a1 coq_All_local_rel **)

  let coq_All_local_rel_app_inv _ _UU0393_' _UU0393_'' h =
    let h0 = coq_All_local_env_app_inv _UU0393_' _UU0393_'' h in
    let (a, a0) = h0 in
    (a, (coq_All_local_env_impl _UU0393_'' a0 (fun _ _ x -> x)))

  (** val coq_All_local_env_app :
      E.context -> E.context -> 'a1 coq_All_local_env -> 'a1
      coq_All_local_rel -> 'a1 coq_All_local_env **)

  let coq_All_local_env_app _UU0393_ _UU0393_' x x0 =
    coq_All_local_rel_ind1 _UU0393_ x (fun _UU0394_ decl iHX0 x1 ->
      coq_All_local_env_snoc (app_context _UU0393_ _UU0394_) decl iHX0 x1)
      _UU0393_' x0

  (** val coq_All_local_rel_app :
      T.term context_decl list -> E.context -> E.context -> 'a1
      coq_All_local_rel -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_app _UU0393_ _UU0393_' _UU0393_'' x x0 =
    coq_All_local_rel_ind1 (app_context _UU0393_ _UU0393_') x
      (fun _UU0394_ decl iHX0 x1 ->
      coq_All_local_rel_snoc _UU0393_ (app_context _UU0393_' _UU0394_) decl
        iHX0 x1) _UU0393_'' x0

  (** val coq_All_local_env_prod_inv :
      E.context -> ('a1 * 'a2) coq_All_local_env -> 'a1
      coq_All_local_env * 'a2 coq_All_local_env **)

  let coq_All_local_env_prod_inv _UU0393_ h =
    ((coq_All_local_env_impl _UU0393_ h (fun _ _ x -> let (p, _) = x in p)),
      (coq_All_local_env_impl _UU0393_ h (fun _ _ x -> let (_, q) = x in q)))

  (** val coq_All_local_env_lift_prod_inv :
      E.context -> ('a1 * 'a2) lift_typing0 coq_All_local_env -> 'a1
      lift_typing0 coq_All_local_env * 'a2 lift_typing0 coq_All_local_env **)

  let coq_All_local_env_lift_prod_inv _UU0394_ h =
    ((coq_All_local_env_impl _UU0394_ h (fun _ j h0 ->
       lift_typing_impl j h0 (fun _ _ __top_assumption_ ->
         let _evar_0_ = fun a _ -> a in
         let (a, b) = __top_assumption_ in _evar_0_ a b))),
      (coq_All_local_env_impl _UU0394_ h (fun _ j h0 ->
        lift_typing_impl j h0 (fun _ _ __top_assumption_ ->
          let _evar_0_ = fun _ b -> b in
          let (a, b) = __top_assumption_ in _evar_0_ a b))))

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'cproperty * 'sproperty

  (** val coq_All_local_env_over_sorting_rect :
      'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
      coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4
      -> 'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
      lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a3
      -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_sorting
      coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 **)

  let rec coq_All_local_env_over_sorting_rect f f0 f1 _ _ = function
  | Coq_localenv_over_nil -> f
  | Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
    f0 _UU0393_ na t0 all a
      (coq_All_local_env_over_sorting_rect f f0 f1 _UU0393_ all a) tu hs
  | Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, a, tu, hc, hs) ->
    f1 _UU0393_ na b t0 all a
      (coq_All_local_env_over_sorting_rect f f0 f1 _UU0393_ all a) tu hc hs

  (** val coq_All_local_env_over_sorting_rec :
      'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
      coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4
      -> 'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
      lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a3
      -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_sorting
      coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting -> 'a5 **)

  let rec coq_All_local_env_over_sorting_rec f f0 f1 _ _ = function
  | Coq_localenv_over_nil -> f
  | Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
    f0 _UU0393_ na t0 all a
      (coq_All_local_env_over_sorting_rec f f0 f1 _UU0393_ all a) tu hs
  | Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, a, tu, hc, hs) ->
    f1 _UU0393_ na b t0 all a
      (coq_All_local_env_over_sorting_rec f f0 f1 _UU0393_ all a) tu hc hs

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty)
    coq_All_local_env_over_sorting

  (** val coq_All_local_env_over_sorting_sig_pack :
      E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2,
      'a3, 'a4) coq_All_local_env_over_sorting -> (E.context * ('a1, 'a2)
      lift_sorting coq_All_local_env) * ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting **)

  let coq_All_local_env_over_sorting_sig_pack _UU0393_ x all_local_env_over_sorting_var =
    (_UU0393_,x),all_local_env_over_sorting_var

  (** val coq_All_local_env_over_sorting_Signature :
      E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> (('a1, 'a2,
      'a3, 'a4) coq_All_local_env_over_sorting, E.context * ('a1, 'a2)
      lift_sorting coq_All_local_env, ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_sorting_sig) coq_Signature **)

  let coq_All_local_env_over_sorting_Signature =
    coq_All_local_env_over_sorting_sig_pack

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing, 'property, 'property) coq_All_local_env_over_sorting

  (** val coq_All_local_env_over_sorting_2 :
      E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2,
      'a3, 'a4) coq_All_local_env_over_sorting -> ('a1 * 'a3, 'a2 * 'a4)
      lift_sorting coq_All_local_env **)

  let rec coq_All_local_env_over_sorting_2 _ _ = function
  | Coq_localenv_over_nil -> Coq_localenv_nil
  | Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
    Coq_localenv_cons_abs (_UU0393_, na, t0,
      (coq_All_local_env_over_sorting_2 _UU0393_ all a),
      (let (_, s) = tu in
       let Coq_existT (x, p) = s in
       let (s0, o) = p in (o, (Coq_existT (x, ((s0, hs), o))))))
  | Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, a, tu, hc, hs) ->
    Coq_localenv_cons_def (_UU0393_, na, b, t0,
      (coq_All_local_env_over_sorting_2 _UU0393_ all a),
      (let (o, s) = tu in
       let Coq_existT (x, p) = s in
       let (s0, o0) = p in
       ((Obj.magic (o, hc)), (Coq_existT (x, ((s0, hs), o0))))))

  type ('typing, 'p) on_wf_local_decl = __

  (** val nth_error_All_local_env_over :
      T.term context_decl list -> nat -> T.term context_decl -> 'a1
      lift_typing0 coq_All_local_env -> ('a1, 'a2) coq_All_local_env_over ->
      ('a1, 'a2) coq_All_local_env_over * ('a1, 'a2) on_wf_local_decl **)

  let rec nth_error_All_local_env_over _ n decl _ = function
  | Coq_localenv_over_nil -> assert false (* absurd case *)
  | Coq_localenv_over_cons_abs (_UU0393_, _, _, all, a, _, hs) ->
    (match n with
     | O -> (a, (Obj.magic hs))
     | S n0 -> nth_error_All_local_env_over _UU0393_ n0 decl all a)
  | Coq_localenv_over_cons_def (_UU0393_, _, _, _, all, a, _, hc, hs) ->
    (match n with
     | O -> (a, (Obj.magic (hc, hs)))
     | S n0 -> nth_error_All_local_env_over _UU0393_ n0 decl all a)

  (** val coq_All_local_env_over_2 :
      E.context -> 'a1 lift_typing0 coq_All_local_env -> ('a1, 'a2)
      coq_All_local_env_over -> ('a1, 'a2) lift_typing_conj coq_All_local_env **)

  let coq_All_local_env_over_2 =
    coq_All_local_env_over_sorting_2

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  (** val ctx_inst_rect :
      E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
      E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
      T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
      T.term list -> E.context -> 'a1 ctx_inst -> 'a2 **)

  let rec ctx_inst_rect _UU0393_ f f0 f1 _ _ = function
  | Coq_ctx_inst_nil -> f
  | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
    f0 na t0 i inst _UU0394_ t1 c
      (ctx_inst_rect _UU0393_ f f0 f1 inst
        (E.subst_telescope (i :: []) O _UU0394_) c)
  | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
    f1 na b t0 inst _UU0394_ c
      (ctx_inst_rect _UU0393_ f f0 f1 inst
        (E.subst_telescope (b :: []) O _UU0394_) c)

  (** val ctx_inst_rec :
      E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
      E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
      T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
      T.term list -> E.context -> 'a1 ctx_inst -> 'a2 **)

  let rec ctx_inst_rec _UU0393_ f f0 f1 _ _ = function
  | Coq_ctx_inst_nil -> f
  | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
    f0 na t0 i inst _UU0394_ t1 c
      (ctx_inst_rec _UU0393_ f f0 f1 inst
        (E.subst_telescope (i :: []) O _UU0394_) c)
  | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
    f1 na b t0 inst _UU0394_ c
      (ctx_inst_rec _UU0393_ f f0 f1 inst
        (E.subst_telescope (b :: []) O _UU0394_) c)

  type 'typing ctx_inst_sig = 'typing ctx_inst

  (** val ctx_inst_sig_pack :
      E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term
      list * E.context) * 'a1 ctx_inst **)

  let ctx_inst_sig_pack _ x x0 ctx_inst_var =
    (x,x0),ctx_inst_var

  (** val ctx_inst_Signature :
      E.context -> T.term list -> E.context -> ('a1 ctx_inst, T.term
      list * E.context, 'a1 ctx_inst_sig) coq_Signature **)

  let ctx_inst_Signature =
    ctx_inst_sig_pack

  (** val coq_NoConfusionPackage_ctx_inst :
      E.context -> ((T.term list * E.context) * 'a1 ctx_inst)
      coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_ctx_inst _ =
    Build_NoConfusionPackage

  (** val ctx_inst_impl_gen :
      E.context -> T.term list -> E.context -> __ list -> (__, __ ctx_inst)
      sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1) -> (__, __
      ctx_inst) coq_All -> 'a1 ctx_inst **)

  let ctx_inst_impl_gen _ inst _UU0394_ args x hPQ h =
    let Coq_existT (_, c) = x in
    let rec f _ _ c0 h0 =
      match c0 with
      | Coq_ctx_inst_nil -> Coq_ctx_inst_nil
      | Coq_ctx_inst_ass (na, t0, i, inst0, _UU0394_0, _, c1) ->
        Coq_ctx_inst_ass (na, t0, i, inst0, _UU0394_0,
          (hPQ i t0
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_ass (_, _, _, _, _, x1, _) -> x1
              | _ -> assert false (* absurd case *)))),
          (f inst0 (E.subst_telescope (i :: []) O _UU0394_0) c1
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_ass (_, _, _, _, _, _, x1) -> x1
              | _ -> assert false (* absurd case *)))))
      | Coq_ctx_inst_def (na, b, t0, inst0, _UU0394_0, c1) ->
        Coq_ctx_inst_def (na, b, t0, inst0, _UU0394_0,
          (f inst0 (E.subst_telescope (b :: []) O _UU0394_0) c1
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_def (_, _, _, _, _, x1) -> x1
              | _ -> assert false (* absurd case *)))))
    in f inst _UU0394_ c h

  (** val ctx_inst_impl :
      E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term ->
      T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst **)

  let rec ctx_inst_impl _UU0393_ _ _ h hPQ =
    match h with
    | Coq_ctx_inst_nil -> Coq_ctx_inst_nil
    | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
      Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, (hPQ i t0 t1),
        (ctx_inst_impl _UU0393_ inst (E.subst_telescope (i :: []) O _UU0394_)
          c hPQ))
    | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
      Coq_ctx_inst_def (na, b, t0, inst, _UU0394_,
        (ctx_inst_impl _UU0393_ inst (E.subst_telescope (b :: []) O _UU0394_)
          c hPQ))

  (** val option_default_size :
      ('a1 -> 'a2 -> size) -> 'a1 option -> __ -> size **)

  let option_default_size fsize o w =
    match o with
    | Some tm -> Obj.magic fsize tm w
    | None -> O

  (** val lift_sorting_size_gen :
      (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size)
      -> nat -> E.judgment -> ('a1, 'a2) lift_sorting -> size **)

  let lift_sorting_size_gen csize ssize base j w =
    add
      (add base
        (option_default_size (fun tm -> csize tm j.j_typ) j.j_term (fst w)))
      (ssize j.j_typ (projT1 (snd w)) (fst (projT2 (snd w))))

  (** val lift_sorting_size_gen_impl :
      (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size)
      -> E.judgment -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 ->
      __ -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
      lift_sorting **)

  let lift_sorting_size_gen_impl _ _ j tu hPQc hPQs =
    let (o, s) = tu in
    let Coq_existT (x, p) = s in
    let (s0, o0) = p in
    ((let o1 = j.j_term in
      match o1 with
      | Some t0 -> Obj.magic hPQc t0 j.j_typ o __
      | None -> o), (Coq_existT (x, ((hPQs j.j_typ x s0 __), o0))))

  (** val on_def_type_size_gen :
      (E.context -> T.term -> Sort.t -> 'a2 -> size) -> nat -> E.context ->
      T.term def -> ('a1, 'a2) lift_sorting on_def_type -> size **)

  let on_def_type_size_gen ssize base _UU0393_ d w =
    add base (ssize _UU0393_ d.dtype (projT1 (snd w)) (fst (projT2 (snd w))))

  (** val on_def_body_size_gen :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term
      -> Sort.t -> 'a2 -> size) -> nat -> T.term context_decl list -> T.term
      context_decl list -> T.term def -> ('a1, 'a2) lift_sorting on_def_body
      -> size **)

  let on_def_body_size_gen csize ssize base types _UU0393_ d w =
    add
      (add base
        (Obj.magic csize (app_context _UU0393_ types) d.dbody
          (T.lift (length types) O d.dtype) (fst w)))
      (ssize (app_context _UU0393_ types) (T.lift (length types) O d.dtype)
        (projT1 (snd w)) (fst (projT2 (snd w))))

  (** val lift_sorting_size_impl :
      E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> (T.term -> Sort.t ->
      'a2 -> size) -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 ->
      __ -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
      lift_sorting **)

  let lift_sorting_size_impl j csize ssize tu xc xs =
    lift_sorting_size_gen_impl csize ssize j tu (fun t0 t1 hty _ ->
      xc t0 t1 hty __) (fun t0 u hty _ -> xs t0 u hty __)

  (** val lift_typing_size_impl :
      E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> 'a1 lift_typing0 ->
      (T.term -> T.term -> 'a1 -> __ -> 'a2) -> 'a2 lift_typing0 **)

  let lift_typing_size_impl j psize tu x =
    lift_sorting_size_gen_impl psize (fun t0 s tu0 ->
      psize t0 (T.tSort s) tu0) j tu x (fun t0 t1 -> x t0 (T.tSort t1))

  (** val coq_All_local_env_size_gen :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term
      -> Sort.t -> 'a2 -> size) -> size -> E.context -> ('a1, 'a2)
      lift_sorting coq_All_local_env -> size **)

  let rec coq_All_local_env_size_gen csize ssize base _ = function
  | Coq_localenv_nil -> base
  | Coq_localenv_cons_abs (_UU0393_', _, t0, w', p) ->
    add (ssize _UU0393_' t0 (projT1 (snd p)) (fst (projT2 (snd p))))
      (coq_All_local_env_size_gen csize ssize base _UU0393_' w')
  | Coq_localenv_cons_def (_UU0393_', _, b, t0, w', p) ->
    add
      (add (Obj.magic csize _UU0393_' b t0 (fst p))
        (ssize _UU0393_' t0 (projT1 (snd p)) (fst (projT2 (snd p)))))
      (coq_All_local_env_size_gen csize ssize base _UU0393_' w')

  (** val coq_All_local_env_size :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context -> ('a1,
      'a1) lift_sorting coq_All_local_env -> size **)

  let coq_All_local_env_size typing_size =
    coq_All_local_env_size_gen typing_size (fun _UU0393_ t0 s ->
      typing_size _UU0393_ t0 (T.tSort s)) O

  (** val coq_All_local_rel_size :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context ->
      E.context -> 'a1 lift_typing0 coq_All_local_rel -> size **)

  let coq_All_local_rel_size typing_size _UU0393_ _UU0393_' wf_UU0393_ =
    coq_All_local_env_size_gen (fun _UU0394_0 ->
      typing_size (app_context _UU0393_ _UU0394_0)) (fun _UU0394_0 ->
      let _UU0393_0 = app_context _UU0393_ _UU0394_0 in
      (fun t0 s tu -> typing_size _UU0393_0 t0 (T.tSort s) tu)) O _UU0393_'
      wf_UU0393_

  (** val coq_All_local_env_sorting_size :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term
      -> Sort.t -> 'a2 -> size) -> E.context -> ('a1, 'a2) lift_sorting
      coq_All_local_env -> size **)

  let coq_All_local_env_sorting_size checking_size sorting_size =
    coq_All_local_env_size_gen checking_size sorting_size (S O)

  (** val coq_All_local_rel_sorting_size :
      (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term
      -> Sort.t -> 'a2 -> size) -> T.term context_decl list -> E.context ->
      ('a1, 'a2) lift_sorting coq_All_local_rel -> size **)

  let coq_All_local_rel_sorting_size checking_size sorting_size _UU0393_ _UU0394_ w =
    coq_All_local_env_size_gen (fun _UU0394_0 ->
      checking_size (app_context _UU0393_ _UU0394_0)) (fun _UU0394_0 ->
      sorting_size (app_context _UU0393_ _UU0394_0)) (S O) _UU0394_ w
 end

module Conversion =
 functor (T:Environment.Term) ->
 functor (E:sig
  type judgment = (Sort.t, T.term) judgment_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Sort.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Sort.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
    one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

  type global_declarations = (kername * global_decl) list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Environment.Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Environment.Retroknowledge.t

  val empty_global_env : global_env

  val add_global_decl : global_env -> (kername * global_decl) -> global_env

  val set_declarations : global_env -> global_declarations -> global_env

  val lookup_global : global_declarations -> kername -> global_decl option

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_globals : global_declarations -> kername -> global_decl list

  val lookup_envs : global_env -> kername -> global_decl list

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  val strictly_extends_decls_extends_part_globals :
    (kername * global_decl) list -> (kername * global_decl) list ->
    ((kername * global_decl) list, __) sigT -> kername -> (global_decl list,
    __) sigT

  val strictly_extends_decls_extends_part :
    global_env -> global_env -> ((kername * global_decl) list, __) sigT ->
    kername -> (global_decl list, __) sigT

  val strictly_extends_decls_extends_decls :
    global_env -> global_env -> strictly_extends_decls -> extends_decls

  val strictly_extends_decls_extends_strictly_on_decls :
    global_env -> global_env -> strictly_extends_decls ->
    extends_strictly_on_decls

  val extends_decls_extends :
    global_env -> global_env -> extends_decls -> extends

  val extends_strictly_on_decls_extends :
    global_env -> global_env -> extends_strictly_on_decls -> extends

  val strictly_extends_decls_extends_decls_subrel :
    (global_env, strictly_extends_decls, extends_decls) subrelation

  val strictly_extends_decls_extends_strictly_on_decls_subrel :
    (global_env, strictly_extends_decls, extends_strictly_on_decls)
    subrelation

  val extends_decls_extends_subrel :
    (global_env, extends_decls, extends) subrelation

  val extends_strictly_on_decls_extends_subrel :
    (global_env, extends_strictly_on_decls, extends) subrelation

  val strictly_extends_decls_extends_subrel :
    (global_env, strictly_extends_decls, extends) subrelation

  val strictly_extends_decls_refl :
    (global_env, strictly_extends_decls) coq_Reflexive

  val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

  val extends_strictly_on_decls_refl :
    (global_env, extends_strictly_on_decls) coq_Reflexive

  val extends_refl : (global_env, extends) coq_Reflexive

  val extends_decls_part_globals_refl :
    global_declarations -> kername -> (global_decl list, __) sigT

  val extends_decls_part_refl :
    global_env -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_refl :
    global_declarations -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_refl :
    global_env -> ((kername * global_decl) list, __) sigT

  val extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
    list, __) sigT) -> kername -> (global_decl list, __) sigT

  val extends_decls_part_trans :
    global_env -> global_env -> global_env -> (kername -> (global_decl list,
    __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername ->
    (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    ((kername * global_decl) list, __) sigT -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_trans :
    global_env -> global_env -> global_env -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT ->
    ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_trans :
    (global_env, strictly_extends_decls) coq_Transitive

  val extends_decls_trans : (global_env, extends_decls) coq_Transitive

  val extends_strictly_on_decls_trans :
    (global_env, extends_strictly_on_decls) coq_Transitive

  val extends_trans : (global_env, extends) coq_Transitive

  val declared_kername_set : global_declarations -> KernameSet.t

  val merge_globals :
    global_declarations -> global_declarations -> global_declarations

  val merge_global_envs : global_env -> global_env -> global_env

  val strictly_extends_decls_l_merge_globals :
    global_declarations -> global_declarations -> ((kername * global_decl)
    list, __) sigT

  val extends_l_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_strictly_on_decls_l_merge :
    global_env -> global_env -> extends_strictly_on_decls

  val extends_l_merge : global_env -> global_env -> extends

  val extends_r_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_r_merge : global_env -> global_env -> extends

  val primitive_constant : global_env -> prim_tag -> kername option

  val tImpl : T.term -> T.term -> T.term

  val array_uctx : name list * ConstraintSet.t

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * T.term

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context * Sort.t) option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type 'wf_term lift_wf_term = __ * 'wf_term

  type ('wf_term, 'wf_univ) lift_wfu_term = __ * ('wf_term * __)

  val lift_wfb_term : (T.term -> bool) -> E.judgment -> bool

  val lift_wfbu_term :
    (T.term -> bool) -> (Sort.t -> bool) -> E.judgment -> bool

  type ('checking, 'sorting) lift_sorting = __ * (Sort.t, 'sorting * __) sigT

  type 'typing lift_typing0 = ('typing, 'typing) lift_sorting

  type ('p, 'q) lift_typing_conj = ('p * 'q) lift_typing0

  val lift_wf_term_it_impl :
    T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
    Sort.t option -> 'a1 lift_wf_term -> __ -> ('a1 -> 'a2) -> 'a2
    lift_wf_term

  val lift_wf_term_f_impl :
    T.term option -> T.term -> Sort.t option -> Sort.t option -> (T.term ->
    T.term) -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2 lift_wf_term

  val lift_wf_term_impl :
    E.judgment -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2
    lift_wf_term

  val unlift_TermTyp :
    T.term -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting -> 'a1

  val unlift_TypUniv :
    T.term option -> T.term -> Sort.t -> ('a1, 'a2) lift_sorting -> 'a2

  val lift_sorting_extract :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_forget_univ :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_forget_body :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_ex_it_impl_gen :
    T.term option -> T.term option -> T.term -> T.term -> ('a1, 'a3)
    lift_sorting -> __ -> ('a3 -> (Sort.t, 'a4) sigT) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_it_impl_gen :
    T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
    ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_fu_it_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_f_it_impl :
    E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> __ -> ('a3
    -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_it_impl :
    E.judgment -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_fu_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> ('a1, 'a3) lift_sorting -> (T.term -> T.term -> 'a1 -> 'a2)
    -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_fu_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2
    lift_typing0

  val lift_sorting_f_impl :
    E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> (T.term ->
    T.term -> 'a1 -> 'a2) -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_typing_f_impl :
    E.judgment -> (T.term -> T.term) -> 'a1 lift_typing0 -> (T.term -> T.term
    -> 'a1 -> 'a2) -> 'a2 lift_typing0

  val lift_typing_map :
    (T.term -> T.term) -> E.judgment -> 'a1 lift_typing0 -> 'a1 lift_typing0

  val lift_typing_mapu :
    (T.term -> T.term) -> (Sort.t -> Sort.t) -> T.term option -> T.term ->
    Sort.t option -> 'a1 lift_typing0 -> 'a1 lift_typing0

  val lift_sorting_impl :
    E.judgment -> ('a1, 'a3) lift_sorting -> (T.term -> T.term -> 'a1 -> 'a2)
    -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_impl :
    E.judgment -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2
    lift_typing0

  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val localenv_cons :
    E.context -> aname -> T.term option -> T.term -> 'a1 coq_All_local_env ->
    'a1 -> 'a1 coq_All_local_env

  val coq_All_local_env_snoc :
    E.context -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1 -> 'a1
    coq_All_local_env

  val coq_All_local_env_tip :
    T.term context_decl list -> T.term context_decl -> 'a1 coq_All_local_env
    -> 'a1 coq_All_local_env * 'a1

  val coq_All_local_env_ind1 :
    'a2 -> (T.term context_decl list -> T.term context_decl -> 'a2 -> 'a1 ->
    'a2) -> E.context -> 'a1 coq_All_local_env -> 'a2

  val coq_All_local_env_map :
    (T.term -> T.term) -> E.context -> 'a1 coq_All_local_env -> 'a1
    coq_All_local_env

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl_gen :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term context_decl
    -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a1 ->
    'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a2
    coq_All_local_env -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> nat -> 'a1 coq_All_local_env -> 'a1 coq_All_local_env

  val coq_All_local_env_app_skipn :
    T.term context_decl list -> T.term context_decl list -> nat -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env

  val coq_All_local_env_nth_error :
    E.context -> nat -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1

  val coq_All_local_env_cst :
    E.context -> ('a1 coq_All_local_env, (T.term context_decl, 'a1) coq_All)
    iffT

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil :
    T.term context_decl list -> 'a1 coq_All_local_rel

  val coq_All_local_rel_snoc :
    T.term context_decl list -> E.context -> T.term context_decl -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    T.term context_decl list -> E.context -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    T.term context_decl list -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_tip :
    T.term context_decl list -> T.term context_decl list -> T.term
    context_decl -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1

  val coq_All_local_rel_ind1 :
    T.term context_decl list -> 'a2 -> (T.term context_decl list -> T.term
    context_decl -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1 coq_All_local_rel
    -> 'a2

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    T.term context_decl list -> T.term context_decl list -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_env_app_inv :
    T.term context_decl list -> T.term context_decl list -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_rel_app_inv :
    T.term context_decl list -> T.term context_decl list -> T.term
    context_decl list -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1
    coq_All_local_rel

  val coq_All_local_env_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  val coq_All_local_rel_app :
    T.term context_decl list -> E.context -> E.context -> 'a1
    coq_All_local_rel -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel

  val coq_All_local_env_prod_inv :
    E.context -> ('a1 * 'a2) coq_All_local_env -> 'a1 coq_All_local_env * 'a2
    coq_All_local_env

  val coq_All_local_env_lift_prod_inv :
    E.context -> ('a1 * 'a2) lift_typing0 coq_All_local_env -> 'a1
    lift_typing0 coq_All_local_env * 'a2 lift_typing0 coq_All_local_env

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'cproperty * 'sproperty

  val coq_All_local_env_over_sorting_rect :
    'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4 -> 'a5) -> (E.context -> aname
    -> T.term -> T.term -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1,
    'a2, 'a3, 'a4) coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2)
    lift_sorting -> 'a3 -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5

  val coq_All_local_env_over_sorting_rec :
    'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4 -> 'a5) -> (E.context -> aname
    -> T.term -> T.term -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1,
    'a2, 'a3, 'a4) coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2)
    lift_sorting -> 'a3 -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty)
    coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_sig_pack :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_sorting -> (E.context * ('a1, 'a2)
    lift_sorting coq_All_local_env) * ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_Signature :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> (('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_sorting, E.context * ('a1, 'a2)
    lift_sorting coq_All_local_env, ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing, 'property, 'property) coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_2 :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_sorting -> ('a1 * 'a3, 'a2 * 'a4)
    lift_sorting coq_All_local_env

  type ('typing, 'p) on_wf_local_decl = __

  val nth_error_All_local_env_over :
    T.term context_decl list -> nat -> T.term context_decl -> 'a1
    lift_typing0 coq_All_local_env -> ('a1, 'a2) coq_All_local_env_over ->
    ('a1, 'a2) coq_All_local_env_over * ('a1, 'a2) on_wf_local_decl

  val coq_All_local_env_over_2 :
    E.context -> 'a1 lift_typing0 coq_All_local_env -> ('a1, 'a2)
    coq_All_local_env_over -> ('a1, 'a2) lift_typing_conj coq_All_local_env

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
    E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
    T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
    T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
    E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
    T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
    T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term
    list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.context -> T.term list -> E.context -> ('a1 ctx_inst, T.term
    list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.context -> ((T.term list * E.context) * 'a1 ctx_inst)
    coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.context -> T.term list -> E.context -> __ list -> (__, __ ctx_inst)
    sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1) -> (__, __
    ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term ->
    T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val option_default_size : ('a1 -> 'a2 -> size) -> 'a1 option -> __ -> size

  val lift_sorting_size_gen :
    (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size) ->
    nat -> E.judgment -> ('a1, 'a2) lift_sorting -> size

  val lift_sorting_size_gen_impl :
    (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size) ->
    E.judgment -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 -> __
    -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val on_def_type_size_gen :
    (E.context -> T.term -> Sort.t -> 'a2 -> size) -> nat -> E.context ->
    T.term def -> ('a1, 'a2) lift_sorting on_def_type -> size

  val on_def_body_size_gen :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> nat -> T.term context_decl list -> T.term
    context_decl list -> T.term def -> ('a1, 'a2) lift_sorting on_def_body ->
    size

  val lift_sorting_size_impl :
    E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> (T.term -> Sort.t ->
    'a2 -> size) -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 -> __
    -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val lift_typing_size_impl :
    E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> 'a1 lift_typing0 ->
    (T.term -> T.term -> 'a1 -> __ -> 'a2) -> 'a2 lift_typing0

  val coq_All_local_env_size_gen :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> size -> E.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> size

  val coq_All_local_env_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context -> ('a1, 'a1)
    lift_sorting coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context -> E.context
    -> 'a1 lift_typing0 coq_All_local_rel -> size

  val coq_All_local_env_sorting_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> E.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> T.term context_decl list -> E.context -> ('a1,
    'a2) lift_sorting coq_All_local_rel -> size
 end) ->
 struct
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  (** val coq_All_decls_alpha_pb_rect :
      conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term
      -> __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot ->
      T.term -> T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) ->
      T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2 **)

  let coq_All_decls_alpha_pb_rect _ f f0 _ _ = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    f0 na na' b t0 b' t' __ eqb eqt

  (** val coq_All_decls_alpha_pb_rec :
      conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term
      -> __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot ->
      T.term -> T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) ->
      T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2 **)

  let coq_All_decls_alpha_pb_rec _ f f0 _ _ = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    f0 na na' b t0 b' t' __ eqb eqt

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  (** val coq_All_decls_alpha_pb_sig_pack :
      conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> (T.term context_decl * T.term
      context_decl) * 'a1 coq_All_decls_alpha_pb **)

  let coq_All_decls_alpha_pb_sig_pack _ x x0 all_decls_alpha_pb_var =
    (x,x0),all_decls_alpha_pb_var

  (** val coq_All_decls_alpha_pb_Signature :
      conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
      coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
      coq_All_decls_alpha_pb_sig) coq_Signature **)

  let coq_All_decls_alpha_pb_Signature =
    coq_All_decls_alpha_pb_sig_pack

  (** val coq_NoConfusionPackage_All_decls_alpha_pb :
      conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
      coq_All_decls_alpha_pb) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_decls_alpha_pb _ =
    Build_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  (** val coq_All_decls_alpha_pb_impl :
      conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
      T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
      coq_All_decls_alpha_pb **)

  let coq_All_decls_alpha_pb_impl pb _ _ x = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
    Coq_all_decls_alpha_vass (na, na', t0, t', (x pb t0 t' eqt))
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', (x Conv b b' eqb),
      (x pb t0 t' eqt))
 end

module GlobalMaps =
 functor (T:Environment.Term) ->
 functor (E:sig
  type judgment = (Sort.t, T.term) judgment_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Sort.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Sort.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
    one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

  type global_declarations = (kername * global_decl) list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Environment.Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Environment.Retroknowledge.t

  val empty_global_env : global_env

  val add_global_decl : global_env -> (kername * global_decl) -> global_env

  val set_declarations : global_env -> global_declarations -> global_env

  val lookup_global : global_declarations -> kername -> global_decl option

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_globals : global_declarations -> kername -> global_decl list

  val lookup_envs : global_env -> kername -> global_decl list

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername * global_decl) list, __) sigT, __) and3

  val strictly_extends_decls_extends_part_globals :
    (kername * global_decl) list -> (kername * global_decl) list ->
    ((kername * global_decl) list, __) sigT -> kername -> (global_decl list,
    __) sigT

  val strictly_extends_decls_extends_part :
    global_env -> global_env -> ((kername * global_decl) list, __) sigT ->
    kername -> (global_decl list, __) sigT

  val strictly_extends_decls_extends_decls :
    global_env -> global_env -> strictly_extends_decls -> extends_decls

  val strictly_extends_decls_extends_strictly_on_decls :
    global_env -> global_env -> strictly_extends_decls ->
    extends_strictly_on_decls

  val extends_decls_extends :
    global_env -> global_env -> extends_decls -> extends

  val extends_strictly_on_decls_extends :
    global_env -> global_env -> extends_strictly_on_decls -> extends

  val strictly_extends_decls_extends_decls_subrel :
    (global_env, strictly_extends_decls, extends_decls) subrelation

  val strictly_extends_decls_extends_strictly_on_decls_subrel :
    (global_env, strictly_extends_decls, extends_strictly_on_decls)
    subrelation

  val extends_decls_extends_subrel :
    (global_env, extends_decls, extends) subrelation

  val extends_strictly_on_decls_extends_subrel :
    (global_env, extends_strictly_on_decls, extends) subrelation

  val strictly_extends_decls_extends_subrel :
    (global_env, strictly_extends_decls, extends) subrelation

  val strictly_extends_decls_refl :
    (global_env, strictly_extends_decls) coq_Reflexive

  val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

  val extends_strictly_on_decls_refl :
    (global_env, extends_strictly_on_decls) coq_Reflexive

  val extends_refl : (global_env, extends) coq_Reflexive

  val extends_decls_part_globals_refl :
    global_declarations -> kername -> (global_decl list, __) sigT

  val extends_decls_part_refl :
    global_env -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_refl :
    global_declarations -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_refl :
    global_env -> ((kername * global_decl) list, __) sigT

  val extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
    list, __) sigT) -> kername -> (global_decl list, __) sigT

  val extends_decls_part_trans :
    global_env -> global_env -> global_env -> (kername -> (global_decl list,
    __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername ->
    (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    ((kername * global_decl) list, __) sigT -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_part_trans :
    global_env -> global_env -> global_env -> ((kername * global_decl) list,
    __) sigT -> ((kername * global_decl) list, __) sigT ->
    ((kername * global_decl) list, __) sigT

  val strictly_extends_decls_trans :
    (global_env, strictly_extends_decls) coq_Transitive

  val extends_decls_trans : (global_env, extends_decls) coq_Transitive

  val extends_strictly_on_decls_trans :
    (global_env, extends_strictly_on_decls) coq_Transitive

  val extends_trans : (global_env, extends) coq_Transitive

  val declared_kername_set : global_declarations -> KernameSet.t

  val merge_globals :
    global_declarations -> global_declarations -> global_declarations

  val merge_global_envs : global_env -> global_env -> global_env

  val strictly_extends_decls_l_merge_globals :
    global_declarations -> global_declarations -> ((kername * global_decl)
    list, __) sigT

  val extends_l_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_strictly_on_decls_l_merge :
    global_env -> global_env -> extends_strictly_on_decls

  val extends_l_merge : global_env -> global_env -> extends

  val extends_r_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_r_merge : global_env -> global_env -> extends

  val primitive_constant : global_env -> prim_tag -> kername option

  val tImpl : T.term -> T.term -> T.term

  val array_uctx : name list * ConstraintSet.t

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * T.term

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context * Sort.t) option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type 'wf_term lift_wf_term = __ * 'wf_term

  type ('wf_term, 'wf_univ) lift_wfu_term = __ * ('wf_term * __)

  val lift_wfb_term : (T.term -> bool) -> E.judgment -> bool

  val lift_wfbu_term :
    (T.term -> bool) -> (Sort.t -> bool) -> E.judgment -> bool

  type ('checking, 'sorting) lift_sorting = __ * (Sort.t, 'sorting * __) sigT

  type 'typing lift_typing0 = ('typing, 'typing) lift_sorting

  type ('p, 'q) lift_typing_conj = ('p * 'q) lift_typing0

  val lift_wf_term_it_impl :
    T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
    Sort.t option -> 'a1 lift_wf_term -> __ -> ('a1 -> 'a2) -> 'a2
    lift_wf_term

  val lift_wf_term_f_impl :
    T.term option -> T.term -> Sort.t option -> Sort.t option -> (T.term ->
    T.term) -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2 lift_wf_term

  val lift_wf_term_impl :
    E.judgment -> 'a1 lift_wf_term -> (T.term -> 'a1 -> 'a2) -> 'a2
    lift_wf_term

  val unlift_TermTyp :
    T.term -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting -> 'a1

  val unlift_TypUniv :
    T.term option -> T.term -> Sort.t -> ('a1, 'a2) lift_sorting -> 'a2

  val lift_sorting_extract :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_forget_univ :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_forget_body :
    T.term option -> T.term -> Sort.t option -> ('a1, 'a2) lift_sorting ->
    ('a1, 'a2) lift_sorting

  val lift_sorting_ex_it_impl_gen :
    T.term option -> T.term option -> T.term -> T.term -> ('a1, 'a3)
    lift_sorting -> __ -> ('a3 -> (Sort.t, 'a4) sigT) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_it_impl_gen :
    T.term option -> T.term option -> T.term -> T.term -> Sort.t option ->
    ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_fu_it_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_f_it_impl :
    E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> __ -> ('a3
    -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_it_impl :
    E.judgment -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_fu_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> ('a1, 'a3) lift_sorting -> (T.term -> T.term -> 'a1 -> 'a2)
    -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_fu_impl :
    T.term option -> T.term -> Sort.t option -> (T.term -> T.term) -> (Sort.t
    -> Sort.t) -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2
    lift_typing0

  val lift_sorting_f_impl :
    E.judgment -> (T.term -> T.term) -> ('a1, 'a3) lift_sorting -> (T.term ->
    T.term -> 'a1 -> 'a2) -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_typing_f_impl :
    E.judgment -> (T.term -> T.term) -> 'a1 lift_typing0 -> (T.term -> T.term
    -> 'a1 -> 'a2) -> 'a2 lift_typing0

  val lift_typing_map :
    (T.term -> T.term) -> E.judgment -> 'a1 lift_typing0 -> 'a1 lift_typing0

  val lift_typing_mapu :
    (T.term -> T.term) -> (Sort.t -> Sort.t) -> T.term option -> T.term ->
    Sort.t option -> 'a1 lift_typing0 -> 'a1 lift_typing0

  val lift_sorting_impl :
    E.judgment -> ('a1, 'a3) lift_sorting -> (T.term -> T.term -> 'a1 -> 'a2)
    -> (T.term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_impl :
    E.judgment -> 'a1 lift_typing0 -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2
    lift_typing0

  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val localenv_cons :
    E.context -> aname -> T.term option -> T.term -> 'a1 coq_All_local_env ->
    'a1 -> 'a1 coq_All_local_env

  val coq_All_local_env_snoc :
    E.context -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1 -> 'a1
    coq_All_local_env

  val coq_All_local_env_tip :
    T.term context_decl list -> T.term context_decl -> 'a1 coq_All_local_env
    -> 'a1 coq_All_local_env * 'a1

  val coq_All_local_env_ind1 :
    'a2 -> (T.term context_decl list -> T.term context_decl -> 'a2 -> 'a1 ->
    'a2) -> E.context -> 'a1 coq_All_local_env -> 'a2

  val coq_All_local_env_map :
    (T.term -> T.term) -> E.context -> 'a1 coq_All_local_env -> 'a1
    coq_All_local_env

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl_gen :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term context_decl
    -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a1 ->
    'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> E.judgment -> 'a2
    coq_All_local_env -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> nat -> 'a1 coq_All_local_env -> 'a1 coq_All_local_env

  val coq_All_local_env_app_skipn :
    T.term context_decl list -> T.term context_decl list -> nat -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env

  val coq_All_local_env_nth_error :
    E.context -> nat -> T.term context_decl -> 'a1 coq_All_local_env -> 'a1

  val coq_All_local_env_cst :
    E.context -> ('a1 coq_All_local_env, (T.term context_decl, 'a1) coq_All)
    iffT

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil :
    T.term context_decl list -> 'a1 coq_All_local_rel

  val coq_All_local_rel_snoc :
    T.term context_decl list -> E.context -> T.term context_decl -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    T.term context_decl list -> E.context -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    T.term context_decl list -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_tip :
    T.term context_decl list -> T.term context_decl list -> T.term
    context_decl -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1

  val coq_All_local_rel_ind1 :
    T.term context_decl list -> 'a2 -> (T.term context_decl list -> T.term
    context_decl -> 'a2 -> 'a1 -> 'a2) -> E.context -> 'a1 coq_All_local_rel
    -> 'a2

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    T.term context_decl list -> T.term context_decl list -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_env_app_inv :
    T.term context_decl list -> T.term context_decl list -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_rel_app_inv :
    T.term context_decl list -> T.term context_decl list -> T.term
    context_decl list -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1
    coq_All_local_rel

  val coq_All_local_env_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  val coq_All_local_rel_app :
    T.term context_decl list -> E.context -> E.context -> 'a1
    coq_All_local_rel -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel

  val coq_All_local_env_prod_inv :
    E.context -> ('a1 * 'a2) coq_All_local_env -> 'a1 coq_All_local_env * 'a2
    coq_All_local_env

  val coq_All_local_env_lift_prod_inv :
    E.context -> ('a1 * 'a2) lift_typing0 coq_All_local_env -> 'a1
    lift_typing0 coq_All_local_env * 'a2 lift_typing0 coq_All_local_env

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'cproperty * 'sproperty

  val coq_All_local_env_over_sorting_rect :
    'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4 -> 'a5) -> (E.context -> aname
    -> T.term -> T.term -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1,
    'a2, 'a3, 'a4) coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2)
    lift_sorting -> 'a3 -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5

  val coq_All_local_env_over_sorting_rec :
    'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4 -> 'a5) -> (E.context -> aname
    -> T.term -> T.term -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1,
    'a2, 'a3, 'a4) coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2)
    lift_sorting -> 'a3 -> 'a4 -> 'a5) -> E.context -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty)
    coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_sig_pack :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_sorting -> (E.context * ('a1, 'a2)
    lift_sorting coq_All_local_env) * ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_Signature :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> (('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_sorting, E.context * ('a1, 'a2)
    lift_sorting coq_All_local_env, ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing, 'property, 'property) coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_2 :
    E.context -> ('a1, 'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_sorting -> ('a1 * 'a3, 'a2 * 'a4)
    lift_sorting coq_All_local_env

  type ('typing, 'p) on_wf_local_decl = __

  val nth_error_All_local_env_over :
    T.term context_decl list -> nat -> T.term context_decl -> 'a1
    lift_typing0 coq_All_local_env -> ('a1, 'a2) coq_All_local_env_over ->
    ('a1, 'a2) coq_All_local_env_over * ('a1, 'a2) on_wf_local_decl

  val coq_All_local_env_over_2 :
    E.context -> 'a1 lift_typing0 coq_All_local_env -> ('a1, 'a2)
    coq_All_local_env_over -> ('a1, 'a2) lift_typing_conj coq_All_local_env

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
    E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
    T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
    T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.context -> 'a2 -> (aname -> T.term -> T.term -> T.term list ->
    E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> T.term ->
    T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
    T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term
    list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.context -> T.term list -> E.context -> ('a1 ctx_inst, T.term
    list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.context -> ((T.term list * E.context) * 'a1 ctx_inst)
    coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.context -> T.term list -> E.context -> __ list -> (__, __ ctx_inst)
    sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1) -> (__, __
    ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.context -> T.term list -> E.context -> 'a1 ctx_inst -> (T.term ->
    T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val option_default_size : ('a1 -> 'a2 -> size) -> 'a1 option -> __ -> size

  val lift_sorting_size_gen :
    (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size) ->
    nat -> E.judgment -> ('a1, 'a2) lift_sorting -> size

  val lift_sorting_size_gen_impl :
    (T.term -> T.term -> 'a1 -> size) -> (T.term -> Sort.t -> 'a2 -> size) ->
    E.judgment -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 -> __
    -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val on_def_type_size_gen :
    (E.context -> T.term -> Sort.t -> 'a2 -> size) -> nat -> E.context ->
    T.term def -> ('a1, 'a2) lift_sorting on_def_type -> size

  val on_def_body_size_gen :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> nat -> T.term context_decl list -> T.term
    context_decl list -> T.term def -> ('a1, 'a2) lift_sorting on_def_body ->
    size

  val lift_sorting_size_impl :
    E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> (T.term -> Sort.t ->
    'a2 -> size) -> ('a1, 'a2) lift_sorting -> (T.term -> T.term -> 'a1 -> __
    -> 'a3) -> (T.term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val lift_typing_size_impl :
    E.judgment -> (T.term -> T.term -> 'a1 -> nat) -> 'a1 lift_typing0 ->
    (T.term -> T.term -> 'a1 -> __ -> 'a2) -> 'a2 lift_typing0

  val coq_All_local_env_size_gen :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> size -> E.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> size

  val coq_All_local_env_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context -> ('a1, 'a1)
    lift_sorting coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> E.context -> E.context
    -> 'a1 lift_typing0 coq_All_local_rel -> size

  val coq_All_local_env_sorting_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> E.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.context -> T.term -> T.term -> 'a1 -> size) -> (E.context -> T.term ->
    Sort.t -> 'a2 -> size) -> T.term context_decl list -> E.context -> ('a1,
    'a2) lift_sorting coq_All_local_rel -> size
 end) ->
 functor (C:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (L:sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body * E.one_inductive_body) option

  val lookup_inductive :
    E.global_env -> inductive ->
    (E.mutual_inductive_body * E.one_inductive_body) option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body)
    option

  val lookup_constructor :
    E.global_env -> inductive -> nat ->
    ((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body)
    option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body) * E.projection_body)
    option

  val lookup_projection :
    E.global_env -> projection ->
    (((E.mutual_inductive_body * E.one_inductive_body) * E.constructor_body) * E.projection_body)
    option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> bool

  val wf_sort_dec : E.global_env_ext -> Sort.t -> bool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end) ->
 struct
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  (** val univs_ext_constraints :
      ConstraintSet.t -> universes_decl -> ConstraintSet.t **)

  let univs_ext_constraints univs _UU03c6_ =
    ConstraintSet.union (constraints_of_udecl _UU03c6_) univs

  (** val ind_realargs : E.one_inductive_body -> nat **)

  let ind_realargs o =
    match TU.destArity [] (E.ind_type o) with
    | Some p -> let (ctx, _) = p in length (E.smash_context [] ctx)
    | None -> O

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  (** val positive_cstr_arg_rect :
      E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
      'a1) -> (T.term context_decl list -> T.term list -> nat ->
      E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
      positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname
      -> T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr_arg -> 'a1 **)

  let rec positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_ _ = function
  | Coq_pos_arg_closed ty -> f _UU0393_ ty __
  | Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
  | Coq_pos_arg_let (na, b, ty, ty', p0) ->
    f1 _UU0393_ na b ty ty' p0
      (positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_
        (T.subst (b :: []) O ty') p0)
  | Coq_pos_arg_ass (na, ty, ty', p0) ->
    f2 _UU0393_ na ty ty' __ p0
      (positive_cstr_arg_rect mdecl f f0 f1 f2 ((E.vass na ty) :: _UU0393_)
        ty' p0)

  (** val positive_cstr_arg_rec :
      E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
      'a1) -> (T.term context_decl list -> T.term list -> nat ->
      E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
      positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname
      -> T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr_arg -> 'a1 **)

  let rec positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_ _ = function
  | Coq_pos_arg_closed ty -> f _UU0393_ ty __
  | Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
  | Coq_pos_arg_let (na, b, ty, ty', p0) ->
    f1 _UU0393_ na b ty ty' p0
      (positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_
        (T.subst (b :: []) O ty') p0)
  | Coq_pos_arg_ass (na, ty, ty', p0) ->
    f2 _UU0393_ na ty ty' __ p0
      (positive_cstr_arg_rec mdecl f f0 f1 f2 ((E.vass na ty) :: _UU0393_)
        ty' p0)

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  (** val positive_cstr_rect :
      E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
      list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
      aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term ->
      positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr -> 'a1 **)

  let rec positive_cstr_rect mdecl i f f0 f1 _UU0393_ _ = function
  | Coq_pos_concl (l, x) -> f _UU0393_ l x
  | Coq_pos_let (na, b, ty, ty', p0) ->
    f0 _UU0393_ na b ty ty' p0
      (positive_cstr_rect mdecl i f f0 f1 _UU0393_ (T.subst (b :: []) O ty')
        p0)
  | Coq_pos_ass (na, ty, ty', p0, p1) ->
    f1 _UU0393_ na ty ty' p0 p1
      (positive_cstr_rect mdecl i f f0 f1 ((E.vass na ty) :: _UU0393_) ty' p1)

  (** val positive_cstr_rec :
      E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
      list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
      aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term ->
      positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr -> 'a1 **)

  let rec positive_cstr_rec mdecl i f f0 f1 _UU0393_ _ = function
  | Coq_pos_concl (l, x) -> f _UU0393_ l x
  | Coq_pos_let (na, b, ty, ty', p0) ->
    f0 _UU0393_ na b ty ty' p0
      (positive_cstr_rec mdecl i f f0 f1 _UU0393_ (T.subst (b :: []) O ty')
        p0)
  | Coq_pos_ass (na, ty, ty', p0, p1) ->
    f1 _UU0393_ na ty ty' p0 p1
      (positive_cstr_rec mdecl i f f0 f1 ((E.vass na ty) :: _UU0393_) ty' p1)

  (** val lift_level : nat -> Level.t_ -> Level.t_ **)

  let lift_level n l = match l with
  | Level.Coq_lvar k -> Level.Coq_lvar (add n k)
  | _ -> l

  (** val lift_instance : nat -> Level.t_ list -> Level.t_ list **)

  let lift_instance n l =
    map (lift_level n) l

  (** val lift_constraint :
      nat -> ((Level.t * ConstraintType.t) * Level.t) ->
      (Level.t_ * ConstraintType.t) * Level.t_ **)

  let lift_constraint n = function
  | (p, l') -> let (l, r) = p in (((lift_level n l), r), (lift_level n l'))

  (** val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t **)

  let lift_constraints n cstrs =
    ConstraintSet.fold (fun elt acc ->
      ConstraintSet.add (lift_constraint n elt) acc) cstrs ConstraintSet.empty

  (** val level_var_instance : nat -> name list -> Level.t_ list **)

  let level_var_instance n inst =
    mapi_rec (fun i _ -> Level.Coq_lvar i) inst n

  (** val variance_cstrs :
      Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t **)

  let rec variance_cstrs v u u' =
    match v with
    | [] -> ConstraintSet.empty
    | v0 :: vs ->
      (match u with
       | [] -> ConstraintSet.empty
       | u0 :: us ->
         (match u' with
          | [] -> ConstraintSet.empty
          | u'0 :: us' ->
            (match v0 with
             | Variance.Irrelevant -> variance_cstrs vs us us'
             | Variance.Covariant ->
               ConstraintSet.add ((u0, (ConstraintType.Le Z0)), u'0)
                 (variance_cstrs vs us us')
             | Variance.Invariant ->
               ConstraintSet.add ((u0, ConstraintType.Eq), u'0)
                 (variance_cstrs vs us us'))))

  (** val variance_universes :
      universes_decl -> Variance.t list -> ((universes_decl * Level.t_
      list) * Level.t_ list) option **)

  let variance_universes univs v =
    match univs with
    | Monomorphic_ctx -> None
    | Polymorphic_ctx auctx ->
      let (inst, cstrs) = auctx in
      let u' = level_var_instance O inst in
      let u = lift_instance (length inst) u' in
      let cstrs0 =
        ConstraintSet.union cstrs (lift_constraints (length inst) cstrs)
      in
      let cstrv = variance_cstrs v u u' in
      let auctx' = ((app inst inst), (ConstraintSet.union cstrs0 cstrv)) in
      Some (((Polymorphic_ctx auctx'), u), u')

  (** val ind_arities :
      E.mutual_inductive_body -> T.term context_decl list **)

  let ind_arities mdecl =
    E.arities_context (E.ind_bodies mdecl)

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  (** val cstr_concl_head :
      E.mutual_inductive_body -> nat -> E.constructor_body -> T.term **)

  let cstr_concl_head mdecl i cdecl =
    T.tRel
      (add
        (add (sub (length (E.ind_bodies mdecl)) (S i))
          (length (E.ind_params mdecl))) (length (E.cstr_args cdecl)))

  (** val cstr_concl :
      E.mutual_inductive_body -> nat -> E.constructor_body -> T.term **)

  let cstr_concl mdecl i cdecl =
    T.mkApps (cstr_concl_head mdecl i cdecl)
      (app
        (E.to_extended_list_k (E.ind_params mdecl)
          (length (E.cstr_args cdecl))) (E.cstr_indices cdecl))

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  (** val on_ctype :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ('a1, 'a2) on_constructor -> 'a2 on_type **)

  let on_ctype _ _ _ _ _ _ _ _ o =
    o.on_ctype

  (** val on_cargs :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx **)

  let on_cargs _ _ _ _ _ _ _ _ o =
    o.on_cargs

  (** val on_cindices :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst **)

  let on_cindices _ _ _ _ _ _ _ _ o =
    o.on_cindices

  (** val on_ctype_positive :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ('a1, 'a2) on_constructor -> positive_cstr **)

  let on_ctype_positive _ _ _ _ _ _ _ _ o =
    o.on_ctype_positive

  (** val on_ctype_variance :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
      cstr_respects_variance **)

  let on_ctype_variance _ _ _ _ _ _ _ _ o v =
    o.on_ctype_variance v __

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Sort.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  (** val on_projs :
      E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
      E.context -> E.constructor_body -> on_projections ->
      (E.projection_body, __) coq_Alli **)

  let on_projs _ _ _ _ _ _ o =
    o

  type constructor_univs = Sort.t list

  (** val elim_sort_prop_ind :
      constructor_univs list -> allowed_eliminations **)

  let elim_sort_prop_ind = function
  | [] -> IntoAny
  | s :: l ->
    (match l with
     | [] ->
       if forallb Sort.is_propositional s then IntoAny else IntoPropSProp
     | _ :: _ -> IntoPropSProp)

  (** val elim_sort_sprop_ind :
      constructor_univs list -> allowed_eliminations **)

  let elim_sort_sprop_ind = function
  | [] -> IntoAny
  | _ :: _ -> IntoSProp

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  (** val onArity :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type **)

  let onArity _ _ _ _ _ _ o =
    o.onArity

  (** val ind_cunivs :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
      constructor_univs list **)

  let ind_cunivs _ _ _ _ _ _ o =
    o.ind_cunivs

  (** val onConstructors :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
      on_constructors **)

  let onConstructors _ _ _ _ _ _ o =
    o.onConstructors

  (** val onProjections :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

  let onProjections _ _ _ _ _ _ o =
    o.onProjections

  (** val ind_sorts :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
      check_ind_sorts **)

  let ind_sorts _ _ _ _ _ _ o =
    o.ind_sorts

  (** val onIndices :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

  let onIndices _ _ _ _ _ _ o =
    o.onIndices

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  (** val onInductives :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
      on_ind_body) coq_Alli **)

  let onInductives _ _ _ _ o =
    o.onInductives

  (** val onParams :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> 'a2 on_context **)

  let onParams _ _ _ _ o =
    o.onParams

  (** val onVariance :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> on_variance **)

  let onVariance _ _ _ _ o =
    o.onVariance

  type 'p on_constant_decl = 'p

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  (** val udecl :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls_data -> universes_decl **)

  let udecl _ _ _ _ _ d _ =
    L.universes_decl_of_decl d

  (** val on_global_decl_d :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls_data -> ('a1, 'a2) on_global_decl **)

  let on_global_decl_d _ _ _ _ _ _ o =
    o

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  (** val on_global_decls_rect :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
      E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

  let rec on_global_decls_rect cf univs retro f f0 _ = function
  | Coq_globenv_nil -> f
  | Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
    f0 _UU03a3_ kn d o0
      (on_global_decls_rect cf univs retro f f0 _UU03a3_ o0) o1

  (** val on_global_decls_rec :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
      E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

  let rec on_global_decls_rec cf univs retro f f0 _ = function
  | Coq_globenv_nil -> f
  | Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
    f0 _UU03a3_ kn d o0 (on_global_decls_rec cf univs retro f f0 _UU03a3_ o0)
      o1

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  (** val on_global_decls_sig_pack :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> ('a1, 'a2) on_global_decls ->
      E.global_declarations * ('a1, 'a2) on_global_decls **)

  let on_global_decls_sig_pack _ _ _ x on_global_decls_var =
    x,on_global_decls_var

  (** val on_global_decls_Signature :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> (('a1, 'a2) on_global_decls,
      E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature **)

  let on_global_decls_Signature =
    on_global_decls_sig_pack

  type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

  type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

  (** val on_global_env_ext_empty_ext :
      checker_flags -> E.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a2)
      on_global_env_ext **)

  let on_global_env_ext_empty_ext _ _ h =
    (h, __)

  (** val type_local_ctx_impl_gen :
      E.global_env_ext -> E.context -> E.context -> Sort.t -> __ list -> (__,
      __ type_local_ctx) sigT -> (E.context -> E.judgment -> (__, __) coq_All
      -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1 type_local_ctx **)

  let rec type_local_ctx_impl_gen _UU03a3_ _UU0393_ _UU0394_ u args hexists hP hPQ =
    match _UU0394_ with
    | [] -> Obj.magic __ _UU0393_ hPQ hP hexists
    | y :: l ->
      let iH_UU0394_ = fun h1 _UU0393_0 h2 h ->
        type_local_ctx_impl_gen _UU03a3_ _UU0393_0 l u args (Coq_existT (__,
          h2)) h1 h
      in
      let iH_UU0394_0 = fun _UU0393_0 h2 -> iH_UU0394_ hP _UU0393_0 h2 in
      let Coq_existT (_, y0) = hexists in
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let (t1, _) = Obj.magic y0 in
         Obj.magic
           ((iH_UU0394_0 _UU0393_ t1
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let (t2, _) = x in t2))),
           (hP (app_context _UU0393_ l) { j_term = (Some t0); j_typ =
             decl_type0; j_univ = None }
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let (_, x0) = x in x0))))
       | None ->
         let (t0, _) = Obj.magic y0 in
         Obj.magic
           ((iH_UU0394_0 _UU0393_ t0
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let (t1, _) = x in t1))),
           (hP (app_context _UU0393_ l) { j_term = None; j_typ = decl_type0;
             j_univ = (Some u) }
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let (_, x0) = x in x0)))))

  (** val type_local_ctx_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      Sort.t -> 'a1 type_local_ctx -> (E.context -> E.judgment -> 'a1 -> 'a2)
      -> 'a2 type_local_ctx **)

  let type_local_ctx_impl _ _ _UU0393_ _UU0394_ u hP =
    let rec f = function
    | [] -> Obj.magic __
    | y :: l0 ->
      (fun _UU0393_0 _ hP0 x ->
        let { decl_name = _; decl_body = decl_body0; decl_type =
          decl_type0 } = y
        in
        (match decl_body0 with
         | Some t0 ->
           let (t1, p) = Obj.magic hP0 in
           Obj.magic ((f l0 _UU0393_0 __ t1 x),
             (x (app_context _UU0393_0 l0) { j_term = (Some t0); j_typ =
               decl_type0; j_univ = None } p))
         | None ->
           let (t0, p) = Obj.magic hP0 in
           Obj.magic ((f l0 _UU0393_0 __ t0 x),
             (x (app_context _UU0393_0 l0) { j_term = None; j_typ =
               decl_type0; j_univ = (Some u) } p))))
    in f _UU0394_ _UU0393_ __ hP

  (** val sorts_local_ctx_impl_gen :
      E.global_env_ext -> E.context -> E.context -> Sort.t list -> __ list ->
      (__, __ sorts_local_ctx) sigT -> (E.context -> E.judgment -> (__, __)
      coq_All -> 'a1) -> (__, __ sorts_local_ctx) coq_All -> 'a1
      sorts_local_ctx **)

  let rec sorts_local_ctx_impl_gen _UU03a3_ _UU0393_ _UU0394_ u args hexists hP hPQ =
    match _UU0394_ with
    | [] -> let Coq_existT (_, y) = hexists in y
    | y :: l ->
      let iH_UU0394_ = fun h1 _UU0393_0 u0 h2 h ->
        sorts_local_ctx_impl_gen _UU03a3_ _UU0393_0 l u0 args (Coq_existT
          (__, h2)) h1 h
      in
      let iH_UU0394_0 = fun _UU0393_0 u0 h2 -> iH_UU0394_ hP _UU0393_0 u0 h2
      in
      let Coq_existT (_, y0) = hexists in
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let (s, _) = Obj.magic y0 in
         Obj.magic
           ((iH_UU0394_0 _UU0393_ u s
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let (s0, _) = x in s0))),
           (hP (app_context _UU0393_ l) { j_term = (Some t0); j_typ =
             decl_type0; j_univ = None }
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let (_, x0) = x in x0))))
       | None ->
         (match u with
          | [] -> Obj.magic __ hPQ y0
          | t0 :: l0 ->
            let (s, _) = Obj.magic y0 in
            Obj.magic
              ((iH_UU0394_0 _UU0393_ l0 s
                 (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                   let (s0, _) = x in s0))),
              (hP (app_context _UU0393_ l) { j_term = None; j_typ =
                decl_type0; j_univ = (Some t0) }
                (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                  let (_, x0) = x in x0))))))

  (** val sorts_local_ctx_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      Sort.t list -> 'a1 sorts_local_ctx -> (E.context -> E.judgment -> 'a1
      -> 'a2) -> 'a2 sorts_local_ctx **)

  let rec sorts_local_ctx_impl _UU03a3_ _UU03a3_' _UU0393_ _UU0394_ u hP hPQ =
    match _UU0394_ with
    | [] -> hP
    | y :: l ->
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let (s, p) = Obj.magic hP in
         Obj.magic
           ((sorts_local_ctx_impl _UU03a3_ _UU03a3_' _UU0393_ l u s hPQ),
           (hPQ (app_context _UU0393_ l) { j_term = (Some t0); j_typ =
             decl_type0; j_univ = None } p))
       | None ->
         (match u with
          | [] -> Obj.magic __ hP
          | t0 :: l0 ->
            let (s, p) = Obj.magic hP in
            Obj.magic
              ((sorts_local_ctx_impl _UU03a3_ _UU03a3_' _UU0393_ l l0 s hPQ),
              (hPQ (app_context _UU0393_ l) { j_term = None; j_typ =
                decl_type0; j_univ = (Some t0) } p))))

  (** val cstr_respects_variance_impl_gen :
      E.global_env -> E.mutual_inductive_body -> Variance.t list ->
      E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT
      -> __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
      cstr_respects_variance **)

  let cstr_respects_variance_impl_gen _ mdecl v cs args =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hexists hPQ hP ->
         let (p0, l) = p in
         let (_, l0) = p0 in
         let hP0 = coq_All_prod_inv args (Obj.magic hP) in
         let (a, a0) = hP0 in
         let hP1 =
           coq_All_All2_fold_swap_sum args
             (subst_instance E.subst_instance_context l0
               (E.expand_lets_ctx (E.ind_params mdecl)
                 (E.smash_context [] (E.cstr_args cs))))
             (subst_instance E.subst_instance_context l
               (E.expand_lets_ctx (E.ind_params mdecl)
                 (E.smash_context [] (E.cstr_args cs)))) a
         in
         let hP2 =
           coq_All_All2_swap_sum args
             (map (fun x ->
               subst_instance T.subst_instance_constr l0
                 (E.expand_lets
                   (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs))
             (map (fun x ->
               subst_instance T.subst_instance_constr l
                 (E.expand_lets
                   (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs)) a0
         in
         (match args with
          | [] ->
            let hPQ0 = fun _UU0393_ t0 t1 pb ->
              Obj.magic hPQ _UU0393_ t0 t1 pb All_nil
            in
            let Coq_existT (_, p1) = hexists in
            let (a1, a2) = Obj.magic p1 in
            Obj.magic
              ((coq_All2_fold_impl
                 (subst_instance E.subst_instance_context l0
                   (E.expand_lets_ctx (E.ind_params mdecl)
                     (E.smash_context [] (E.cstr_args cs))))
                 (subst_instance E.subst_instance_context l
                   (E.expand_lets_ctx (E.ind_params mdecl)
                     (E.smash_context [] (E.cstr_args cs)))) a1
                 (fun _UU0393_ _ d d' ->
                 C.coq_All_decls_alpha_pb_impl Cumul d d' (fun pb t0 t' _ ->
                   hPQ0
                     (app_context
                       (subst_instance E.subst_instance_context l0
                         (app_context (ind_arities mdecl)
                           (E.smash_context [] (E.ind_params mdecl))))
                       _UU0393_) t0 t' pb))),
              (coq_All2_impl
                (map (fun x ->
                  subst_instance T.subst_instance_constr l0
                    (E.expand_lets
                      (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
                  (E.cstr_indices cs))
                (map (fun x ->
                  subst_instance T.subst_instance_constr l
                    (E.expand_lets
                      (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
                  (E.cstr_indices cs)) a2 (fun x y _ ->
                hPQ0
                  (subst_instance E.subst_instance_context l0
                    (app_context (ind_arities mdecl)
                      (E.smash_context []
                        (app_context (E.ind_params mdecl) (E.cstr_args cs)))))
                  x y Conv)))
          | _ :: l1 ->
            (match hP1 with
             | Coq_inl _ -> assert false (* absurd case *)
             | Coq_inr a1 ->
               (match hP2 with
                | Coq_inl _ -> assert false (* absurd case *)
                | Coq_inr a2 ->
                  Obj.magic
                    ((coq_All2_fold_impl
                       (subst_instance E.subst_instance_context l0
                         (E.expand_lets_ctx (E.ind_params mdecl)
                           (E.smash_context [] (E.cstr_args cs))))
                       (subst_instance E.subst_instance_context l
                         (E.expand_lets_ctx (E.ind_params mdecl)
                           (E.smash_context [] (E.cstr_args cs)))) a1
                       (fun _UU0393_ _ _ _ x ->
                       match x with
                       | All_nil -> assert false (* absurd case *)
                       | All_cons (_, _, x0, x1) ->
                         (match x0 with
                          | C.Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
                            C.Coq_all_decls_alpha_vass (na, na', t0, t',
                              (Obj.magic hPQ
                                (app_context
                                  (subst_instance E.subst_instance_context l0
                                    (app_context (ind_arities mdecl)
                                      (E.smash_context []
                                        (E.ind_params mdecl)))) _UU0393_) t0
                                t' Cumul (All_cons (__, l1, eqt,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _,
                                                                eqt0) ->
                                    eqt0
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, _, _) ->
                                    assert false (* absurd case *)))))))
                          | C.Coq_all_decls_alpha_vdef (na, na', b, t0, b',
                                                        t', eqb, eqt) ->
                            C.Coq_all_decls_alpha_vdef (na, na', b, t0, b',
                              t',
                              (Obj.magic hPQ
                                (app_context
                                  (subst_instance E.subst_instance_context l0
                                    (app_context (ind_arities mdecl)
                                      (E.smash_context []
                                        (E.ind_params mdecl)))) _UU0393_) b
                                b' Conv (All_cons (__, l1, eqb,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _, _) ->
                                    assert false (* absurd case *)
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, eqb0, _) ->
                                    eqb0))))),
                              (Obj.magic hPQ
                                (app_context
                                  (subst_instance E.subst_instance_context l0
                                    (app_context (ind_arities mdecl)
                                      (E.smash_context []
                                        (E.ind_params mdecl)))) _UU0393_) t0
                                t' Cumul (All_cons (__, l1, eqt,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _, _) ->
                                    assert false (* absurd case *)
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, _, eqt0) ->
                                    eqt0))))))))),
                    (coq_All2_impl
                      (map (fun x ->
                        subst_instance T.subst_instance_constr l0
                          (E.expand_lets
                            (app_context (E.ind_params mdecl)
                              (E.cstr_args cs)) x)) (E.cstr_indices cs))
                      (map (fun x ->
                        subst_instance T.subst_instance_constr l
                          (E.expand_lets
                            (app_context (E.ind_params mdecl)
                              (E.cstr_args cs)) x)) (E.cstr_indices cs)) a2
                      (fun x y x0 ->
                      Obj.magic hPQ
                        (subst_instance E.subst_instance_context l0
                          (app_context (ind_arities mdecl)
                            (E.smash_context []
                              (app_context (E.ind_params mdecl)
                                (E.cstr_args cs))))) x y Conv x0)))))))
     | None -> Obj.magic __)

  (** val cstr_respects_variance_impl :
      E.global_env -> E.global_env -> E.mutual_inductive_body -> Variance.t
      list -> E.constructor_body -> __ -> 'a1 cstr_respects_variance -> 'a2
      cstr_respects_variance **)

  let cstr_respects_variance_impl _ _ mdecl v cs =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hPQ __top_assumption_ ->
         let (p0, l) = p in
         let (_, l0) = p0 in
         let _evar_0_ = fun hP1 hP2 ->
           ((coq_All2_fold_impl
              (subst_instance E.subst_instance_context l0
                (E.expand_lets_ctx (E.ind_params mdecl)
                  (E.smash_context [] (E.cstr_args cs))))
              (subst_instance E.subst_instance_context l
                (E.expand_lets_ctx (E.ind_params mdecl)
                  (E.smash_context [] (E.cstr_args cs)))) hP1
              (fun _UU0393_ _ d d' ->
              C.coq_All_decls_alpha_pb_impl Cumul d d' (fun pb t0 t' x ->
                Obj.magic hPQ
                  (app_context
                    (subst_instance E.subst_instance_context l0
                      (app_context (ind_arities mdecl)
                        (E.smash_context [] (E.ind_params mdecl)))) _UU0393_)
                  t0 t' pb x))),
           (coq_All2_impl
             (map (fun x ->
               subst_instance T.subst_instance_constr l0
                 (E.expand_lets
                   (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs))
             (map (fun x ->
               subst_instance T.subst_instance_constr l
                 (E.expand_lets
                   (app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs)) hP2 (fun x y x0 ->
             Obj.magic hPQ
               (subst_instance E.subst_instance_context l0
                 (app_context (ind_arities mdecl)
                   (E.smash_context []
                     (app_context (E.ind_params mdecl) (E.cstr_args cs))))) x
               y Conv x0)))
         in
         let (a, b) = Obj.magic __top_assumption_ in Obj.magic _evar_0_ a b)
     | None -> Obj.magic __)

  (** val on_constructor_impl_config_gen :
      E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Sort.t list
      -> ((checker_flags * __) * __) list -> checker_flags ->
      ((checker_flags * __) * __, __) sigT -> (E.context -> E.judgment ->
      ((checker_flags * __) * __, __) coq_All -> 'a2) -> (universes_decl ->
      E.context -> T.term -> T.term -> conv_pb -> ((checker_flags * __) * __,
      __) coq_All -> 'a1) -> ((checker_flags * __) * __, __) coq_All -> ('a1,
      'a2) on_constructor **)

  let on_constructor_impl_config_gen _UU03a3_ mdecl _ _ ind_indices0 cdecl cunivs args _ hexists h1 h2 hargs =
    let Coq_existT (_, y) = hexists in
    let (_, o) = Obj.magic y in
    let { on_ctype = _; on_cargs = on_cargs0; on_cindices = on_cindices0;
      on_ctype_positive = on_ctype_positive0; on_ctype_variance =
      on_ctype_variance0 } = o
    in
    { on_ctype =
    (h1 (E.arities_context (E.ind_bodies mdecl)) { j_term = None; j_typ =
      (E.cstr_type cdecl); j_univ = None }
      (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_ctype)));
    on_cargs =
    (sorts_local_ctx_impl_gen _UU03a3_
      (app_context (E.arities_context (E.ind_bodies mdecl))
        (E.ind_params mdecl)) (E.cstr_args cdecl) cunivs
      (map (Obj.magic __) args) (Coq_existT (__, on_cargs0))
      (fun _UU0393_ j x ->
      h1 _UU0393_ j
        (let (_, x0) = coq_All_eta3 args in
         x0 (coq_All_map_inv (Obj.magic __) args x)))
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_cargs))));
    on_cindices =
    (ET.ctx_inst_impl_gen
      (app_context
        (app_context (E.arities_context (E.ind_bodies mdecl))
          (E.ind_params mdecl)) (E.cstr_args cdecl)) (E.cstr_indices cdecl)
      (List0.rev (E.lift_context (length (E.cstr_args cdecl)) O ind_indices0))
      (map (Obj.magic __) args) (Coq_existT (__, on_cindices0))
      (fun t0 t1 x ->
      h1
        (app_context
          (app_context (E.arities_context (E.ind_bodies mdecl))
            (E.ind_params mdecl)) (E.cstr_args cdecl)) { j_term = (Some t0);
        j_typ = t1; j_univ = None }
        (let (_, x0) = coq_All_eta3 args in
         x0 (coq_All_map_inv (Obj.magic __) args x)))
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_cindices))));
    on_ctype_positive = on_ctype_positive0; on_ctype_variance = (fun _v_ _ ->
    let on_ctype_variance1 = on_ctype_variance0 _v_ __ in
    cstr_respects_variance_impl_gen (E.fst_ctx _UU03a3_) mdecl _v_ cdecl
      (map (Obj.magic __) args) (Coq_existT (__, on_ctype_variance1))
      (let o0 = variance_universes (E.ind_universes mdecl) _v_ in
       match o0 with
       | Some p ->
         let (p0, _) = p in
         let (u, _) = p0 in
         Obj.magic (fun _UU0393_ t0 t1 pb x ->
           h2 u _UU0393_ t0 t1 pb
             (let (_, x0) = coq_All_eta3 args in
              x0 (coq_All_map_inv (Obj.magic __) args x)))
       | None -> Obj.magic __ __)
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x ->
          x.on_ctype_variance _v_ __)))) }

  (** val on_constructors_impl_config_gen :
      E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body list -> Sort.t
      list list -> ((checker_flags * __) * __) list -> checker_flags ->
      ((checker_flags * __) * __, __) sigT -> ((checker_flags * __) * __, __)
      coq_All -> (E.context -> E.judgment -> ((checker_flags * __) * __, __)
      coq_All -> 'a2) -> (universes_decl -> E.context -> T.term -> T.term ->
      conv_pb -> ((checker_flags * __) * __, __) coq_All -> 'a1) ->
      ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructors **)

  let on_constructors_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0 cdecl cunivs args cf hexists hargsconfig h1 h2 hargs =
    let Coq_existT (x, y) = hexists in
    let (p, _) = x in
    let (c, _) = p in
    let (_, o) = Obj.magic y in
    (match args with
     | [] ->
       coq_All2_impl cdecl cunivs o (fun x0 y0 x1 ->
         on_constructor_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0
           x0 y0 [] cf (Coq_existT (((c, __), __), (Obj.magic (__, x1)))) h1
           h2 All_nil)
     | p0 :: l ->
       let x0 = fun ls -> let (x0, _) = coq_All_eta3 ls in x0 in
       let hargs0 = x0 (p0 :: l) hargs in
       let hargs1 = coq_All_All2_swap (p0 :: l) cdecl cunivs hargs0 in
       coq_All2_impl cdecl cunivs hargs1 (fun _x_ _y_ hargs' ->
         on_constructor_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0
           _x_ _y_ (p0 :: l) cf
           (let (p1, _) = p0 in
            let (c0, _) = p1 in
            (match hargs' with
             | All_nil -> assert false (* absurd case *)
             | All_cons (_, _, x1, _) ->
               (match hargsconfig with
                | All_nil -> assert false (* absurd case *)
                | All_cons (_, _, _, _) ->
                  Obj.magic (Coq_existT (((c0, __), __), (__, x1)))))) h1 h2
           (let (p1, _) = p0 in
            let (c0, _) = p1 in
            (match hargs' with
             | All_nil -> assert false (* absurd case *)
             | All_cons (_, _, x1, x2) ->
               (match hargsconfig with
                | All_nil -> assert false (* absurd case *)
                | All_cons (_, _, _, _) ->
                  Obj.magic (All_cons (((c0, __), __), l, x1,
                    (coq_All_impl l x2 (fun _ x3 -> x3)))))))))

  (** val ind_respects_variance_impl :
      E.global_env -> E.global_env -> E.mutual_inductive_body -> Variance.t
      list -> E.context -> __ -> 'a1 ind_respects_variance -> 'a2
      ind_respects_variance **)

  let ind_respects_variance_impl _ _ mdecl v cs =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hPQ hP ->
         let (p0, l) = p in
         let (_, l0) = p0 in
         Obj.magic coq_All2_fold_impl
           (subst_instance E.subst_instance_context l0
             (E.expand_lets_ctx (E.ind_params mdecl) (E.smash_context [] cs)))
           (subst_instance E.subst_instance_context l
             (E.expand_lets_ctx (E.ind_params mdecl) (E.smash_context [] cs)))
           hP (fun _UU0393_ _ _ _ x ->
           match x with
           | C.Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
             C.Coq_all_decls_alpha_vass (na, na', t0, t',
               (Obj.magic hPQ
                 (app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context [] (E.ind_params mdecl))) _UU0393_) t0
                 t' Cumul eqt))
           | C.Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
             C.Coq_all_decls_alpha_vdef (na, na', b, t0, b', t',
               (Obj.magic hPQ
                 (app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context [] (E.ind_params mdecl))) _UU0393_) b
                 b' Conv eqb),
               (Obj.magic hPQ
                 (app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context [] (E.ind_params mdecl))) _UU0393_) t0
                 t' Cumul eqt))))
     | None -> Obj.magic __)

  (** val on_variance_impl :
      E.global_env -> universes_decl -> Variance.t list option ->
      checker_flags -> checker_flags -> on_variance -> on_variance **)

  let on_variance_impl _ univs variances _ _ x =
    let _evar_0_ =
      let _evar_0_ = fun _ _ x0 ->
        let Coq_existT (x1, s) = x0 in
        let Coq_existT (x2, s0) = s in
        let Coq_existT (x3, _) = s0 in
        Coq_existT (x1, (Coq_existT (x2, (Coq_existT (x3, __)))))
      in
      let _evar_0_0 = fun _ h0 -> h0 in
      (fun cst _ x0 ->
      match variances with
      | Some a -> _evar_0_ a cst x0
      | None -> _evar_0_0 cst x0)
    in
    (match univs with
     | Monomorphic_ctx -> Obj.magic __ __ x
     | Polymorphic_ctx cst -> Obj.magic _evar_0_ cst __ x)

  (** val on_global_decl_impl_full :
      checker_flags -> checker_flags -> (E.global_env * universes_decl) ->
      (E.global_env * universes_decl) -> kername -> E.global_decl ->
      (E.context -> E.judgment -> 'a3 -> 'a4) -> (universes_decl -> E.context
      -> conv_pb -> T.term -> T.term -> 'a1 -> 'a2) -> (universes_decl ->
      Variance.t list option -> on_variance -> on_variance) -> ('a1, 'a3)
      on_global_decl -> ('a2, 'a4) on_global_decl **)

  let on_global_decl_impl_full cf1 cf2 _UU03a3_ _UU03a3_' _ d xP xcmp xv =
    match d with
    | E.ConstantDecl c ->
      Obj.magic xP [] { j_term = (E.cst_body c); j_typ = (E.cst_type c);
        j_univ = None }
    | E.InductiveDecl m ->
      (fun x ->
        let { onInductives = onInductives0; onParams = onParams0;
          onVariance = onVariance0 } = Obj.magic x
        in
        Obj.magic { onInductives =
          (coq_Alli_impl (E.ind_bodies m) O onInductives0 (fun _ x0 x1 ->
            { onArity =
            (xP [] { j_term = None; j_typ = (E.ind_type x0); j_univ = None }
              x1.onArity); ind_cunivs = x1.ind_cunivs; onConstructors =
            (let x2 = x1.onConstructors in
             coq_All2_impl (E.ind_ctors x0) x1.ind_cunivs x2 (fun x3 y x4 ->
               let { on_ctype = on_ctype0; on_cargs = on_cargs0;
                 on_cindices = on_cindices0; on_ctype_positive =
                 on_ctype_positive0; on_ctype_variance =
                 on_ctype_variance0 } = x4
               in
               { on_ctype =
               (xP (E.arities_context (E.ind_bodies m)) { j_term = None;
                 j_typ = (E.cstr_type x3); j_univ = None } on_ctype0);
               on_cargs =
               (sorts_local_ctx_impl _UU03a3_ _UU03a3_'
                 (app_context (E.arities_context (E.ind_bodies m))
                   (E.ind_params m)) (E.cstr_args x3) y on_cargs0 xP);
               on_cindices =
               (ET.ctx_inst_impl
                 (app_context
                   (app_context (E.arities_context (E.ind_bodies m))
                     (E.ind_params m)) (E.cstr_args x3)) (E.cstr_indices x3)
                 (List0.rev
                   (E.lift_context (length (E.cstr_args x3)) O
                     (E.ind_indices x0))) on_cindices0 (fun t0 t1 x5 ->
                 xP
                   (app_context
                     (app_context (E.arities_context (E.ind_bodies m))
                       (E.ind_params m)) (E.cstr_args x3)) { j_term = (Some
                   t0); j_typ = t1; j_univ = None } x5)); on_ctype_positive =
               on_ctype_positive0; on_ctype_variance = (fun v _ ->
               cstr_respects_variance_impl (E.fst_ctx _UU03a3_)
                 (E.fst_ctx _UU03a3_') m v x3
                 (let o = variance_universes (E.ind_universes m) v in
                  match o with
                  | Some p ->
                    let (p0, _) = p in
                    let (u, _) = p0 in
                    Obj.magic (fun _UU0393_ t0 t1 pb x5 ->
                      xcmp u _UU0393_ pb t0 t1 x5)
                  | None -> Obj.magic __) (on_ctype_variance0 v __)) }));
            onProjections = x1.onProjections; ind_sorts =
            (let x2 = x1.ind_sorts in
             let f = Sort.to_family (E.ind_sort x0) in
             (match f with
              | Sort.Coq_fType ->
                let (_, y) = Obj.magic x2 in
                Obj.magic (__,
                  (let b = cf2.indices_matter in
                   if b
                   then let b0 = cf1.indices_matter in
                        if b0
                        then type_local_ctx_impl _UU03a3_ _UU03a3_'
                               (E.ind_params m) (E.ind_indices x0)
                               (E.ind_sort x0) y xP
                        else let _evar_0_ = fun _ _ -> assert false
                               (* absurd case *)
                             in
                             Obj.magic _evar_0_ __ y
                   else Obj.magic __ __ y))
              | _ -> Obj.magic __ x2)); onIndices =
            (let o = E.ind_variance m in
             match o with
             | Some l ->
               ind_respects_variance_impl (E.fst_ctx _UU03a3_)
                 (E.fst_ctx _UU03a3_') m l (E.ind_indices x0)
                 (let o0 = variance_universes (E.ind_universes m) l in
                  match o0 with
                  | Some p ->
                    let (p0, _) = p in
                    let (u, _) = p0 in
                    Obj.magic (fun _UU0393_ t0 t1 pb x2 ->
                      xcmp u _UU0393_ pb t0 t1 x2)
                  | None -> Obj.magic __) x1.onIndices
             | None -> Obj.magic __ onVariance0 x1.onIndices) })); onParams =
          (ET.coq_All_local_env_impl (E.ind_params m) onParams0 xP);
          onVariance =
          (xv (E.ind_universes m) (E.ind_variance m) onVariance0) })

  (** val on_global_decl_impl_only_config :
      checker_flags -> checker_flags -> checker_flags ->
      (E.global_env * universes_decl) -> kername -> E.global_decl ->
      (E.context -> E.judgment -> ('a1, 'a3) on_global_env -> 'a3 -> 'a4) ->
      (universes_decl -> E.context -> conv_pb -> T.term -> T.term -> ('a1,
      'a3) on_global_env -> 'a1 -> 'a2) -> ('a1, 'a3) on_global_env -> ('a1,
      'a3) on_global_decl -> ('a2, 'a4) on_global_decl **)

  let on_global_decl_impl_only_config _ cf1 cf2 _UU03a3_ kn d x x0 x1 x2 =
    on_global_decl_impl_full cf1 cf2 _UU03a3_ _UU03a3_ kn d
      (fun _UU0393_ j -> x _UU0393_ j x1) (fun u0 _UU0393_ pb t0 t' ->
      x0 u0 _UU0393_ pb t0 t' x1) (fun u0 l ->
      on_variance_impl (fst _UU03a3_) u0 l cf1 cf2) x2

  (** val on_global_decl_impl_simple :
      checker_flags -> (E.global_env * universes_decl) -> kername ->
      E.global_decl -> (E.context -> E.judgment -> ('a1, 'a2) on_global_env
      -> 'a2 -> 'a3) -> ('a1, 'a2) on_global_env -> ('a1, 'a2) on_global_decl
      -> ('a1, 'a3) on_global_decl **)

  let on_global_decl_impl_simple cf _UU03a3_ kn d x =
    on_global_decl_impl_only_config cf cf cf _UU03a3_ kn d x
      (fun _ _ _ _ _ _ x1 -> x1)

  (** val on_global_env_impl_config :
      checker_flags -> checker_flags -> ((E.global_env * universes_decl) ->
      E.context -> E.judgment -> ('a1, 'a3) on_global_env -> ('a2, 'a4)
      on_global_env -> 'a3 -> 'a4) -> ((E.global_env * universes_decl) ->
      E.context -> T.term -> T.term -> conv_pb -> ('a1, 'a3) on_global_env ->
      ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> E.global_env -> ('a1, 'a3)
      on_global_env -> ('a2, 'a4) on_global_env **)

  let on_global_env_impl_config cf1 cf2 x xcmp _UU03a3_ = function
  | (_, o) ->
    (__,
      (let univs = E.universes _UU03a3_ in
       let retro = E.retroknowledge _UU03a3_ in
       let g = E.declarations _UU03a3_ in
       let rec f l iH =
         match l with
         | [] -> Coq_globenv_nil
         | y :: l0 ->
           let iH0 = (y :: l0),iH in
           let iH2 = let _,pr2 = iH0 in pr2 in
           (match iH2 with
            | Coq_globenv_nil -> assert false (* absurd case *)
            | Coq_globenv_decl (_, kn, d, o0, o1) ->
              let iHg = f l0 o0 in
              Coq_globenv_decl (l0, kn, d, iHg,
              (let udecl0 = L.universes_decl_of_decl d in
               on_global_decl_impl_only_config cf1 cf1 cf2 ({ E.universes =
                 univs; E.declarations = l0; E.retroknowledge = retro },
                 udecl0) kn d (fun _UU0393_ j x1 x2 ->
                 x ({ E.universes = univs; E.declarations = l0;
                   E.retroknowledge = retro }, udecl0) _UU0393_ j x1 (__,
                   iHg) x2) (fun u _UU0393_ pb t0 t' x1 x2 ->
                 xcmp ({ E.universes = univs; E.declarations = l0;
                   E.retroknowledge = retro }, u) _UU0393_ t0 t' pb x1 (__,
                   iHg) x2) (__, o0) o1)))
       in f g o))

  (** val on_global_env_impl :
      checker_flags -> ((E.global_env * universes_decl) -> E.context ->
      E.judgment -> ('a1, 'a2) on_global_env -> ('a1, 'a3) on_global_env ->
      'a2 -> 'a3) -> E.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
      on_global_env **)

  let on_global_env_impl cf x _UU03a3_ x0 =
    on_global_env_impl_config cf cf x (fun _ _ _ _ _ _ _ x3 -> x3) _UU03a3_ x0

  (** val lookup_on_global_env :
      checker_flags -> E.global_env -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_env -> (E.global_env_ext, ('a1, 'a2)
      on_global_env * (E.strictly_extends_decls * ('a1, 'a2) on_global_decl))
      sigT **)

  let lookup_on_global_env _ _UU03a3_ c _ x =
    let { E.universes = universes0; E.declarations = declarations0;
      E.retroknowledge = retroknowledge0 } = _UU03a3_
    in
    let (_, o) = x in
    let rec f _ = function
    | Coq_globenv_nil -> (fun _ -> assert false (* absurd case *))
    | Coq_globenv_decl (_UU03a3_0, kn, d, o1, o2) ->
      let udecl0 = L.universes_decl_of_decl d in
      let _evar_0_ = fun _ _ -> Coq_existT (({ E.universes = universes0;
        E.declarations = _UU03a3_0; E.retroknowledge = retroknowledge0 },
        udecl0), ((__, o1), ((Times3 (__, (Coq_existT (((kn, d) :: []), __)),
        __)), o2)))
      in
      let _evar_0_0 = fun _ _ ->
        let x0 = f _UU03a3_0 o1 __ in
        let Coq_existT (x1, p) = x0 in
        let (p0, p1) = p in
        let (s, o3) = p1 in
        let Times3 (_, s0, _) = s in
        Coq_existT (x1, (p0, ((Times3 (__,
        (let Coq_existT (x2, _) = s0 in Coq_existT (((kn, d) :: x2), __)),
        __)), o3)))
      in
      (match eqb_specT Kername.reflect_kername c kn with
       | ReflectT -> _evar_0_ __
       | ReflectF -> _evar_0_0 __)
    in f declarations0 o __
 end
