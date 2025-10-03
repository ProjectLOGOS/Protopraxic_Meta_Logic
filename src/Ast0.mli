open All_Forall
open BasicAst
open CRelationClasses
open Classes0
open Datatypes
open Kernames
open List0
open MCProd
open Nat0
open PeanoNat
open PrimString
open Primitive
open Signature
open Specif
open Universes0

type __ = Obj.t

type 'term predicate = { puinst : Instance.t; pparams : 'term list;
                         pcontext : aname list; preturn : 'term }

val test_predicate :
  (Instance.t -> bool) -> ('a1 -> bool) -> ('a1 -> bool) -> 'a1 predicate ->
  bool

val map_predicate :
  (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 predicate
  -> 'a2 predicate

type 'term branch = { bcontext : aname list; bbody : 'term }

val test_branch : ('a1 -> bool) -> 'a1 branch -> bool

val map_branch : ('a1 -> 'a2) -> 'a1 branch -> 'a2 branch

module Coq__1 : sig
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Sort.t
 | Coq_tCast of term * cast_kind * term
 | Coq_tProd of aname * term * term
 | Coq_tLambda of aname * term * term
 | Coq_tLetIn of aname * term * term * term
 | Coq_tApp of term * term list
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of case_info * term predicate * term * term branch list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
 | Coq_tInt of Uint63.t
 | Coq_tFloat of Float64.t
 | Coq_tString of string
 | Coq_tArray of Level.t * term list * term * term
end
include module type of struct include Coq__1 end

val mkApps : term -> term list -> term

val lift : nat -> nat -> term -> term

val subst : term list -> nat -> term -> term

val closedn : nat -> term -> bool

val noccur_between : nat -> nat -> term -> bool

val subst_instance_constr : term coq_UnivSubst

module TemplateTerm :
 sig
  type term = Coq__1.term

  val tRel : nat -> Coq__1.term

  val tSort : Sort.t -> Coq__1.term

  val tProd : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLambda : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLetIn :
    aname -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tInd : inductive -> Instance.t -> Coq__1.term

  val tProj : projection -> Coq__1.term -> Coq__1.term

  val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term

  val lift : nat -> nat -> Coq__1.term -> Coq__1.term

  val subst : Coq__1.term list -> nat -> Coq__1.term -> Coq__1.term

  val closedn : nat -> Coq__1.term -> bool

  val noccur_between : nat -> nat -> Coq__1.term -> bool

  val subst_instance_constr : Instance.t -> Coq__1.term -> Coq__1.term
 end

module Env :
 sig
  type judgment = (Sort.t, term) judgment_

  val vass : aname -> term -> term context_decl

  val vdef : aname -> term -> term -> term context_decl

  type context = term context_decl list

  val lift_decl : nat -> nat -> term context_decl -> term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : term list -> nat -> context -> context

  val subst_decl : term list -> nat -> term context_decl -> term context_decl

  val subst_telescope : term list -> nat -> context -> context

  val subst_instance_decl : term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> term context_decl -> term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> term list

  val expand_lets_k : context -> nat -> term -> term

  val expand_lets : context -> term -> term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : term list; cstr_type : term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> term list

  val cstr_type : constructor_body -> term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> term

  val map_constructor_body :
    nat -> nat -> (nat -> term -> term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> term -> term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Sort.t; ind_type : term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Sort.t

  val ind_type : one_inductive_body -> term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> term -> term) -> one_inductive_body ->
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

  type constant_body = { cst_type : term; cst_body : term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> term

  val cst_body : constant_body -> term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (term -> term) -> constant_body -> constant_body

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

  val tImpl : term -> term -> term

  val array_uctx : name list * ConstraintSet.t

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * term

  val mkLambda_or_LetIn : term context_decl -> term -> term

  val it_mkLambda_or_LetIn : context -> term -> term

  val mkProd_or_LetIn : term context_decl -> term -> term

  val it_mkProd_or_LetIn : context -> term -> term

  val reln : term list -> nat -> term context_decl list -> term list

  val to_extended_list_k : term context_decl list -> nat -> term list

  val to_extended_list : term context_decl list -> term list

  val reln_alt : nat -> context -> term list

  val arities_context : one_inductive_body list -> term context_decl list

  val map_mutual_inductive_body :
    (nat -> term -> term) -> mutual_inductive_body -> mutual_inductive_body

  val projs : inductive -> nat -> nat -> term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * term * term * 'p
  | Coq_on_vdef of aname * term * term * term * term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
    -> term -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term context_decl
    -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
    -> term -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term context_decl
    -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> (term
    context_decl * term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    term context_decl -> term context_decl -> ('a1 coq_All_decls, term
    context_decl * term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((term context_decl * term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * term * 
     term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * term * 
     term * term * term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
    'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
    -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
    'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
    -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    term context_decl -> term context_decl -> 'a1 coq_All_decls_alpha ->
    (term context_decl * term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    term context_decl -> term context_decl -> ('a1 coq_All_decls_alpha, term
    context_decl * term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((term context_decl * term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> (term ->
    term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    term context_decl -> term context_decl -> 'a1 coq_All_decls_alpha ->
    (term -> term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (term context_decl, (term context_decl, term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end

val inds : kername -> Instance.t -> Env.one_inductive_body list -> term list

val lookup_minductive_gen :
  (kername -> Env.global_decl option) -> kername -> Env.mutual_inductive_body
  option

val lookup_inductive_gen :
  (kername -> Env.global_decl option) -> inductive ->
  (Env.mutual_inductive_body * Env.one_inductive_body) option

val lookup_inductive :
  Env.global_env -> inductive ->
  (Env.mutual_inductive_body * Env.one_inductive_body) option
