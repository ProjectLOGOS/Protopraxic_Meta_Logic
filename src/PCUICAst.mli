open All_Forall
open BasicAst
open BinNums
open Byte
open CRelationClasses
open Classes0
open Datatypes
open EnvironmentTyping
open Kernames
open List0
open MCList
open MCProd
open MCReflect
open Nat0
open PCUICPrimitive
open PeanoNat
open Primitive
open Reflect
open ReflectEq
open Signature
open Specif
open Universes0
open Bytestring
open Config0

type __ = Obj.t

type 'term predicate = { pparams : 'term list; puinst : Instance.t;
                         pcontext : 'term context_decl list; preturn : 
                         'term }

val pparams : 'a1 predicate -> 'a1 list

val puinst : 'a1 predicate -> Instance.t

val pcontext : 'a1 predicate -> 'a1 context_decl list

val preturn : 'a1 predicate -> 'a1

val coq_NoConfusionPackage_predicate : 'a1 predicate coq_NoConfusionPackage

val map_predicate :
  (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1
  context_decl list -> 'a2 context_decl list) -> 'a1 predicate -> 'a2
  predicate

val shiftf : (nat -> 'a1 -> 'a2) -> nat -> nat -> 'a1 -> 'a2

val map_predicate_k :
  (Instance.t -> Instance.t) -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 predicate
  -> 'a1 predicate

val test_predicate :
  (Instance.t -> bool) -> ('a1 -> bool) -> 'a1 predicate -> bool

val test_predicate_k :
  (Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate -> bool

val test_predicate_ku :
  (nat -> Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate
  -> bool

type 'term branch = { bcontext : 'term context_decl list; bbody : 'term }

val bcontext : 'a1 branch -> 'a1 context_decl list

val bbody : 'a1 branch -> 'a1

val coq_NoConfusionPackage_branch : 'a1 branch coq_NoConfusionPackage

val string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

val pretty_string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

val test_branch : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 branch -> bool

val test_branch_k :
  'a1 predicate -> (nat -> 'a1 -> bool) -> nat -> 'a1 branch -> bool

val map_branch :
  ('a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list) -> 'a1
  branch -> 'a2 branch

val map_branches :
  ('a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list) -> 'a1
  branch list -> 'a2 branch list

val map_branch_k :
  (nat -> 'a1 -> 'a2) -> ('a1 context_decl list -> 'a2 context_decl list) ->
  nat -> 'a1 branch -> 'a2 branch

module Coq__1 : sig
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Sort.t
 | Coq_tProd of aname * term * term
 | Coq_tLambda of aname * term * term
 | Coq_tLetIn of aname * term * term * term
 | Coq_tApp of term * term
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of case_info * term predicate * term * term branch list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
 | Coq_tPrim of term prim_val
end
include module type of struct include Coq__1 end

val term_rect :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Sort.t ->
  'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term ->
  'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term
  -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername ->
  Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive -> nat
  -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1 ->
  term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
  mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
  prim_val -> 'a1) -> term -> 'a1

val term_rec :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Sort.t ->
  'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term ->
  'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term
  -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername ->
  Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive -> nat
  -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1 ->
  term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
  mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
  prim_val -> 'a1) -> term -> 'a1

val coq_NoConfusionPackage_term : term coq_NoConfusionPackage

val mkApps : term -> term list -> term

val isApp : term -> bool

val isLambda : term -> bool

val lift : nat -> nat -> term -> term

val subst : term list -> nat -> term -> term

val subst1 : term -> nat -> term -> term

val closedn : nat -> term -> bool

val test_context_nlict : (term -> bool) -> term context_decl list -> bool

val test_branch_nlict : (term -> bool) -> term branch -> bool

val test_branches_nlict : (term -> bool) -> term branch list -> bool

val nlict : term -> bool

val noccur_between : nat -> nat -> term -> bool

val subst_instance_constr : term coq_UnivSubst

val closedu : nat -> term -> bool

module PCUICTerm :
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

module PCUICEnvironment :
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

val destArity :
  term context_decl list -> term -> (term context_decl list * Sort.t) option

val inds :
  kername -> Instance.t -> PCUICEnvironment.one_inductive_body list -> term
  list

module PCUICTermUtils :
 sig
  val destArity :
    term context_decl list -> term -> (term context_decl list * Sort.t) option

  val inds :
    kername -> Instance.t -> PCUICEnvironment.one_inductive_body list -> term
    list
 end

module PCUICEnvTyping :
 sig
  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type 'wf_term lift_wf_term = __ * 'wf_term

  type ('wf_term, 'wf_univ) lift_wfu_term = __ * ('wf_term * __)

  val lift_wfb_term : (term -> bool) -> PCUICEnvironment.judgment -> bool

  val lift_wfbu_term :
    (term -> bool) -> (Sort.t -> bool) -> PCUICEnvironment.judgment -> bool

  type ('checking, 'sorting) lift_sorting = __ * (Sort.t, 'sorting * __) sigT

  type 'typing lift_typing0 = ('typing, 'typing) lift_sorting

  type ('p, 'q) lift_typing_conj = ('p * 'q) lift_typing0

  val lift_wf_term_it_impl :
    term option -> term option -> term -> term -> Sort.t option -> Sort.t
    option -> 'a1 lift_wf_term -> __ -> ('a1 -> 'a2) -> 'a2 lift_wf_term

  val lift_wf_term_f_impl :
    term option -> term -> Sort.t option -> Sort.t option -> (term -> term)
    -> 'a1 lift_wf_term -> (term -> 'a1 -> 'a2) -> 'a2 lift_wf_term

  val lift_wf_term_impl :
    PCUICEnvironment.judgment -> 'a1 lift_wf_term -> (term -> 'a1 -> 'a2) ->
    'a2 lift_wf_term

  val unlift_TermTyp :
    term -> term -> Sort.t option -> ('a1, 'a2) lift_sorting -> 'a1

  val unlift_TypUniv :
    term option -> term -> Sort.t -> ('a1, 'a2) lift_sorting -> 'a2

  val lift_sorting_extract :
    term option -> term -> Sort.t option -> ('a1, 'a2) lift_sorting -> ('a1,
    'a2) lift_sorting

  val lift_sorting_forget_univ :
    term option -> term -> Sort.t option -> ('a1, 'a2) lift_sorting -> ('a1,
    'a2) lift_sorting

  val lift_sorting_forget_body :
    term option -> term -> Sort.t option -> ('a1, 'a2) lift_sorting -> ('a1,
    'a2) lift_sorting

  val lift_sorting_ex_it_impl_gen :
    term option -> term option -> term -> term -> ('a1, 'a3) lift_sorting ->
    __ -> ('a3 -> (Sort.t, 'a4) sigT) -> ('a2, 'a4) lift_sorting

  val lift_sorting_it_impl_gen :
    term option -> term option -> term -> term -> Sort.t option -> ('a1, 'a3)
    lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_fu_it_impl :
    term option -> term -> Sort.t option -> (term -> term) -> (Sort.t ->
    Sort.t) -> ('a1, 'a3) lift_sorting -> __ -> ('a3 -> 'a4) -> ('a2, 'a4)
    lift_sorting

  val lift_sorting_f_it_impl :
    PCUICEnvironment.judgment -> (term -> term) -> ('a1, 'a3) lift_sorting ->
    __ -> ('a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_it_impl :
    PCUICEnvironment.judgment -> ('a1, 'a3) lift_sorting -> __ -> ('a3 ->
    'a4) -> ('a2, 'a4) lift_sorting

  val lift_sorting_fu_impl :
    term option -> term -> Sort.t option -> (term -> term) -> (Sort.t ->
    Sort.t) -> ('a1, 'a3) lift_sorting -> (term -> term -> 'a1 -> 'a2) ->
    (term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_fu_impl :
    term option -> term -> Sort.t option -> (term -> term) -> (Sort.t ->
    Sort.t) -> 'a1 lift_typing0 -> (term -> term -> 'a1 -> 'a2) -> 'a2
    lift_typing0

  val lift_sorting_f_impl :
    PCUICEnvironment.judgment -> (term -> term) -> ('a1, 'a3) lift_sorting ->
    (term -> term -> 'a1 -> 'a2) -> (term -> Sort.t -> 'a3 -> 'a4) -> ('a2,
    'a4) lift_sorting

  val lift_typing_f_impl :
    PCUICEnvironment.judgment -> (term -> term) -> 'a1 lift_typing0 -> (term
    -> term -> 'a1 -> 'a2) -> 'a2 lift_typing0

  val lift_typing_map :
    (term -> term) -> PCUICEnvironment.judgment -> 'a1 lift_typing0 -> 'a1
    lift_typing0

  val lift_typing_mapu :
    (term -> term) -> (Sort.t -> Sort.t) -> term option -> term -> Sort.t
    option -> 'a1 lift_typing0 -> 'a1 lift_typing0

  val lift_sorting_impl :
    PCUICEnvironment.judgment -> ('a1, 'a3) lift_sorting -> (term -> term ->
    'a1 -> 'a2) -> (term -> Sort.t -> 'a3 -> 'a4) -> ('a2, 'a4) lift_sorting

  val lift_typing_impl :
    PCUICEnvironment.judgment -> 'a1 lift_typing0 -> (term -> term -> 'a1 ->
    'a2) -> 'a2 lift_typing0

  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of PCUICEnvironment.context * aname * term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of PCUICEnvironment.context * aname * term * 
     term * 'typing coq_All_local_env * 'typing

  val coq_All_local_env_rect :
    'a2 -> (PCUICEnvironment.context -> aname -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> (PCUICEnvironment.context ->
    aname -> term -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1 -> 'a2) ->
    PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (PCUICEnvironment.context -> aname -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> (PCUICEnvironment.context ->
    aname -> term -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1 -> 'a2) ->
    PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    PCUICEnvironment.context -> 'a1 coq_All_local_env ->
    PCUICEnvironment.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    PCUICEnvironment.context -> ('a1 coq_All_local_env,
    PCUICEnvironment.context, 'a1 coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (PCUICEnvironment.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val localenv_cons :
    PCUICEnvironment.context -> aname -> term option -> term -> 'a1
    coq_All_local_env -> 'a1 -> 'a1 coq_All_local_env

  val coq_All_local_env_snoc :
    PCUICEnvironment.context -> term context_decl -> 'a1 coq_All_local_env ->
    'a1 -> 'a1 coq_All_local_env

  val coq_All_local_env_tip :
    term context_decl list -> term context_decl -> 'a1 coq_All_local_env ->
    'a1 coq_All_local_env * 'a1

  val coq_All_local_env_ind1 :
    'a2 -> (term context_decl list -> term context_decl -> 'a2 -> 'a1 -> 'a2)
    -> PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a2

  val coq_All_local_env_map :
    (term -> term) -> PCUICEnvironment.context -> 'a1 coq_All_local_env ->
    'a1 coq_All_local_env

  val coq_All_local_env_fold :
    (nat -> term -> term) -> PCUICEnvironment.context -> ('a1
    coq_All_local_env, 'a1 coq_All_local_env) iffT

  val coq_All_local_env_impl_gen :
    PCUICEnvironment.context -> 'a1 coq_All_local_env ->
    (PCUICEnvironment.context -> term context_decl -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_impl :
    PCUICEnvironment.context -> 'a1 coq_All_local_env ->
    (PCUICEnvironment.context -> PCUICEnvironment.judgment -> 'a1 -> 'a2) ->
    'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    PCUICEnvironment.context -> 'a1 coq_All_local_env ->
    (PCUICEnvironment.context -> PCUICEnvironment.judgment -> 'a2
    coq_All_local_env -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_skipn :
    PCUICEnvironment.context -> nat -> 'a1 coq_All_local_env -> 'a1
    coq_All_local_env

  val coq_All_local_env_app_skipn :
    term context_decl list -> term context_decl list -> nat -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_env

  val coq_All_local_env_nth_error :
    PCUICEnvironment.context -> nat -> term context_decl -> 'a1
    coq_All_local_env -> 'a1

  val coq_All_local_env_cst :
    PCUICEnvironment.context -> ('a1 coq_All_local_env, (term context_decl,
    'a1) coq_All) iffT

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : term context_decl list -> 'a1 coq_All_local_rel

  val coq_All_local_rel_snoc :
    term context_decl list -> PCUICEnvironment.context -> term context_decl
    -> 'a1 coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    term context_decl list -> PCUICEnvironment.context -> term -> aname ->
    'a1 coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    term context_decl list -> PCUICEnvironment.context -> term -> term ->
    aname -> 'a1 coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_tip :
    term context_decl list -> term context_decl list -> term context_decl ->
    'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1

  val coq_All_local_rel_ind1 :
    term context_decl list -> 'a2 -> (term context_decl list -> term
    context_decl -> 'a2 -> 'a1 -> 'a2) -> PCUICEnvironment.context -> 'a1
    coq_All_local_rel -> 'a2

  val coq_All_local_rel_local :
    PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    PCUICEnvironment.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    term context_decl list -> term context_decl list -> 'a1 coq_All_local_env
    -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_env_app_inv :
    term context_decl list -> term context_decl list -> 'a1 coq_All_local_env
    -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

  val coq_All_local_rel_app_inv :
    term context_decl list -> term context_decl list -> term context_decl
    list -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_rel * 'a1
    coq_All_local_rel

  val coq_All_local_env_app :
    PCUICEnvironment.context -> PCUICEnvironment.context -> 'a1
    coq_All_local_env -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_rel_app :
    term context_decl list -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> 'a1 coq_All_local_rel -> 'a1
    coq_All_local_rel -> 'a1 coq_All_local_rel

  val coq_All_local_env_prod_inv :
    PCUICEnvironment.context -> ('a1 * 'a2) coq_All_local_env -> 'a1
    coq_All_local_env * 'a2 coq_All_local_env

  val coq_All_local_env_lift_prod_inv :
    PCUICEnvironment.context -> ('a1 * 'a2) lift_typing0 coq_All_local_env ->
    'a1 lift_typing0 coq_All_local_env * 'a2 lift_typing0 coq_All_local_env

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of PCUICEnvironment.context * aname * 
     term * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'sproperty
  | Coq_localenv_over_cons_def of PCUICEnvironment.context * aname * 
     term * term * ('checking, 'sorting) lift_sorting coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_sorting * ('checking, 'sorting) lift_sorting
     * 'cproperty * 'sproperty

  val coq_All_local_env_over_sorting_rect :
    'a5 -> (PCUICEnvironment.context -> aname -> term -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4
    -> 'a5) -> (PCUICEnvironment.context -> aname -> term -> term -> ('a1,
    'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a3
    -> 'a4 -> 'a5) -> PCUICEnvironment.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5

  val coq_All_local_env_over_sorting_rec :
    'a5 -> (PCUICEnvironment.context -> aname -> term -> ('a1, 'a2)
    lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a4
    -> 'a5) -> (PCUICEnvironment.context -> aname -> term -> term -> ('a1,
    'a2) lift_sorting coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_sorting -> 'a5 -> ('a1, 'a2) lift_sorting -> 'a3
    -> 'a4 -> 'a5) -> PCUICEnvironment.context -> ('a1, 'a2) lift_sorting
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting
    -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty)
    coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_sig_pack :
    PCUICEnvironment.context -> ('a1, 'a2) lift_sorting coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting ->
    (PCUICEnvironment.context * ('a1, 'a2) lift_sorting
    coq_All_local_env) * ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_Signature :
    PCUICEnvironment.context -> ('a1, 'a2) lift_sorting coq_All_local_env ->
    (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting,
    PCUICEnvironment.context * ('a1, 'a2) lift_sorting coq_All_local_env,
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing, 'property, 'property) coq_All_local_env_over_sorting

  val coq_All_local_env_over_sorting_2 :
    PCUICEnvironment.context -> ('a1, 'a2) lift_sorting coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_sorting -> ('a1 * 'a3,
    'a2 * 'a4) lift_sorting coq_All_local_env

  type ('typing, 'p) on_wf_local_decl = __

  val nth_error_All_local_env_over :
    term context_decl list -> nat -> term context_decl -> 'a1 lift_typing0
    coq_All_local_env -> ('a1, 'a2) coq_All_local_env_over -> ('a1, 'a2)
    coq_All_local_env_over * ('a1, 'a2) on_wf_local_decl

  val coq_All_local_env_over_2 :
    PCUICEnvironment.context -> 'a1 lift_typing0 coq_All_local_env -> ('a1,
    'a2) coq_All_local_env_over -> ('a1, 'a2) lift_typing_conj
    coq_All_local_env

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * term * term * term list
     * PCUICEnvironment.context * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * term * term * term list
     * PCUICEnvironment.context * 'typing ctx_inst

  val ctx_inst_rect :
    PCUICEnvironment.context -> 'a2 -> (aname -> term -> term -> term list ->
    PCUICEnvironment.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> PCUICEnvironment.context -> 'a1 ctx_inst
    -> 'a2 -> 'a2) -> term list -> PCUICEnvironment.context -> 'a1 ctx_inst
    -> 'a2

  val ctx_inst_rec :
    PCUICEnvironment.context -> 'a2 -> (aname -> term -> term -> term list ->
    PCUICEnvironment.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> PCUICEnvironment.context -> 'a1 ctx_inst
    -> 'a2 -> 'a2) -> term list -> PCUICEnvironment.context -> 'a1 ctx_inst
    -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    PCUICEnvironment.context -> term list -> PCUICEnvironment.context -> 'a1
    ctx_inst -> (term list * PCUICEnvironment.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    PCUICEnvironment.context -> term list -> PCUICEnvironment.context -> ('a1
    ctx_inst, term list * PCUICEnvironment.context, 'a1 ctx_inst_sig)
    coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    PCUICEnvironment.context -> ((term list * PCUICEnvironment.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    PCUICEnvironment.context -> term list -> PCUICEnvironment.context -> __
    list -> (__, __ ctx_inst) sigT -> (term -> term -> (__, __) coq_All ->
    'a1) -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    PCUICEnvironment.context -> term list -> PCUICEnvironment.context -> 'a1
    ctx_inst -> (term -> term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val option_default_size : ('a1 -> 'a2 -> size) -> 'a1 option -> __ -> size

  val lift_sorting_size_gen :
    (term -> term -> 'a1 -> size) -> (term -> Sort.t -> 'a2 -> size) -> nat
    -> PCUICEnvironment.judgment -> ('a1, 'a2) lift_sorting -> size

  val lift_sorting_size_gen_impl :
    (term -> term -> 'a1 -> size) -> (term -> Sort.t -> 'a2 -> size) ->
    PCUICEnvironment.judgment -> ('a1, 'a2) lift_sorting -> (term -> term ->
    'a1 -> __ -> 'a3) -> (term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val on_def_type_size_gen :
    (PCUICEnvironment.context -> term -> Sort.t -> 'a2 -> size) -> nat ->
    PCUICEnvironment.context -> term def -> ('a1, 'a2) lift_sorting
    on_def_type -> size

  val on_def_body_size_gen :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    (PCUICEnvironment.context -> term -> Sort.t -> 'a2 -> size) -> nat ->
    term context_decl list -> term context_decl list -> term def -> ('a1,
    'a2) lift_sorting on_def_body -> size

  val lift_sorting_size_impl :
    PCUICEnvironment.judgment -> (term -> term -> 'a1 -> nat) -> (term ->
    Sort.t -> 'a2 -> size) -> ('a1, 'a2) lift_sorting -> (term -> term -> 'a1
    -> __ -> 'a3) -> (term -> Sort.t -> 'a2 -> __ -> 'a4) -> ('a3, 'a4)
    lift_sorting

  val lift_typing_size_impl :
    PCUICEnvironment.judgment -> (term -> term -> 'a1 -> nat) -> 'a1
    lift_typing0 -> (term -> term -> 'a1 -> __ -> 'a2) -> 'a2 lift_typing0

  val coq_All_local_env_size_gen :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    (PCUICEnvironment.context -> term -> Sort.t -> 'a2 -> size) -> size ->
    PCUICEnvironment.context -> ('a1, 'a2) lift_sorting coq_All_local_env ->
    size

  val coq_All_local_env_size :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    PCUICEnvironment.context -> ('a1, 'a1) lift_sorting coq_All_local_env ->
    size

  val coq_All_local_rel_size :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    PCUICEnvironment.context -> PCUICEnvironment.context -> 'a1 lift_typing0
    coq_All_local_rel -> size

  val coq_All_local_env_sorting_size :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    (PCUICEnvironment.context -> term -> Sort.t -> 'a2 -> size) ->
    PCUICEnvironment.context -> ('a1, 'a2) lift_sorting coq_All_local_env ->
    size

  val coq_All_local_rel_sorting_size :
    (PCUICEnvironment.context -> term -> term -> 'a1 -> size) ->
    (PCUICEnvironment.context -> term -> Sort.t -> 'a2 -> size) -> term
    context_decl list -> PCUICEnvironment.context -> ('a1, 'a2) lift_sorting
    coq_All_local_rel -> size
 end

module PCUICConversion :
 sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot * 
     term * term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot * 
     term * term * term * term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> term context_decl -> term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> term context_decl -> term context_decl -> ('a1
    coq_All_decls_alpha_pb, term context_decl * term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> term context_decl -> term context_decl -> (conv_pb -> term ->
    term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end

val context_reflect :
  term coq_ReflectEq -> term context_decl list coq_ReflectEq

val string_of_predicate : ('a1 -> String.t) -> 'a1 predicate -> String.t

val eqb_predicate_gen :
  (Instance.t -> Instance.t -> bool) -> (term context_decl -> term
  context_decl -> bool) -> (term -> term -> bool) -> term predicate -> term
  predicate -> bool

val eqb_predicate :
  (term -> term -> bool) -> term predicate -> term predicate -> bool

type 'p tCasePredProp_k = (term, 'p) coq_All * ((term, 'p) onctx_k * 'p)

type ('term, 'pparams, 'preturn) tCasePredProp =
  ('term, 'pparams) coq_All * (('term context_decl, ('term, 'pparams) ondecl)
  coq_All * 'preturn)

val test_prim_primProp : ('a1 -> bool) -> 'a1 prim_val -> ('a1, __) tPrimProp

val tPrimProp_impl :
  'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3)
  tPrimProp

val tPrimProp_prod :
  'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a3) tPrimProp -> ('a1,
  'a2 * 'a3) tPrimProp

val primProp_map :
  ('a1 -> 'a1) -> 'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a2) tPrimProp

val primProp_map_inv :
  ('a1 -> 'a1) -> 'a1 prim_val -> ('a1, 'a2) tPrimProp -> ('a1, 'a2) tPrimProp

type ('a, 'p) tCaseBrsProp =
  ('a branch, ('a context_decl, ('a, 'p) ondecl) coq_All * 'p) coq_All

type 'p tCaseBrsProp_k = (term branch, (term, 'p) onctx_k * 'p) coq_All

val onctx_k_rev :
  nat -> term context_decl list -> ((term, 'a1) onctx_k, (term context_decl,
  (term, 'a1) ondecl) coq_Alli) iffT

val onctx_k_shift :
  nat -> term context_decl list -> (term, 'a1) onctx_k -> (term, 'a1) onctx_k

val onctx_k_P :
  (nat -> term -> bool) -> nat -> PCUICEnvironment.context -> (nat -> term ->
  'a1 reflectT) -> (term, 'a1) onctx_k reflectT

module PCUICLookup :
 sig
  val lookup_constant_gen :
    (kername -> PCUICEnvironment.global_decl option) -> kername ->
    PCUICEnvironment.constant_body option

  val lookup_constant :
    PCUICEnvironment.global_env -> kername -> PCUICEnvironment.constant_body
    option

  val lookup_minductive_gen :
    (kername -> PCUICEnvironment.global_decl option) -> kername ->
    PCUICEnvironment.mutual_inductive_body option

  val lookup_minductive :
    PCUICEnvironment.global_env -> kername ->
    PCUICEnvironment.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> PCUICEnvironment.global_decl option) -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option

  val lookup_inductive :
    PCUICEnvironment.global_env -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option

  val lookup_constructor_gen :
    (kername -> PCUICEnvironment.global_decl option) -> inductive -> nat ->
    ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
    option

  val lookup_constructor :
    PCUICEnvironment.global_env -> inductive -> nat ->
    ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
    option

  val lookup_projection_gen :
    (kername -> PCUICEnvironment.global_decl option) -> projection ->
    (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
    option

  val lookup_projection :
    PCUICEnvironment.global_env -> projection ->
    (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
    option

  val on_udecl_decl :
    (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1

  val universes_decl_of_decl : PCUICEnvironment.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : PCUICEnvironment.global_env -> ConstraintSet.t

  val global_uctx : PCUICEnvironment.global_env -> ContextSet.t

  val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t

  val global_ext_constraints :
    PCUICEnvironment.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : PCUICEnvironment.global_env_ext -> ContextSet.t

  val wf_universe_dec : PCUICEnvironment.global_env_ext -> Universe.t -> bool

  val wf_sort_dec : PCUICEnvironment.global_env_ext -> Sort.t -> bool

  val declared_ind_declared_constructors :
    checker_flags -> PCUICEnvironment.global_env -> inductive ->
    PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.one_inductive_body ->
    (PCUICEnvironment.constructor_body, __) coq_Alli
 end

val lookup_constant_gen :
  (kername -> PCUICEnvironment.global_decl option) -> kername ->
  PCUICEnvironment.constant_body option

val lookup_constant :
  PCUICEnvironment.global_env -> kername -> PCUICEnvironment.constant_body
  option

val lookup_minductive_gen :
  (kername -> PCUICEnvironment.global_decl option) -> kername ->
  PCUICEnvironment.mutual_inductive_body option

val lookup_minductive :
  PCUICEnvironment.global_env -> kername ->
  PCUICEnvironment.mutual_inductive_body option

val lookup_inductive_gen :
  (kername -> PCUICEnvironment.global_decl option) -> inductive ->
  (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
  option

val lookup_inductive :
  PCUICEnvironment.global_env -> inductive ->
  (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
  option

val lookup_constructor_gen :
  (kername -> PCUICEnvironment.global_decl option) -> inductive -> nat ->
  ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
  option

val lookup_constructor :
  PCUICEnvironment.global_env -> inductive -> nat ->
  ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
  option

val lookup_projection_gen :
  (kername -> PCUICEnvironment.global_decl option) -> projection ->
  (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
  option

val lookup_projection :
  PCUICEnvironment.global_env -> projection ->
  (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
  option

val on_udecl_decl :
  (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1

val universes_decl_of_decl : PCUICEnvironment.global_decl -> universes_decl

val global_levels : ContextSet.t -> LevelSet.t

val global_constraints : PCUICEnvironment.global_env -> ConstraintSet.t

val global_uctx : PCUICEnvironment.global_env -> ContextSet.t

val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t

val global_ext_constraints :
  PCUICEnvironment.global_env_ext -> ConstraintSet.t

val global_ext_uctx : PCUICEnvironment.global_env_ext -> ContextSet.t

val wf_universe_dec : PCUICEnvironment.global_env_ext -> Universe.t -> bool

val wf_sort_dec : PCUICEnvironment.global_env_ext -> Sort.t -> bool

val declared_ind_declared_constructors :
  checker_flags -> PCUICEnvironment.global_env -> inductive ->
  PCUICEnvironment.mutual_inductive_body ->
  PCUICEnvironment.one_inductive_body -> (PCUICEnvironment.constructor_body,
  __) coq_Alli

val coq_NoConfusionPackage_global_decl :
  PCUICEnvironment.global_decl coq_NoConfusionPackage

module PCUICGlobalMaps :
 sig
  type 'p on_context = 'p PCUICEnvTyping.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : PCUICEnvironment.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of term
  | Coq_pos_arg_concl of term list * nat
     * PCUICEnvironment.one_inductive_body * (term, __) coq_All
  | Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

  val positive_cstr_arg_rect :
    PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
    -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
    PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
    'a1) -> (term context_decl list -> aname -> term -> term -> term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
    term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term
    context_decl list -> term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
    -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
    PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
    'a1) -> (term context_decl list -> aname -> term -> term -> term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
    term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term
    context_decl list -> term -> positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of term list * (term, __) coq_All
  | Coq_pos_let of aname * term * term * term * positive_cstr
  | Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list
    -> term list -> (term, __) coq_All -> 'a1) -> (term context_decl list ->
    aname -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> positive_cstr_arg ->
    positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr -> 'a1

  val positive_cstr_rec :
    PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list
    -> term list -> (term, __) coq_All -> 'a1) -> (term context_decl list ->
    aname -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> positive_cstr_arg ->
    positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t * ConstraintType.t) * Level.t) ->
    (Level.t_ * ConstraintType.t) * Level.t_

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl * Level.t_
    list) * Level.t_ list) option

  val ind_arities :
    PCUICEnvironment.mutual_inductive_body -> term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term

  val cstr_concl :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p PCUICEnvTyping.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> 'a2 PCUICEnvTyping.ctx_inst

  val on_ctype_positive :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
    on_constructor -> Variance.t list -> 'a1 cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (PCUICEnvironment.constructor_body, Sort.t list, ('pcmp, 'p)
    on_constructor) coq_All2

  type on_projections =
    (PCUICEnvironment.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    PCUICEnvironment.mutual_inductive_body -> kername -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> on_projections ->
    (PCUICEnvironment.projection_body, __) coq_Alli

  type constructor_univs = Sort.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  val onArity :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    on_type

  val ind_cunivs :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1,
    'a2) on_constructors

  val onProjections :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (PCUICEnvironment.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    (PCUICEnvironment.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli

  val onParams :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2
    on_context

  val onVariance :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    on_variance

  type 'p on_constant_decl = 'p

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
    universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data -> ('a1,
    'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of PCUICEnvironment.global_declarations * kername
     * PCUICEnvironment.global_decl * ('pcmp, 'p) on_global_decls
     * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
    PCUICEnvironment.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> (('a1, 'a2) on_global_decls,
    PCUICEnvironment.global_declarations, ('a1, 'a2) on_global_decls_sig)
    coq_Signature

  type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

  type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

  val on_global_env_ext_empty_ext :
    checker_flags -> PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a2) on_global_env_ext

  val type_local_ctx_impl_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Sort.t -> __ list -> (__, __ type_local_ctx)
    sigT -> (PCUICEnvironment.context -> PCUICEnvironment.judgment -> (__,
    __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx

  val type_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t -> 'a1
    type_local_ctx -> (PCUICEnvironment.context -> PCUICEnvironment.judgment
    -> 'a1 -> 'a2) -> 'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Sort.t list -> __ list -> (__, __
    sorts_local_ctx) sigT -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> (__, __) coq_All -> 'a1) -> (__, __
    sorts_local_ctx) coq_All -> 'a1 sorts_local_ctx

  val sorts_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t list ->
    'a1 sorts_local_ctx -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> 'a1 -> 'a2) -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    PCUICEnvironment.global_env -> PCUICEnvironment.mutual_inductive_body ->
    Variance.t list -> PCUICEnvironment.constructor_body -> __ list -> (__,
    __ cstr_respects_variance) sigT -> __ -> (__, __ cstr_respects_variance)
    coq_All -> 'a1 cstr_respects_variance

  val cstr_respects_variance_impl :
    PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
    PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
    PCUICEnvironment.constructor_body -> __ -> 'a1 cstr_respects_variance ->
    'a2 cstr_respects_variance

  val on_constructor_impl_config_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
    -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
    -> PCUICEnvironment.constructor_body -> Sort.t list ->
    ((checker_flags * __) * __) list -> checker_flags ->
    ((checker_flags * __) * __, __) sigT -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ((checker_flags * __) * __, __) coq_All ->
    'a2) -> (universes_decl -> PCUICEnvironment.context -> term -> term ->
    conv_pb -> ((checker_flags * __) * __, __) coq_All -> 'a1) ->
    ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructor

  val on_constructors_impl_config_gen :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
    -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
    -> PCUICEnvironment.constructor_body list -> Sort.t list list ->
    ((checker_flags * __) * __) list -> checker_flags ->
    ((checker_flags * __) * __, __) sigT -> ((checker_flags * __) * __, __)
    coq_All -> (PCUICEnvironment.context -> PCUICEnvironment.judgment ->
    ((checker_flags * __) * __, __) coq_All -> 'a2) -> (universes_decl ->
    PCUICEnvironment.context -> term -> term -> conv_pb ->
    ((checker_flags * __) * __, __) coq_All -> 'a1) ->
    ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructors

  val ind_respects_variance_impl :
    PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
    PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
    PCUICEnvironment.context -> __ -> 'a1 ind_respects_variance -> 'a2
    ind_respects_variance

  val on_variance_impl :
    PCUICEnvironment.global_env -> universes_decl -> Variance.t list option
    -> checker_flags -> checker_flags -> on_variance -> on_variance

  val on_global_decl_impl_full :
    checker_flags -> checker_flags ->
    (PCUICEnvironment.global_env * universes_decl) ->
    (PCUICEnvironment.global_env * universes_decl) -> kername ->
    PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> 'a3 -> 'a4) -> (universes_decl ->
    PCUICEnvironment.context -> conv_pb -> term -> term -> 'a1 -> 'a2) ->
    (universes_decl -> Variance.t list option -> on_variance -> on_variance)
    -> ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl

  val on_global_decl_impl_only_config :
    checker_flags -> checker_flags -> checker_flags ->
    (PCUICEnvironment.global_env * universes_decl) -> kername ->
    PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ('a1, 'a3) on_global_env -> 'a3 -> 'a4) ->
    (universes_decl -> PCUICEnvironment.context -> conv_pb -> term -> term ->
    ('a1, 'a3) on_global_env -> 'a1 -> 'a2) -> ('a1, 'a3) on_global_env ->
    ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl

  val on_global_decl_impl_simple :
    checker_flags -> (PCUICEnvironment.global_env * universes_decl) ->
    kername -> PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
    PCUICEnvironment.judgment -> ('a1, 'a2) on_global_env -> 'a2 -> 'a3) ->
    ('a1, 'a2) on_global_env -> ('a1, 'a2) on_global_decl -> ('a1, 'a3)
    on_global_decl

  val on_global_env_impl_config :
    checker_flags -> checker_flags ->
    ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> PCUICEnvironment.judgment -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env -> 'a3 -> 'a4) ->
    ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> term -> term -> conv_pb -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) ->
    PCUICEnvironment.global_env -> ('a1, 'a3) on_global_env -> ('a2, 'a4)
    on_global_env

  val on_global_env_impl :
    checker_flags -> ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> PCUICEnvironment.judgment -> ('a1, 'a2)
    on_global_env -> ('a1, 'a3) on_global_env -> 'a2 -> 'a3) ->
    PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env

  val lookup_on_global_env :
    checker_flags -> PCUICEnvironment.global_env -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_env ->
    (PCUICEnvironment.global_env_ext, ('a1, 'a2)
    on_global_env * (PCUICEnvironment.strictly_extends_decls * ('a1, 'a2)
    on_global_decl)) sigT
 end

type 'p on_context = 'p PCUICEnvTyping.coq_All_local_env

type 'p type_local_ctx = __

type 'p sorts_local_ctx = __

type 'p on_type = 'p

val univs_ext_constraints :
  ConstraintSet.t -> universes_decl -> ConstraintSet.t

val ind_realargs : PCUICEnvironment.one_inductive_body -> nat

type positive_cstr_arg = PCUICGlobalMaps.positive_cstr_arg =
| Coq_pos_arg_closed of term
| Coq_pos_arg_concl of term list * nat * PCUICEnvironment.one_inductive_body
   * (term, __) coq_All
| Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
| Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

val positive_cstr_arg_rect :
  PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
  -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
  PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
  'a1) -> (term context_decl list -> aname -> term -> term -> term ->
  positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
  term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl
  list -> term -> positive_cstr_arg -> 'a1

val positive_cstr_arg_rec :
  PCUICEnvironment.mutual_inductive_body -> (term context_decl list -> term
  -> __ -> 'a1) -> (term context_decl list -> term list -> nat ->
  PCUICEnvironment.one_inductive_body -> __ -> (term, __) coq_All -> __ ->
  'a1) -> (term context_decl list -> aname -> term -> term -> term ->
  positive_cstr_arg -> 'a1 -> 'a1) -> (term context_decl list -> aname ->
  term -> term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl
  list -> term -> positive_cstr_arg -> 'a1

type positive_cstr = PCUICGlobalMaps.positive_cstr =
| Coq_pos_concl of term list * (term, __) coq_All
| Coq_pos_let of aname * term * term * term * positive_cstr
| Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

val positive_cstr_rect :
  PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list ->
  term list -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname
  -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
  context_decl list -> aname -> term -> term -> positive_cstr_arg ->
  positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
  positive_cstr -> 'a1

val positive_cstr_rec :
  PCUICEnvironment.mutual_inductive_body -> nat -> (term context_decl list ->
  term list -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname
  -> term -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term
  context_decl list -> aname -> term -> term -> positive_cstr_arg ->
  positive_cstr -> 'a1 -> 'a1) -> term context_decl list -> term ->
  positive_cstr -> 'a1

val lift_level : nat -> Level.t_ -> Level.t_

val lift_instance : nat -> Level.t_ list -> Level.t_ list

val lift_constraint :
  nat -> ((Level.t * ConstraintType.t) * Level.t) ->
  (Level.t_ * ConstraintType.t) * Level.t_

val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

val level_var_instance : nat -> name list -> Level.t_ list

val variance_cstrs :
  Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

val variance_universes :
  universes_decl -> Variance.t list -> ((universes_decl * Level.t_
  list) * Level.t_ list) option

val ind_arities :
  PCUICEnvironment.mutual_inductive_body -> term context_decl list

type 'pcmp ind_respects_variance = __

type 'pcmp cstr_respects_variance = __

val cstr_concl_head :
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.constructor_body -> term

val cstr_concl :
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.constructor_body -> term

type ('pcmp, 'p) on_constructor = ('pcmp, 'p) PCUICGlobalMaps.on_constructor = { 
on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
on_cindices : 'p PCUICEnvTyping.ctx_inst; on_ctype_positive : positive_cstr;
on_ctype_variance : (Variance.t list -> __ -> 'pcmp cstr_respects_variance) }

val on_ctype :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
  on_constructor -> 'a2 on_type

val on_cargs :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
  on_constructor -> 'a2 sorts_local_ctx

val on_cindices :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
  on_constructor -> 'a2 PCUICEnvTyping.ctx_inst

val on_ctype_positive :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
  on_constructor -> positive_cstr

val on_ctype_variance :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> Sort.t list -> ('a1, 'a2)
  on_constructor -> Variance.t list -> 'a1 cstr_respects_variance

type ('pcmp, 'p) on_constructors =
  (PCUICEnvironment.constructor_body, Sort.t list, ('pcmp, 'p)
  on_constructor) coq_All2

type on_projections =
  (PCUICEnvironment.projection_body, __) coq_Alli
  (* singleton inductive, whose constructor was Build_on_projections *)

val on_projs :
  PCUICEnvironment.mutual_inductive_body -> kername -> nat ->
  PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
  PCUICEnvironment.constructor_body -> on_projections ->
  (PCUICEnvironment.projection_body, __) coq_Alli

type constructor_univs = Sort.t list

val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

type 'p check_ind_sorts = __

type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) PCUICGlobalMaps.on_ind_body = { 
onArity : 'p on_type; ind_cunivs : constructor_univs list;
onConstructors : ('pcmp, 'p) on_constructors; onProjections : __;
ind_sorts : 'p check_ind_sorts; onIndices : __ }

val onArity :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

val ind_cunivs :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
  constructor_univs list

val onConstructors :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
  on_constructors

val onProjections :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

val ind_sorts :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
  check_ind_sorts

val onIndices :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> nat ->
  PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

type on_variance = __

type ('pcmp, 'p) on_inductive = ('pcmp, 'p) PCUICGlobalMaps.on_inductive = { 
onInductives : (PCUICEnvironment.one_inductive_body, ('pcmp, 'p) on_ind_body)
               coq_Alli; onParams : 'p on_context; onVariance : on_variance }

val onInductives :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
  (PCUICEnvironment.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli

val onParams :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2
  on_context

val onVariance :
  checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
  PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
  on_variance

type 'p on_constant_decl = 'p

type ('pcmp, 'p) on_global_decl = __

type ('pcmp, 'p) on_global_decls_data =
  ('pcmp, 'p) on_global_decl
  (* singleton inductive, whose constructor was Build_on_global_decls_data *)

val udecl :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  PCUICEnvironment.global_declarations -> kername ->
  PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
  universes_decl

val on_global_decl_d :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  PCUICEnvironment.global_declarations -> kername ->
  PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data -> ('a1,
  'a2) on_global_decl

type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) PCUICGlobalMaps.on_global_decls =
| Coq_globenv_nil
| Coq_globenv_decl of PCUICEnvironment.global_declarations * kername
   * PCUICEnvironment.global_decl * ('pcmp, 'p) on_global_decls
   * ('pcmp, 'p) on_global_decls_data

val on_global_decls_rect :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
  (PCUICEnvironment.global_declarations -> kername ->
  PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 -> ('a1,
  'a2) on_global_decls_data -> 'a3) -> PCUICEnvironment.global_declarations
  -> ('a1, 'a2) on_global_decls -> 'a3

val on_global_decls_rec :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
  (PCUICEnvironment.global_declarations -> kername ->
  PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 -> ('a1,
  'a2) on_global_decls_data -> 'a3) -> PCUICEnvironment.global_declarations
  -> ('a1, 'a2) on_global_decls -> 'a3

type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

val on_global_decls_sig_pack :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
  PCUICEnvironment.global_declarations * ('a1, 'a2) on_global_decls

val on_global_decls_Signature :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  PCUICEnvironment.global_declarations -> (('a1, 'a2) on_global_decls,
  PCUICEnvironment.global_declarations, ('a1, 'a2) on_global_decls_sig)
  coq_Signature

type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

val on_global_env_ext_empty_ext :
  checker_flags -> PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env ->
  ('a1, 'a2) on_global_env_ext

val type_local_ctx_impl_gen :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
  PCUICEnvironment.context -> Sort.t -> __ list -> (__, __ type_local_ctx)
  sigT -> (PCUICEnvironment.context -> PCUICEnvironment.judgment -> (__, __)
  coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1 type_local_ctx

val type_local_ctx_impl :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t -> 'a1
  type_local_ctx -> (PCUICEnvironment.context -> PCUICEnvironment.judgment ->
  'a1 -> 'a2) -> 'a2 type_local_ctx

val sorts_local_ctx_impl_gen :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
  PCUICEnvironment.context -> Sort.t list -> __ list -> (__, __
  sorts_local_ctx) sigT -> (PCUICEnvironment.context ->
  PCUICEnvironment.judgment -> (__, __) coq_All -> 'a1) -> (__, __
  sorts_local_ctx) coq_All -> 'a1 sorts_local_ctx

val sorts_local_ctx_impl :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> PCUICEnvironment.context -> Sort.t list -> 'a1
  sorts_local_ctx -> (PCUICEnvironment.context -> PCUICEnvironment.judgment
  -> 'a1 -> 'a2) -> 'a2 sorts_local_ctx

val cstr_respects_variance_impl_gen :
  PCUICEnvironment.global_env -> PCUICEnvironment.mutual_inductive_body ->
  Variance.t list -> PCUICEnvironment.constructor_body -> __ list -> (__, __
  cstr_respects_variance) sigT -> __ -> (__, __ cstr_respects_variance)
  coq_All -> 'a1 cstr_respects_variance

val cstr_respects_variance_impl :
  PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
  PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
  PCUICEnvironment.constructor_body -> __ -> 'a1 cstr_respects_variance ->
  'a2 cstr_respects_variance

val on_constructor_impl_config_gen :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
  -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
  -> PCUICEnvironment.constructor_body -> Sort.t list ->
  ((checker_flags * __) * __) list -> checker_flags ->
  ((checker_flags * __) * __, __) sigT -> (PCUICEnvironment.context ->
  PCUICEnvironment.judgment -> ((checker_flags * __) * __, __) coq_All ->
  'a2) -> (universes_decl -> PCUICEnvironment.context -> term -> term ->
  conv_pb -> ((checker_flags * __) * __, __) coq_All -> 'a1) ->
  ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructor

val on_constructors_impl_config_gen :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.mutual_inductive_body
  -> nat -> PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context
  -> PCUICEnvironment.constructor_body list -> Sort.t list list ->
  ((checker_flags * __) * __) list -> checker_flags ->
  ((checker_flags * __) * __, __) sigT -> ((checker_flags * __) * __, __)
  coq_All -> (PCUICEnvironment.context -> PCUICEnvironment.judgment ->
  ((checker_flags * __) * __, __) coq_All -> 'a2) -> (universes_decl ->
  PCUICEnvironment.context -> term -> term -> conv_pb ->
  ((checker_flags * __) * __, __) coq_All -> 'a1) ->
  ((checker_flags * __) * __, __) coq_All -> ('a1, 'a2) on_constructors

val ind_respects_variance_impl :
  PCUICEnvironment.global_env -> PCUICEnvironment.global_env ->
  PCUICEnvironment.mutual_inductive_body -> Variance.t list ->
  PCUICEnvironment.context -> __ -> 'a1 ind_respects_variance -> 'a2
  ind_respects_variance

val on_variance_impl :
  PCUICEnvironment.global_env -> universes_decl -> Variance.t list option ->
  checker_flags -> checker_flags -> on_variance -> on_variance

val on_global_decl_impl_full :
  checker_flags -> checker_flags ->
  (PCUICEnvironment.global_env * universes_decl) ->
  (PCUICEnvironment.global_env * universes_decl) -> kername ->
  PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
  PCUICEnvironment.judgment -> 'a3 -> 'a4) -> (universes_decl ->
  PCUICEnvironment.context -> conv_pb -> term -> term -> 'a1 -> 'a2) ->
  (universes_decl -> Variance.t list option -> on_variance -> on_variance) ->
  ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl

val on_global_decl_impl_only_config :
  checker_flags -> checker_flags -> checker_flags ->
  (PCUICEnvironment.global_env * universes_decl) -> kername ->
  PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
  PCUICEnvironment.judgment -> ('a1, 'a3) on_global_env -> 'a3 -> 'a4) ->
  (universes_decl -> PCUICEnvironment.context -> conv_pb -> term -> term ->
  ('a1, 'a3) on_global_env -> 'a1 -> 'a2) -> ('a1, 'a3) on_global_env ->
  ('a1, 'a3) on_global_decl -> ('a2, 'a4) on_global_decl

val on_global_decl_impl_simple :
  checker_flags -> (PCUICEnvironment.global_env * universes_decl) -> kername
  -> PCUICEnvironment.global_decl -> (PCUICEnvironment.context ->
  PCUICEnvironment.judgment -> ('a1, 'a2) on_global_env -> 'a2 -> 'a3) ->
  ('a1, 'a2) on_global_env -> ('a1, 'a2) on_global_decl -> ('a1, 'a3)
  on_global_decl

val on_global_env_impl_config :
  checker_flags -> checker_flags ->
  ((PCUICEnvironment.global_env * universes_decl) -> PCUICEnvironment.context
  -> PCUICEnvironment.judgment -> ('a1, 'a3) on_global_env -> ('a2, 'a4)
  on_global_env -> 'a3 -> 'a4) ->
  ((PCUICEnvironment.global_env * universes_decl) -> PCUICEnvironment.context
  -> term -> term -> conv_pb -> ('a1, 'a3) on_global_env -> ('a2, 'a4)
  on_global_env -> 'a1 -> 'a2) -> PCUICEnvironment.global_env -> ('a1, 'a3)
  on_global_env -> ('a2, 'a4) on_global_env

val on_global_env_impl :
  checker_flags -> ((PCUICEnvironment.global_env * universes_decl) ->
  PCUICEnvironment.context -> PCUICEnvironment.judgment -> ('a1, 'a2)
  on_global_env -> ('a1, 'a3) on_global_env -> 'a2 -> 'a3) ->
  PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
  on_global_env

val lookup_on_global_env :
  checker_flags -> PCUICEnvironment.global_env -> kername ->
  PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_env ->
  (PCUICEnvironment.global_env_ext, ('a1, 'a2)
  on_global_env * (PCUICEnvironment.strictly_extends_decls * ('a1, 'a2)
  on_global_decl)) sigT

type parameter_entry = { parameter_entry_type : term;
                         parameter_entry_universes : universes_decl }

val parameter_entry_type : parameter_entry -> term

val parameter_entry_universes : parameter_entry -> universes_decl

type definition_entry = { definition_entry_type : term;
                          definition_entry_body : term;
                          definition_entry_universes : universes_decl;
                          definition_entry_opaque : bool }

val definition_entry_type : definition_entry -> term

val definition_entry_body : definition_entry -> term

val definition_entry_universes : definition_entry -> universes_decl

val definition_entry_opaque : definition_entry -> bool

type constant_entry =
| ParameterEntry of parameter_entry
| DefinitionEntry of definition_entry

val constant_entry_rect :
  (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry ->
  'a1

val constant_entry_rec :
  (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry ->
  'a1

val coq_NoConfusionPackage_parameter_entry :
  parameter_entry coq_NoConfusionPackage

val coq_NoConfusionPackage_definition_entry :
  definition_entry coq_NoConfusionPackage

val coq_NoConfusionPackage_constant_entry :
  constant_entry coq_NoConfusionPackage

type local_entry =
| LocalDef of term
| LocalAssum of term

val local_entry_rect : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

val local_entry_rec : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_template : bool;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

val mind_entry_typename : one_inductive_entry -> ident

val mind_entry_arity : one_inductive_entry -> term

val mind_entry_template : one_inductive_entry -> bool

val mind_entry_consnames : one_inductive_entry -> ident list

val mind_entry_lc : one_inductive_entry -> term list

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : PCUICEnvironment.context;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_universes : universes_decl;
                                mind_entry_private : bool option }

val mind_entry_record : mutual_inductive_entry -> ident option option

val mind_entry_finite : mutual_inductive_entry -> recursivity_kind

val mind_entry_params : mutual_inductive_entry -> PCUICEnvironment.context

val mind_entry_inds : mutual_inductive_entry -> one_inductive_entry list

val mind_entry_universes : mutual_inductive_entry -> universes_decl

val mind_entry_private : mutual_inductive_entry -> bool option

val coq_NoConfusionPackage_local_entry : local_entry coq_NoConfusionPackage

val coq_NoConfusionPackage_one_inductive_entry :
  one_inductive_entry coq_NoConfusionPackage

val coq_NoConfusionPackage_mutual_inductive_entry :
  mutual_inductive_entry coq_NoConfusionPackage
