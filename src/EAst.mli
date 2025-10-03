open BasicAst
open Classes0
open Datatypes
open EPrimitive
open Kernames
open List0
open Nat0
open Universes0

type __ = Obj.t

type 'term def = { dname : name; dbody : 'term; rarg : nat }

val dname : 'a1 def -> name

val dbody : 'a1 def -> 'a1

val rarg : 'a1 def -> nat

val coq_NoConfusionPackage_def : 'a1 def coq_NoConfusionPackage

val map_def : ('a1 -> 'a1) -> 'a1 def -> 'a1 def

val test_def : ('a1 -> bool) -> 'a1 def -> bool

type 'term mfixpoint = 'term def list

type term =
| Coq_tBox
| Coq_tRel of nat
| Coq_tVar of ident
| Coq_tEvar of nat * term list
| Coq_tLambda of name * term
| Coq_tLetIn of name * term * term
| Coq_tApp of term * term
| Coq_tConst of kername
| Coq_tConstruct of inductive * nat * term list
| Coq_tCase of (inductive * nat) * term * (name list * term) list
| Coq_tProj of projection * term
| Coq_tFix of term mfixpoint * nat
| Coq_tCoFix of term mfixpoint * nat
| Coq_tPrim of term prim_val
| Coq_tLazy of term
| Coq_tForce of term

val term_rect :
  'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (name
  -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
  (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername -> 'a1) -> (inductive ->
  nat -> term list -> 'a1) -> ((inductive * nat) -> term -> 'a1 -> (name
  list * term) list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
  mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
  prim_val -> 'a1) -> (term -> 'a1 -> 'a1) -> (term -> 'a1 -> 'a1) -> term ->
  'a1

val term_rec :
  'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (name
  -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
  (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername -> 'a1) -> (inductive ->
  nat -> term list -> 'a1) -> ((inductive * nat) -> term -> 'a1 -> (name
  list * term) list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
  mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term
  prim_val -> 'a1) -> (term -> 'a1 -> 'a1) -> (term -> 'a1 -> 'a1) -> term ->
  'a1

val coq_NoConfusionPackage_term : term coq_NoConfusionPackage

val mkApps : term -> term list -> term

val mkApp : term -> term -> term

val isApp : term -> bool

val isLambda : term -> bool

type definition_entry = { definition_entry_body : term;
                          definition_entry_opaque : bool }

val definition_entry_body : definition_entry -> term

val definition_entry_opaque : definition_entry -> bool

type constant_entry =
| ParameterEntry
| DefinitionEntry of definition_entry

val constant_entry_rect :
  (__ -> 'a1) -> (definition_entry -> 'a1) -> constant_entry -> 'a1

val constant_entry_rec :
  (__ -> 'a1) -> (definition_entry -> 'a1) -> constant_entry -> 'a1

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
                                mind_entry_params : (ident * local_entry) list;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_private : bool option }

val mind_entry_record : mutual_inductive_entry -> ident option option

val mind_entry_finite : mutual_inductive_entry -> recursivity_kind

val mind_entry_params : mutual_inductive_entry -> (ident * local_entry) list

val mind_entry_inds : mutual_inductive_entry -> one_inductive_entry list

val mind_entry_private : mutual_inductive_entry -> bool option

type context_decl = { decl_name : name; decl_body : term option }

val decl_name : context_decl -> name

val decl_body : context_decl -> term option

val vass : name -> context_decl

val vdef : name -> term -> context_decl

type context = context_decl list

val map_decl : (term -> term) -> context_decl -> context_decl

val map_context : (term -> term) -> context_decl list -> context_decl list

val snoc : 'a1 list -> 'a1 -> 'a1 list

type constructor_body = { cstr_name : ident; cstr_nargs : nat }

val cstr_name : constructor_body -> ident

val cstr_nargs : constructor_body -> nat

val coq_NoConfusionPackage_constructor_body :
  constructor_body coq_NoConfusionPackage

type projection_body =
  ident
  (* singleton inductive, whose constructor was mkProjection *)

val proj_name : projection_body -> ident

val coq_NoConfusionPackage_projection_body :
  projection_body coq_NoConfusionPackage

type one_inductive_body = { ind_name : ident; ind_propositional : bool;
                            ind_kelim : allowed_eliminations;
                            ind_ctors : constructor_body list;
                            ind_projs : projection_body list }

val ind_name : one_inductive_body -> ident

val ind_propositional : one_inductive_body -> bool

val ind_kelim : one_inductive_body -> allowed_eliminations

val ind_ctors : one_inductive_body -> constructor_body list

val ind_projs : one_inductive_body -> projection_body list

val coq_NoConfusionPackage_one_inductive_body :
  one_inductive_body coq_NoConfusionPackage

type mutual_inductive_body = { ind_finite : recursivity_kind;
                               ind_npars : nat;
                               ind_bodies : one_inductive_body list }

val ind_finite : mutual_inductive_body -> recursivity_kind

val ind_npars : mutual_inductive_body -> nat

val ind_bodies : mutual_inductive_body -> one_inductive_body list

val coq_NoConfusionPackage_mutual_inductive_body :
  mutual_inductive_body coq_NoConfusionPackage

val cstr_arity : mutual_inductive_body -> constructor_body -> nat

type constant_body =
  term option
  (* singleton inductive, whose constructor was Build_constant_body *)

val cst_body : constant_body -> term option

type global_decl =
| ConstantDecl of constant_body
| InductiveDecl of mutual_inductive_body

val global_decl_rect :
  (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl ->
  'a1

val global_decl_rec :
  (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl ->
  'a1

val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

type global_declarations = (kername * global_decl) list

type program = global_declarations * term
