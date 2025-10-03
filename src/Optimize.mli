open All_Forall
open BasicAst
open Datatypes
open EAst
open ELiftSubst
open EPrimitive
open ExAst
open Kernames
open List0
open MCList
open MCOption
open MCProd
open Nat0
open PeanoNat
open ReflectEq
open ResultMonad
open Utils
open Bytestring

val map_subterms : (term -> term) -> term -> term

type bitmask = bool list

val count_zeros : bitmask -> nat

val count_ones : bitmask -> nat

val trim_start : bool -> bitmask -> bitmask

val trim_end : bool -> bitmask -> bitmask

type mib_masks = { param_mask : bitmask;
                   ctor_masks : ((nat * nat) * bitmask) list }

val get_mib_masks : (kername * mib_masks) list -> kername -> mib_masks option

val dearg_single : bitmask -> term -> term list -> term

val get_branch_mask : mib_masks -> nat -> nat -> bitmask

val get_ctor_mask : (kername * mib_masks) list -> inductive -> nat -> bitmask

val get_const_mask : (kername * bitmask) list -> kername -> bitmask

val masked : bitmask -> 'a1 list -> 'a1 list

val dearg_lambdas : bitmask -> term -> term

val dearg_branch_body_rec : nat -> bitmask -> term -> nat * term

val complete_ctx_mask : bitmask -> name list -> bitmask

val dearg_branch_body : bitmask -> name list -> term -> name list * term

val dearged_npars : mib_masks option -> nat -> nat

val dearg_case_branch :
  mib_masks -> inductive -> nat -> (name list * term) -> name list * term

val dearg_case_branches :
  mib_masks option -> inductive -> (name list * term) list -> (name
  list * term) list

val dearged_proj_arg : mib_masks option -> inductive -> nat -> nat

val dearg_case :
  (kername * mib_masks) list -> inductive -> nat -> term -> (name
  list * term) list -> term

val dearg_proj :
  (kername * mib_masks) list -> inductive -> nat -> nat -> term -> term

val dearg_aux :
  (kername * mib_masks) list -> (kername * bitmask) list -> term list -> term
  -> term

val dearg :
  (kername * mib_masks) list -> (kername * bitmask) list -> term -> term

val dearg_cst_type_top : bitmask -> box_type -> box_type

val dearg_cst :
  (kername * mib_masks) list -> (kername * bitmask) list -> kername ->
  constant_body -> constant_body

val dearg_ctor :
  bitmask -> bitmask -> ((ident * (name * box_type) list) * nat) ->
  (ident * (name * box_type) list) * nat

val dearg_oib : mib_masks -> nat -> one_inductive_body -> one_inductive_body

val dearg_mib :
  (kername * mib_masks) list -> kername -> mutual_inductive_body ->
  mutual_inductive_body

val dearg_decl :
  (kername * mib_masks) list -> (kername * bitmask) list -> kername ->
  global_decl -> global_decl

val dearg_env :
  (kername * mib_masks) list -> (kername * bitmask) list -> global_env ->
  global_env

val is_dead : nat -> term -> bool

val valid_dearg_mask : bitmask -> term -> bool

val valid_dearg_mask_branch : nat -> bitmask -> term -> bool

val valid_case_masks :
  (kername * mib_masks) list -> inductive -> nat -> (name list * term) list
  -> bool

val valid_proj : (kername * mib_masks) list -> inductive -> nat -> nat -> bool

val valid_cases : (kername * mib_masks) list -> term -> bool

val forallbi : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool

val check_oib_masks : mib_masks -> nat -> one_inductive_body -> bool

val valid_masks_decl :
  (kername * mib_masks) list -> (kername * bitmask) list ->
  ((kername * bool) * global_decl) -> bool

val valid_masks_env :
  (kername * mib_masks) list -> (kername * bitmask) list -> global_env -> bool

val is_expanded_aux :
  (kername * mib_masks) list -> (kername * bitmask) list -> nat -> term ->
  bool

val is_expanded :
  (kername * mib_masks) list -> (kername * bitmask) list -> term -> bool

val is_expanded_env :
  (kername * mib_masks) list -> (kername * bitmask) list -> global_env -> bool

val keep_tvar : type_var_info -> bool

val dearg_single_bt :
  type_var_info list -> box_type -> box_type list -> box_type

val get_inductive_tvars : global_env -> inductive -> type_var_info list

val debox_box_type_aux : global_env -> box_type list -> box_type -> box_type

val debox_box_type : global_env -> box_type -> box_type

val debox_type_constant : global_env -> constant_body -> constant_body

val reindex : type_var_info list -> box_type -> box_type

val debox_type_oib : global_env -> one_inductive_body -> one_inductive_body

val debox_type_mib :
  global_env -> mutual_inductive_body -> mutual_inductive_body

val debox_type_decl : global_env -> global_decl -> global_decl

val debox_env_types : global_env -> global_env

val clear_bit : nat -> bitmask -> bitmask

type analyze_state = bitmask * (kername * mib_masks) list

val set_used : analyze_state -> nat -> analyze_state

val new_vars : analyze_state -> nat -> analyze_state

val new_var : analyze_state -> analyze_state

val remove_vars : analyze_state -> nat -> analyze_state

val remove_var : analyze_state -> analyze_state

val update_mib_masks : analyze_state -> kername -> mib_masks -> analyze_state

val update_ind_ctor_mask :
  nat -> nat -> ((nat * nat) * bitmask) list -> (bitmask -> bitmask) ->
  ((nat * nat) * bitmask) list

val fold_lefti : (nat -> 'a1 -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1 -> 'a1

val analyze_top_level :
  (analyze_state -> term -> analyze_state) -> analyze_state -> nat -> term ->
  bitmask * analyze_state

val analyze : analyze_state -> term -> analyze_state

val decompose_TArr : box_type -> box_type list * box_type

val is_box_or_any : box_type -> bool

val analyze_constant :
  constant_body -> (kername * mib_masks) list ->
  bitmask * (kername * mib_masks) list

type dearg_set = { const_masks : (kername * bitmask) list;
                   ind_masks : (kername * mib_masks) list }

val analyze_env : (kername -> bitmask option) -> global_env -> dearg_set

val trim_const_masks : (kername * bitmask) list -> (kername * bitmask) list

val trim_ctor_masks :
  ((nat * nat) * bitmask) list -> ((nat * nat) * bitmask) list

val trim_mib_masks : mib_masks -> mib_masks

val trim_ind_masks : (kername * mib_masks) list -> (kername * mib_masks) list

val throwIf : bool -> String.t -> (unit, String.t) result
