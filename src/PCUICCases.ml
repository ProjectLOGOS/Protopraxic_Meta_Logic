open BasicAst
open Datatypes
open Kernames
open List0
open PCUICAst
open Universes0

(** val ind_predicate_context :
    inductive -> PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context **)

let ind_predicate_context ind mdecl idecl =
  let ictx =
    PCUICEnvironment.expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
      (PCUICEnvironment.ind_indices idecl)
  in
  let indty =
    mkApps (Coq_tInd (ind,
      (abstract_instance (PCUICEnvironment.ind_universes mdecl))))
      (PCUICEnvironment.to_extended_list
        (app_context
          (PCUICEnvironment.smash_context []
            (PCUICEnvironment.ind_params mdecl)) ictx))
  in
  let inddecl = { decl_name = { binder_name = (Coq_nNamed
    (PCUICEnvironment.ind_name idecl)); binder_relevance =
    (PCUICEnvironment.ind_relevance idecl) }; decl_body = None; decl_type =
    indty }
  in
  inddecl :: ictx

(** val inst_case_context :
    term list -> Instance.t -> PCUICEnvironment.context ->
    PCUICEnvironment.context **)

let inst_case_context params puinst0 pctx =
  PCUICEnvironment.subst_context (rev params) O
    (subst_instance PCUICEnvironment.subst_instance_context puinst0 pctx)

(** val inst_case_predicate_context :
    term predicate -> PCUICEnvironment.context **)

let inst_case_predicate_context p =
  inst_case_context p.pparams p.puinst p.pcontext

(** val inst_case_branch_context :
    term predicate -> term branch -> PCUICEnvironment.context **)

let inst_case_branch_context p br =
  inst_case_context p.pparams p.puinst br.bcontext

(** val iota_red :
    nat -> term predicate -> term list -> term branch -> term **)

let iota_red npar p args br =
  subst (rev (skipn npar args)) O
    (PCUICEnvironment.expand_lets (inst_case_branch_context p br) br.bbody)

(** val cstr_branch_context :
    inductive -> PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.constructor_body -> PCUICEnvironment.context **)

let cstr_branch_context ind mdecl cdecl =
  PCUICEnvironment.expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
    (PCUICEnvironment.subst_context
      (inds ind.inductive_mind
        (abstract_instance (PCUICEnvironment.ind_universes mdecl))
        (PCUICEnvironment.ind_bodies mdecl))
      (length (PCUICEnvironment.ind_params mdecl))
      (PCUICEnvironment.cstr_args cdecl))

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (fix_subst mfix) O d.dbody))
  | None -> None

(** val cofix_subst : term mfixpoint -> term list **)

let cofix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tCoFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_cofix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_cofix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (cofix_subst mfix) O d.dbody))
  | None -> None
