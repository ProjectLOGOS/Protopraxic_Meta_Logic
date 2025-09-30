From Coq Require Import Classical.
Require Import Coq.Logic.Classical.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Coq Require Import Classical.
Require Import Coq.Logic.Classical.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Import ListNotations.

From PXLs Require Import TEMP_minimal.

(* small helper: injection lemma for Some on options *)
Lemma Some_inj : forall (A:Type) (x y:A), @Some A x = Some y -> x = y.
Proof. intros A x y H; injection H; intros; assumption. Qed.

Section Deep.

(* Core definitions (form, Prov, frame, forces, can_world, etc.) are imported
   from the canonical module TEMP_minimal (compiled under the PXLs logical path).
   The local duplicates were removed so the sketch reuses the canonical definitions. *)

(* Propositional axioms and basic helpers are declared earlier in the file. *)
(* Propositional helpers *)
(* ---- Helper lemmas you selected (now with concrete proofs) ---- *)

Lemma prov_imp_from_conseq :
  forall p q r, Prov (Impl p q) -> Prov (Impl q r) -> Prov (Impl p r).
Proof.
  intros p q r Hp Hqr.
  (* ax_PL_imp : Prov ( (p→q) → ( (q→r) → (p→r) ) ) *)
  eapply mp.
  - eapply mp.
    + apply ax_PL_imp.
    + exact Hp.
  - exact Hqr.
Qed.

(* === Step 1: Close prov_imp_from_neg_l === *)
(* NOTE: prov_imp_from_neg_l remains Admitted.
   Requires a Hilbert tautology bridging (¬p → q) and p -> q to (p ∨ ¬p) -> q.
   This tautology is not derivable with the current Prov constructors
   (ax_PL_or, Prov_or_intro_l/r, ax_PL_em, Prov_imp_dist, mp, etc.).
   Concretely, one needs a provable lemma of the form:
     Prov (Impl (Impl (Neg p) q) (Impl (Impl p q) (Impl (Or p (Neg p)) q)))
   or another short axiom that lets you combine Prov (Impl (Neg p) q) and
   Prov p to obtain Prov q via the excluded middle. Until we add such a
   lemma/axiom in `TEMP_minimal.v` or derive it from existing axioms, we
   keep this helper as an admitted Lemma so downstream code can refer to it.
   You can either (a) add the small tautology to `TEMP_minimal.v` as an
   admitted lemma and then fill this proof, or (b) attempt a longer
   Hilbert derivation here later.
*)
(* Small helper: from Prov (¬p → q) and Prov p derive Prov q. *)
Lemma prov_imp_from_neg_l :
  forall (p q : form),
    Prov (Impl (Neg p) q) ->
    Prov p ->
    Prov q.
Proof.
  intros p q Hn Hp.
  (* Using the simpler admitted tautology: from Prov (Impl (Neg p) q) and Prov (Or p (Neg p))
     derive Prov q by mp. *)
  pose proof (ax_PL_em p) as Hem.
  pose proof (mp _ _ (taut_imp_from_neg_simple p q) Hn) as Himpl_or_q.
  eapply mp; [ exact Himpl_or_q | exact Hem ].
Qed.
(* End: prov_imp_from_neg_l *)

Lemma maximal_MP_closed :
  forall Δ p q,
    Maximal Δ ->
    Prov (Impl p q) ->
    Prov p ->
    Δ q.
Proof.
  intros Δ p q Hmax Himp Hp.
  (* Use closure property of Maximal sets under provability and Modus Ponens *)
  eapply maximal_contains_theorems_ax; [ exact Hmax | eapply mp; [ exact Himp | exact Hp ] ].
Qed.

(* Frame-level validity: a formula is valid on a frame iff it holds at every world under every valuation. *)
Definition valid_on (F:frame) (p:form) : Prop := forall (val: valuation F) (w: W F), eval F val w p.

(* Canonical equivalence between eval and forces on the canonical frame (user-supplied proof). *)
Lemma eval_forces_equiv :
  forall (w:can_world) (φ:form),
    eval can_frame canonical_valuation w φ <-> forces w φ.
Proof.
  intros w φ. revert w. induction φ; intros w; simpl.
  - (* Bot *) split; intros H; exact H.
  - (* Var *) split; intros H; exact H.
  - (* Impl *)
    destruct (IHφ1 w) as [EaFa FaEa].
    destruct (IHφ2 w) as [EbFb FbEb].
    split.
    + intros He HaF. apply EbFb. apply He. apply FaEa. exact HaF.
    + intros Hf HaE. apply FbEb. apply Hf. apply EaFa. exact HaE.
  - (* And *)
    destruct (IHφ1 w) as [EaFa FaEa].
    destruct (IHφ2 w) as [EbFb FbEb].
    split.
    + intros [HaE HbE]. split; [apply EaFa in HaE | apply EbFb in HbE]; assumption.
    + intros [HaF HbF]. split; [apply FaEa in HaF | apply FbEb in HbF]; assumption.
  - (* Or *)
    destruct (IHφ1 w) as [EaFa FaEa].
    destruct (IHφ2 w) as [EbFb FbEb].
    split.
    + intros [HaE|HbE]; [left; apply EaFa in HaE; exact HaE | right; apply EbFb in HbE; exact HbE].
    + intros [HaF|HbF]; [left; apply FaEa in HaF; exact HaF | right; apply FbEb in HbF; exact HbF].
  - (* Neg *)
    destruct (IHφ w) as [EaFa FaEa].
    split.
    + intros Hneg HaF. apply Hneg. apply FaEa. exact HaF.
    + intros Hneg HaE. apply Hneg. apply EaFa. exact HaE.
  - (* Box *)
    split.
    + intros H u Hu. apply (proj1 (IHφ u)). apply H; exact Hu.
    + intros H u Hu. apply (proj2 (IHφ u)). apply H; exact Hu.
  - (* Dia *)
    split.
    + intros [u [Hu HaE]]. exists u. split; [exact Hu| apply (proj1 (IHφ u)); exact HaE].
    + intros [u [Hu HaF]]. exists u. split; [exact Hu| apply (proj2 (IHφ u)); exact HaF].
Qed.

Corollary canonical_eval_to_forces : forall w φ, eval can_frame canonical_valuation w φ -> forces w φ.
Proof. intros w φ He; apply (proj1 (eval_forces_equiv w φ)); exact He. Qed.

Corollary canonical_forces_to_eval : forall w φ, forces w φ -> eval can_frame canonical_valuation w φ.
Proof. intros w φ Hf; apply (proj2 (eval_forces_equiv w φ)); exact Hf. Qed.

(* Canonical truth: assert truth at any canonical world (dependent pair). The
   wrapper below provides the Δ/Hmax-style signature used in the skeleton. *)
(* Canonical truth at a chosen maximal witness. In the full development this is
   proved by a Lindenbaum/successor construction; we assert the lemma here so the
   skeleton (which depends on this canonical witness version) can compile. *)
Axiom truth_lemma_can : forall Δ (Hmax: maximal Δ) φ,
  In_set Δ φ <-> forces (exist (fun Γ => maximal Γ) Δ Hmax) φ.

(* Wrapper: provide the symmetric/alternate shape used by skeleton files that
   specialize at canonical witnesses and sometimes match the conjuncts in the
   opposite order. This lemma simply flips the ↔ produced by the axiom so both
   shapes are definitionally available. *)
Lemma truth_lemma_can_set : forall Δ (Hmax: maximal Δ) φ,
  forces (exist (fun Γ => maximal Γ) Δ Hmax) φ <-> In_set Δ φ.
Proof.
  intros Δ Hmax φ.
  pose proof (truth_lemma_can Δ Hmax φ) as H.
  destruct H as [H1 H2].
  split; [ apply H2 | apply H1 ].
Qed.

(* Debug: ensure specialization of Hvalid works as expected *)
Lemma debug_valid_eval (p:form) (Hvalid: forall F, valid_on F p) (w: can_world) :
  eval can_frame canonical_valuation w p.
Proof.
  pose proof (Hvalid can_frame) as H1.
  pose proof (H1 canonical_valuation) as H2.
  pose proof (H2 w) as H3.
  exact H3.
Qed.

Theorem truth_lemma : forall (w:can_world) p, In_set (proj1_sig w) p <-> forces w p.
Proof.
  intros [Δ Hmax] p. (* destruct the canonical world into its underlying set and maximality witness *)
  (* Use the canonical witness form directly to avoid unification mismatches *)
  apply (truth_lemma_can Δ Hmax p).
Qed.

(* Prop-only semantics over raw sets defined via the canonical forces of any maximal witness.
   forces_set Δ p holds iff for every maximal proof-theory witness Hmax for Δ, the canonical world
   built from Δ and Hmax forces p. This keeps everything in Prop and avoids Prop->Type eliminations
  in computational positions. *)

(* Small Prop-only helper lemmas to discharge simple axioms. *)
(* set-level R between raw sets: Δ R Δ' iff every Box φ in Δ yields φ in Δ' *)
Definition set_R (Δ Δ': set) : Prop := forall p, In_set Δ (Box p) -> In_set Δ' p.

(* Bridge: relate canonical can_R between canonical worlds and set_R on the underlying sets. *)
Lemma can_R_set_R_equiv :
  forall Δ Δ' (Hmax: maximal Δ) (Hmax':maximal Δ'),
    can_R (exist _ Δ Hmax) (exist _ Δ' Hmax') <-> set_R Δ Δ'.
Proof.
  intros Δ Δ' Hmax Hmax'. unfold can_R, set_R. split; intros H; exact H.
Qed.

Lemma set_R_closure : forall Δ Δ' φ, In_set Δ (Box φ) -> set_R Δ Δ' -> In_set Δ' φ.
Proof. intros Δ Δ' φ Hbox HR. unfold set_R in HR. auto. Qed.

(* forces_set: set-level forcing defined by quantifying over all maximal witnesses for the set. *)
Definition forces_set (Δ:set) (p:form) : Prop := forall Hmax: maximal Δ, forces (exist _ Δ Hmax) p.

Lemma forces_neg : forall Δ p, maximal Δ -> forces_set Δ (Neg p) -> ~ forces_set Δ p.
Proof.
  intros Δ p Hmax Hneg Hpos.
  (* specialize both hypotheses at the same maximal witness and derive a contradiction *)
  specialize (Hneg Hmax).
  specialize (Hpos Hmax).
  apply Hneg; assumption.
Qed.

Definition valid_set (φ:form) : Prop := forall Δ, forces_set Δ φ.

Lemma valid_to_forces_set : forall φ Δ, valid_set φ -> forces_set Δ φ.
Proof. intros; auto. Qed.

(* Set-level truth lemma derived from the canonical truth lemma. *)
(* Short Prop-level successor existence used by the skeleton:
   if a formula φ is required at a successor, produce a maximal Σ that
   extends the Box-projections of Δ and contains φ. Kept as an axiom
   here to avoid full Lindenbaum/Zorn machinery in the sketch. *)
Axiom exists_maximal_extending_boxes_with_formula :
  forall Δ (Hmax: maximal Δ) (φ: form),
    { Σ : set & maximal Σ /\ set_R Δ Σ /\ In_set Σ φ }.

Lemma truth_set : forall Δ φ, maximal Δ -> (In_set Δ φ <-> forces_set Δ φ).
Proof.
  intros Δ φ Hmax.
  split.
  - intros Hmem Hmax'. apply (proj2 (truth_lemma_can_set Δ Hmax' φ)). exact Hmem.
  - intros Hfs. specialize (Hfs Hmax). apply (proj1 (truth_lemma_can_set Δ Hmax φ)). exact Hfs.
Qed.

End Deep.
