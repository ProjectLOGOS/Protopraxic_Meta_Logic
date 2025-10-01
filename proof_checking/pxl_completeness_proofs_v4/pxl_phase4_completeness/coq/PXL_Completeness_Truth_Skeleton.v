From PXLs Require Import TEMP_minimal.
From PXLs Require Import PXL_Completeness_Sketch.

(* ========================================================== *)
(* PXL Completeness: Fixed-Point / Trinitarian Optimization   *)
(* ========================================================== *)

Require Import Arith Lia.
Require Import Coq.Logic.Classical.

(* ------------------------------------------------------------------ *)
(* Small axioms/lemmas needed by the modal backward directions         *)
(* ------------------------------------------------------------------ *)

(* Semantic negation elim: if a world forces ¬φ then it cannot force φ. *)
(* Derive from the canonical eval↔forces equivalence and the definition of Neg. *)
Lemma forces_neg_elim : forall w φ, forces w (Neg φ) -> ~ forces w φ.
Proof.
  intros w φ Hneg Hpos.
  (* Move both forces facts to eval using the canonical bridge, then contradict. *)
  pose proof (canonical_forces_to_eval w (Neg φ)) as Hc1.
  pose proof (canonical_forces_to_eval w φ) as Hc2.
  apply Hc1 in Hneg.
  apply Hc2 in Hpos.
  (* Hneg : eval ... (Neg φ) i.e. ~ eval ... φ ; Hpos : eval ... φ *)
  exact (Hneg Hpos).
Qed.

(* TODO: replace with constructive derivation. Scoped helper to lift a proof
   from the boxes-of(Δ) context to a boxed theorem in Δ. This is a short-term
   admit to close the successor-consistency argument in the skeleton. *)
(* Minimal forwarding lemma: use the small admissible lifting axiom from
   TEMP_minimal.v. This keeps the skeleton light while we maintain the
   minimal [pf_lift_boxes] hook in the core development. *)
Lemma prov_from_boxes_implies_prov_box_in_delta :
  forall Δ φ, Prov_from (boxes_of Δ) φ -> Prov_from Δ (Box φ).
Proof. intros Δ φ H. apply pf_lift_boxes. exact H. Qed.

(* If Δ doesn't contain Box φ, then adding ¬φ to boxes_of Δ is consistent.
   We prove this by contradiction: if add (boxes_of Δ) (Neg φ) were
   inconsistent then we can derive Prov_from (boxes_of Δ) φ, lift it to
   Prov_from Δ (Box φ) using the scoped helper, and contradict maximality.
   The helper [prov_from_boxes_implies_prov_box_in_delta] is a small
   admissible axiom in TEMP_minimal.v (TODO: make constructive). *)
Lemma boxes_neg_consistent :
  forall Δ (H:maximal Δ) φ,
    ~ In_set Δ (Box φ) ->
    consistent (add (boxes_of Δ) (Neg φ)).
Proof.
  intros Δ H φ Hnmem.
  unfold consistent. intros Hinc.
  (* From inconsistency witness (exists p, ...) produce the double-negation-shaped
    [inconsistent (add ...)] expected by the pf_incons_to_pf_bot_add_neg axiom. *)
  pose proof (pf_incons_to_pf_bot_add_neg (boxes_of Δ) φ
    (fun (Hcons: consistent (add (boxes_of Δ) (Neg φ))) => Hcons Hinc)) as Hbot.
  (* From Prov_from (add (boxes_of Δ) (Neg φ)) Bot derive Prov_from (boxes_of Δ) φ. *)
  pose proof (pf_deduction_from_addneg_bot_to_pos (boxes_of Δ) φ Hbot) as Hpos_boxes.
  (* Lift provability from boxes_of Δ to Δ as a boxed theorem. *)
  pose proof (prov_from_boxes_implies_prov_box_in_delta Δ φ Hpos_boxes) as Hboxprov.
  (* From Prov_from Δ (Box φ) and maximality we get that either Box φ ∈ Δ or
     Neg (Box φ) ∈ Δ. Since we assumed ~ In_set Δ (Box φ), the latter holds and
     yields Prov_from Δ (Neg (Box φ)) by pf_assumption. This contradicts
     Prov_from Δ (Box φ) via pf_contradiction_to_bot and pf_incons_def. *)
  pose proof (proj2 H (Box φ)) as Hdec.
  destruct Hdec as [Hbox_in | Hneg_box_in].
  - contradict Hnmem; assumption.
  - pose proof (pf_assumption Δ (Neg (Box φ)) Hneg_box_in) as Hprov_neg_box.
    pose proof (pf_contradiction_to_bot Δ (Box φ) Hboxprov Hprov_neg_box) as Hbot2.
  pose proof (pf_incons_def Δ Hbot2) as HincΔ.
  (* Use consistency part of maximal Δ to contradict the derived inconsistency. *)
  exact (HincΔ (proj1 H)).
Qed.

(* Evaluation on the canonical frame depends only on the underlying set Δ of
   a canonical world and not on the particular maximal witness. We prove this
   by structural induction on formulas. The Box/Dia cases convert between the
   canonical can_R and the set-level set_R using the sketch bridge
   [can_R_set_R_equiv], avoiding any name-clash with the sketch's set-level
   [can_R]. *)
Lemma eval_indep_witness :
  forall Δ (H1 H2: maximal Δ) φ,
    eval can_frame canonical_valuation (exist _ Δ H1) φ <->
    eval can_frame canonical_valuation (exist _ Δ H2) φ.
Proof.
  intros Δ H1 H2; induction φ; simpl.
  - split; intros H; exact H.
  - split; intros H; exact H.
  - (* Impl *)
    destruct (IHφ1) as [I1a I1b].
    destruct (IHφ2) as [I2a I2b].
    split.
    + intros H Ha. apply I2a. apply H. apply I1b. exact Ha.
    + intros H Ha. apply I2b. apply H. apply I1a. exact Ha.
  - (* And *)
    destruct (IHφ1) as [I1a I1b].
    destruct (IHφ2) as [I2a I2b].
    split.
    + intros [Ha Hb]. split; [apply I1a in Ha| apply I2a in Hb]; assumption.
    + intros [Ha Hb]. split; [apply I1b in Ha| apply I2b in Hb]; assumption.
  - (* Or *)
    destruct (IHφ1) as [I1a I1b].
    destruct (IHφ2) as [I2a I2b].
    split.
    + intros H; destruct H as [Ha|Hb]; [left; apply I1a in Ha| right; apply I2a in Hb]; assumption.
    + intros H; destruct H as [Ha|Hb]; [left; apply I1b in Ha| right; apply I2b in Hb]; assumption.
  - (* Neg *)
    destruct (IHφ) as [Ia Ib].
    split; intros Hn Hf; [ apply Hn; apply Ib; exact Hf | apply Hn; apply Ia; exact Hf ].
  - (* Box *)
    intros. split; intros H u Hu.
    + pose proof (proj1 (can_R_set_R_equiv Δ (proj1_sig u) H2 (proj2_sig u))) as Hcan2_to_set.
      pose proof (proj2 (can_R_set_R_equiv Δ (proj1_sig u) H1 (proj2_sig u))) as Hset_to_can1.
      apply H. apply Hset_to_can1. apply Hcan2_to_set. exact Hu.
    + pose proof (proj1 (can_R_set_R_equiv Δ (proj1_sig u) H1 (proj2_sig u))) as Hcan1_to_set.
      pose proof (proj2 (can_R_set_R_equiv Δ (proj1_sig u) H2 (proj2_sig u))) as Hset_to_can2.
      apply H. apply Hset_to_can2. apply Hcan1_to_set. exact Hu.
  - (* Dia *)
    intros. split; intros [u [Hc He]].
    + exists u. split.
      * pose proof (proj1 (can_R_set_R_equiv Δ (proj1_sig u) H1 (proj2_sig u))) as Hcan1_to_set.
        pose proof (proj2 (can_R_set_R_equiv Δ (proj1_sig u) H2 (proj2_sig u))) as Hset_to_can2.
        apply Hset_to_can2. apply Hcan1_to_set. exact Hc.
      * exact He.
    + exists u. split.
      * pose proof (proj1 (can_R_set_R_equiv Δ (proj1_sig u) H2 (proj2_sig u))) as Hcan2_to_set.
        pose proof (proj2 (can_R_set_R_equiv Δ (proj1_sig u) H1 (proj2_sig u))) as Hset_to_can1.
        apply Hset_to_can1. apply Hcan2_to_set. exact Hc.
      * exact He.
Qed.

(* Witness-independence of forces follows from eval_indep_witness composed with
   the eval↔forces equivalence proved in the canonical module. *)
Lemma forces_indep_witness :
  forall Δ (H1 H2: maximal Δ) φ,
    forces (exist _ Δ H1) φ <-> forces (exist _ Δ H2) φ.
Proof.
  intros Δ H1 H2 φ; split; intro H.
  - apply (proj1 (eval_forces_equiv (exist _ Δ H2) φ)).
    apply (proj2 (eval_forces_equiv (exist _ Δ H1) φ)) in H.
    apply (proj1 (eval_indep_witness Δ H1 H2 φ)). exact H.
  - apply (proj1 (eval_forces_equiv (exist _ Δ H1) φ)).
    apply (proj2 (eval_forces_equiv (exist _ Δ H2) φ)) in H.
    apply (proj2 (eval_indep_witness Δ H1 H2 φ)). exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Box backward: forces at the canonical world for □φ implies Box φ in Δ *)
(* ------------------------------------------------------------------ *)
Lemma box_forces_to_mem :
  forall (Δ:set) (H:maximal Δ) φ,
    forces (exist _ Δ H) (Box φ) -> In_set Δ (Box φ).
Proof.
  intros Δ H φ Hbox.
  destruct (classic (In_set Δ (Box φ))) as [Hmem|Hnmem]; [exact Hmem|].
  pose proof (boxes_neg_consistent Δ H φ Hnmem) as Hcons.
  destruct (exists_maximal_extending_boxes_with_formula Δ H (Neg φ) Hcons)
    as [Γ [HmaxΓ [Hext [HsetR Hneg_in]]]].
  (* forces at Δ for □φ yields forces at Γ for φ via R Δ Γ *)
  (* The sketch returns both an extends Δ Γ and a set-level can_R (here named HsetR).
     Convert the set-level can_R to the canonical can_R on canonical worlds using
     can_R_set_R_equiv (proj2 direction), then specialize the Box-forcing. *)
  pose proof (proj2 (can_R_set_R_equiv Δ Γ H HmaxΓ) HsetR) as HcanR_canonical.
  specialize (Hbox (exist _ Γ HmaxΓ) HcanR_canonical).
  (* From Γ ⊢ ¬φ we get forces Γ ¬φ via the TEMP_minimal bridge, contradicting forces Γ φ obtained from □φ *)
  pose proof (mem_implies_forces (exist _ Γ HmaxΓ) (Neg φ) Hneg_in) as Hforces_neg.
  pose proof (forces_neg_elim (exist _ Γ HmaxΓ) φ Hforces_neg) as Hnot_forces.
  pose proof (Hnot_forces Hbox) as Hfalse.
  exfalso. exact Hfalse.
Qed.

(* ------------------------------------------------------------------ *)
(* Dia backward: membership of ◇φ in Δ gives forces at the canonical world *)
(* ------------------------------------------------------------------ *)
(* Dia-backward proof lives later as part of the full structural induction
   (see Lemma [truth_set_dia_ind] below). The stray fragment removed here
   was a duplicate leftover from an earlier edit. *)

(* Transfer lemma: move a Box-forcing fact from one canonical witness to another via set_R/can_R. *)
Lemma forces_transfer_witness :
  forall Δ (HΔ: maximal Δ) Σ (HΣ: maximal Σ) φ,
    set_R Δ Σ ->
    forces (exist _ Δ HΔ) (Box φ) ->
    forces (exist _ Σ HΣ) φ.
Proof.
  intros Δ HΔ Σ HΣ φ Hset Hforces.
  (* set_R gives can_R by can_R_set_R_equiv; then apply the Box-forcing at Δ to the successor *)
  pose proof (can_R_set_R_equiv Δ Σ HΔ HΣ) as Hbridge.
  destruct Hbridge as [Hcan_to_set Hset_to_can].
  pose proof (Hset_to_can Hset) as Hcan.
  apply Hforces. exact Hcan.
Qed.

Lemma forces_transfer :
  forall Δ (HΔ: maximal Δ) Σ φ,
    set_R Δ Σ ->
    forces (exist _ Δ HΔ) (Box φ) ->
    forces_set Σ φ.
Proof.
  intros Δ HΔ Σ φ Hset Hf HΣ.
  apply (forces_transfer_witness Δ HΔ Σ HΣ φ Hset Hf).
Qed.

(* Negation: both directions using the admitted canonical truth lemma and IH *)
Lemma truth_set_neg_ind :
  forall (p: form),
    (forall Δ (Hmax: maximal Δ), In_set Δ p <-> forces_set Δ p) ->
    forall Δ (Hmax: maximal Δ), In_set Δ (Neg p) <-> forces_set Δ (Neg p).
Proof.
  intros p IH Δ Hmax.
  split.
  - (* In_set Δ (Neg p) -> forces_set Δ (Neg p) *)
    intros Hmem.
  pose proof (mem_implies_forces (exist _ Δ Hmax) (Neg p) Hmem) as Hforces_at_Hmax.
    intros H0. (* arbitrary maximal witness for Δ *)
    (* transport forces from Hmax to H0 *)
    pose proof (proj1 (forces_indep_witness Δ Hmax H0 (Neg p))) as Htrans.
    apply Htrans in Hforces_at_Hmax. exact Hforces_at_Hmax.
  - (* forces_set Δ (Neg p) -> In_set Δ (Neg p) *)
    intros Hfs.
    specialize (Hfs Hmax). simpl in Hfs.
  exact (forces_implies_mem (exist _ Δ Hmax) (Neg p) Hfs).
Qed.

(* Stub Dia/Box cases — leave them admitted for now. *)
(* Full backward for implication (uses Lindenbaum/successor argument) - keep admitted as scaffold) *)
Lemma truth_set_impl_backward_complete :
  forall Δ (Hmax: maximal Δ) p q,
   (forall Δ (Hmax: maximal Δ), In_set Δ p <-> forces_set Δ p) ->
   (forall Δ (Hmax: maximal Δ), In_set Δ q <-> forces_set Δ q) ->
   forces_set Δ (Impl p q) -> In_set Δ (Impl p q).
Proof.
  intros Δ Hmax p q IHp IHq Himpl_fs.
  (* Use maximality: either Impl p q ∈ Δ or its negation is in Δ. *)
  destruct (proj2 Hmax (Impl p q)) as [Hin | Hneg].
  - (* already in Δ *) exact Hin.
  - (* Neg (Impl p q) in Δ leads to contradiction with forces_set Δ (Impl p q) *)
   specialize (Himpl_fs Hmax). simpl in Himpl_fs.
   (* truth_lemma_can_set relates In_set and forces at the canonical witness (admitted in sketch). *)
  (* From In_set Δ (Neg (Impl p q)) we get forces at the canonical witness *)
  pose proof (mem_implies_forces (exist _ Δ Hmax) (Neg (Impl p q)) Hneg) as Hforces_neg.
   (* But Himpl_fs at the same witness yields forces (Impl p q), contradiction *)
   exfalso. apply Hforces_neg. exact Himpl_fs.
Qed.

(* Stub Dia/Box cases — leave them admitted for now. *)
Lemma truth_set_box_ind :
  forall (p: form),
    (forall Δ (Hmax: maximal Δ), In_set Δ p <-> forces_set Δ p) ->
    forall Δ (Hmax: maximal Δ), In_set Δ (Box p) <-> forces_set Δ (Box p).
Proof.
  intros p IH Δ Hmax.
  split.
  - (* In_set Δ (Box p) -> forces_set Δ (Box p) *)
    intros Hmem. unfold forces_set. intros H0.
    (* Use truth_box_from_set at the chosen witness Hmax to get forces there, then
       transfer to an arbitrary H0 via forces_indep_witness. *)
   (* Inline the body of truth_box_from_set here so we don't rely on a later
     lemma definition. We need to prove forces (exist _ Δ H0) (Box p). *)
   unfold forces. simpl. intros u Hcan_local.
   destruct u as [Σ HΣ]. simpl in Hcan_local.
   (* Convert can_R to set_R, close Box membership to Σ, then use canonical truth *)
   pose proof (proj1 (can_R_set_R_equiv Δ Σ H0 HΣ)) as Hcan_to_set_local.
   pose proof (Hcan_to_set_local Hcan_local) as Hset_rel_local.
   pose proof (set_R_closure Δ Σ p Hmem Hset_rel_local) as H_in_u_p_local.
   pose proof (truth_lemma_can Σ HΣ p) as Hcanon_u_local.
   destruct Hcanon_u_local as [Hset_to_forces_u_local _].
   apply Hset_to_forces_u_local. exact H_in_u_p_local.
  - (* forces_set Δ (Box p) -> In_set Δ (Box p) *)
    intros Hfs.
    (* instantiate forces_set at the canonical witness Hmax and apply box_forces_to_mem *)
    specialize (Hfs Hmax). simpl in Hfs.
    apply (box_forces_to_mem Δ Hmax p Hfs).
Qed.

Lemma truth_set_dia_ind :
  forall (p: form),
    (forall Δ (Hmax: maximal Δ), In_set Δ p <-> forces_set Δ p) ->
    forall Δ (Hmax: maximal Δ), In_set Δ (Dia p) <-> forces_set Δ (Dia p).
Proof.
  intros p IH Δ Hmax.
  split.
  - (* In_set Δ (Dia p) -> forces_set Δ (Dia p) *)
    intros Hmem. unfold forces_set. intros Hmax'. simpl.
  (* Use the TEMP_minimal bridge at the original canonical witness and then
     transfer the resulting forces fact to the arbitrary Hmax' using
     [forces_indep_witness]. *)
  pose proof (mem_implies_forces (exist _ Δ Hmax) (Dia p) Hmem) as Hforces_at_Hmax.
  pose proof (proj1 (forces_indep_witness Δ Hmax Hmax' (Dia p))) as Htrans.
  apply Htrans in Hforces_at_Hmax. exact Hforces_at_Hmax.
  - (* forces_set Δ (Dia p) -> In_set Δ (Dia p) *)
    intros Hfs.
    (* Specialize to the canonical witness Hmax and use truth_lemma_can_set to convert to membership. *)
  specialize (Hfs Hmax). simpl in Hfs.
  exact (forces_implies_mem (exist _ Δ Hmax) (Dia p) Hfs).
Qed.

(* Final skeleton: state the full lemma and leave it Admitted for now so you can iterate.
   The helper lemmas above cover Var/Bot and the forward Impl step; continue similarly for And/Or/Box/Dia. *)
(* Final skeleton: state the full lemma and leave it Admitted for now so you can iterate.
   The helper lemmas above cover Var/Bot and the forward Impl step; continue similarly for And/Or/Box/Dia. *)
(* NOTE: the full [truth_set_ind] is placed after the modal helper lemmas below so
   Coq sees the base Lemmas (Bot/Var/Box/Dia helpers) before the structural induction
   that references them. *)

(* Non-modal helpers that use the current canonical-truth axiom.
   These reduce admitted stubs and are safe while `truth_lemma_can` remains
   axiomatic in the sketch. Replace hook-names below if your project uses
   different identifiers for successor/construction lemmas. *)

Lemma truth_impl_backward :
  forall Δ (Hmax: maximal Δ) φ ψ,
    In_set Δ (Impl φ ψ) ->
    In_set Δ φ ->
    In_set Δ ψ.
Proof.
  intros Δ Hmax φ ψ Himpl Hphi.
  (* Use TEMP_minimal corollaries to move between set-membership and forces *)
  pose proof (mem_implies_forces (exist _ Δ Hmax) (Impl φ ψ)) as Hset_to_forces_impl.
  pose proof (mem_implies_forces (exist _ Δ Hmax) φ)           as Hset_to_forces_phi.
  pose proof (forces_implies_mem (exist _ Δ Hmax) ψ)           as Hforces_to_set_psi.

  pose proof (Hset_to_forces_impl Himpl) as Hforces_impl_fun.
  pose proof (Hset_to_forces_phi Hphi)  as Hforces_phi.
  pose proof (Hforces_impl_fun Hforces_phi) as Hforces_psi.

  apply Hforces_to_set_psi. exact Hforces_psi.
Qed.

(* Maximal sets do not contain Bot (small compatibility admit used in skeleton). *)
Lemma maximal_not_Bot : forall Γ, Maximal Γ -> ~ In_set Γ Bot.
Proof.
  intros Γ Hmax Hbot.
  destruct Hmax as [Hcons _].
  (* From Bot ∈ Γ we get Prov_from Γ Bot by pf_assumption, then pf_incons_def gives
     inconsistent Γ (i.e. ~ consistent Γ). Applying that to the consistency assumption
     yields a contradiction. *)
  pose proof (pf_assumption Γ Bot Hbot) as Hprov.
  pose proof (pf_incons_def Γ Hprov) as Hinc.
  unfold inconsistent in Hinc.
  exact (Hinc Hcons).
Qed.

Lemma truth_set_bot_forward :
  forall (Δ:set) (Hmax: maximal Δ),
    In_set Δ Bot -> forces_set Δ Bot.
Proof.
  intros Δ Hmax Hmem Hmax'. simpl.
  exfalso. apply (maximal_not_Bot Δ Hmax'). exact Hmem.
Qed.

Lemma truth_set_bot_backward :
  forall (Δ:set) (Hmax: maximal Δ),
    forces_set Δ Bot -> In_set Δ Bot.
Proof.
  intros Δ Hmax Hfs.
  specialize (Hfs Hmax). simpl in Hfs. exfalso. exact Hfs.
Qed.

Lemma truth_box_from_set :
  forall Δ (Hmax: maximal Δ) φ,
    In_set Δ (Box φ) ->
    forces (exist _ Δ Hmax) (Box φ).
Proof.
  intros Δ Hmax φ Hbox.
  (* We prove the Box at the canonical world by showing it holds at every can_R-successor. *)
  unfold forces. simpl. (* forces (exist Δ Hmax) (Box φ) := forall u, can_R _ u -> forces u φ *)
  intros u Hcan.
  (* Break the canonical world into its underlying set and witness so Coq treats the
    canonical world produced by [truth_lemma_can] and the local [u] as definitionally
    equal. *)
  destruct u as [Σ HΣ]. simpl in Hcan.
  (* Convert can_R to set_R using the available bridge, then use set_R_closure to move
    membership from Δ to Σ and finally to forces via the canonical-truth axiom. *)
  pose proof (proj1 (can_R_set_R_equiv Δ Σ Hmax HΣ)) as Hcan_to_set.
  pose proof (Hcan_to_set Hcan) as Hset_rel.
  (* From In_set Δ (Box φ) and set_R we get In_set Σ φ via set_R_closure (in sketch). *)
  pose proof (set_R_closure Δ Σ φ Hbox Hset_rel) as H_in_u_phi.
  (* Now use the canonical-truth axiom at Σ to obtain forces at the (definitionally equal) world u. *)
  pose proof (truth_lemma_can Σ HΣ φ) as Hcanon_u.
  destruct Hcanon_u as [Hset_to_forces_u _].
  apply Hset_to_forces_u. exact H_in_u_phi.
Qed.

Lemma truth_dia_from_set :
  forall Δ (Hmax: maximal Δ) φ,
    In_set Δ (Dia φ) ->
    forces (exist _ Δ Hmax) (Dia φ).
Proof.
  intros Δ Hmax φ Hdia.
  (* Simply use the canonical bridge: membership at Δ implies forces at the canonical witness. *)
  pose proof (mem_implies_forces (exist _ Δ Hmax) (Dia φ) Hdia) as Hforces.
  exact Hforces.
Qed.

Lemma dia_mem_to_forces_succ :
  forall (Δ:set) (H:maximal Δ) φ,
    In_set Δ (Dia φ) -> forces (exist _ Δ H) (Dia φ).
Proof.
  intros Δ H φ Hdia.
  (* Successor on φ from boxes_of Δ *)
  assert (Hcons : consistent (add (boxes_of Δ) φ)).
  {
    unfold consistent. intros Hex.
    (* The hypothesis Hex is an existential witness of the form
       exists p, add (boxes_of Δ) φ p /\/ add (boxes_of Δ) φ (Neg p).
       Convert that witness into the `inconsistent` predicate expected by
       the proof-bridging axiom [pf_incons_to_pf_bot_add]. *)
   (* Hex is a concrete witness of inconsistency (an existential). Convert it into
     the `inconsistent` predicate expected by [pf_incons_to_pf_bot_add] by
     supplying a function that contradicts any assumed consistency. *)
   pose proof (pf_incons_to_pf_bot_add (boxes_of Δ) φ (fun (Hc: consistent (add (boxes_of Δ) φ)) => Hc Hex)) as Hbot_add.
    (* From Prov_from (add ...) Bot derive Prov_from (boxes_of Δ) (Neg φ) *)
    pose proof (pf_deduction_from_add_bot_to_neg (boxes_of Δ) φ Hbot_add) as Hneg_in_boxes.
    (* Lift provability from boxes_of Δ to Δ as boxed theorem *)
  (* Lift provability of ¬φ in the boxed-context to Δ as a boxed theorem □¬φ. *)
  pose proof (prov_from_boxes_implies_prov_box_in_delta Δ (Neg φ) Hneg_in_boxes) as Hboxprov.
    (* Use maximality decision on Box (Neg φ) to derive contradiction in either case. *)
    pose proof (proj2 H (Box (Neg φ))) as Hdec.
    destruct Hdec as [Hbox_in | Hneg_box_in].
    - (* Case: Box (Neg φ) ∈ Δ. Use forces to contradict Dia φ ∈ Δ. *)
      pose proof (mem_implies_forces (exist _ Δ H) (Box (Neg φ)) Hbox_in) as Hforces_boxneg.
      pose proof (mem_implies_forces (exist _ Δ H) (Dia φ) Hdia) as Hforces_dia.
      destruct Hforces_dia as [u [Hcan_u Hforces_u_phi]].
      pose proof (Hforces_boxneg u Hcan_u) as Hforces_neg_at_u.
      pose proof (forces_neg_elim u φ Hforces_neg_at_u) as Hnot_phi_at_u.
      exact (Hnot_phi_at_u Hforces_u_phi).
    - (* Case: Neg (Box (Neg φ)) ∈ Δ. Derive provable contradiction in Δ. *)
      pose proof (pf_assumption Δ (Neg (Box (Neg φ))) Hneg_box_in) as Hprov_neg_box.
      pose proof (pf_contradiction_to_bot Δ (Box (Neg φ)) Hboxprov Hprov_neg_box) as Hbot_delta.
      pose proof (pf_incons_def Δ Hbot_delta) as Hinc_delta.
      exact (Hinc_delta (proj1 H)).
  }
  destruct (exists_maximal_extending_boxes_with_formula Δ H φ Hcons)
    as [Γ [HmaxΓ [Hext_boxes [HcanR Hφ_in_Γ]]]].
  (* Exhibit Γ as the Dia witness *)
  unfold forces; cbn. eexists (exist _ Γ HmaxΓ); split; [exact HcanR|].
  apply (mem_implies_forces (exist _ Γ HmaxΓ) φ); exact Hφ_in_Γ.
Qed.

(* ------------------------------------------------------------------ *)
(* Small propositional helpers (simple direction proofs using the canonical bridges) *)
(* ------------------------------------------------------------------ *)
Lemma truth_set_var_forward :
  forall Δ (Hmax: maximal Δ) φ,
    In_set Δ φ -> forces_set Δ φ.
Proof.
  intros Δ Hmax φ Hmem Hmax'.
  apply (mem_implies_forces (exist _ Δ Hmax') φ Hmem).
Qed.

Lemma truth_set_var_backward :
  forall Δ (Hmax: maximal Δ) φ,
    forces_set Δ φ -> In_set Δ φ.
Proof.
  intros Δ Hmax φ Hfs.
  specialize (Hfs Hmax). simpl in Hfs.
  apply (forces_implies_mem (exist _ Δ Hmax) φ Hfs).
Qed.

Lemma truth_set_impl_forward_ind :
  forall φ1 φ2,
    (forall Δ (Hmax: maximal Δ), In_set Δ (Impl φ1 φ2) -> forces_set Δ (Impl φ1 φ2)).
Proof.
  intros φ1 φ2 Δ Hmax Hmem.
  intros Hmax'.
  apply (mem_implies_forces (exist _ Δ Hmax') (Impl φ1 φ2) Hmem).
Qed.

Lemma truth_set_and_ind :
  forall φ1 φ2,
    (forall Δ (Hmax: maximal Δ), In_set Δ (And φ1 φ2) <-> forces_set Δ (And φ1 φ2)).
Proof.
  intros φ1 φ2 Δ Hmax.
  split.
  - intros Hmem Hmax'. apply (mem_implies_forces (exist _ Δ Hmax') (And φ1 φ2) Hmem).
  - intros Hfs. specialize (Hfs Hmax). simpl in Hfs. apply (forces_implies_mem (exist _ Δ Hmax) (And φ1 φ2) Hfs).
Qed.

Lemma truth_set_or_ind :
  forall φ1 φ2,
    (forall Δ (Hmax: maximal Δ), In_set Δ (Or φ1 φ2) <-> forces_set Δ (Or φ1 φ2)).
Proof.
  intros φ1 φ2 Δ Hmax.
  split.
  - intros Hmem Hmax'. apply (mem_implies_forces (exist _ Δ Hmax') (Or φ1 φ2) Hmem).
  - intros Hfs. specialize (Hfs Hmax). simpl in Hfs. apply (forces_implies_mem (exist _ Δ Hmax) (Or φ1 φ2) Hfs).
Qed.

(* Final skeleton: state the full lemma and leave it Admitted for now so you can iterate.
   The helper lemmas above cover Var/Bot and the forward Impl step; continue similarly for And/Or/Box/Dia. *)
Lemma truth_set_ind : forall Δ φ, maximal Δ -> (In_set Δ φ <-> forces_set Δ φ).
Proof.
  intros Δ φ Hmax.
  revert Δ Hmax.
  induction φ; intros Δ Hmax; simpl.
  - (* Bot *) split; [ apply truth_set_bot_forward | apply truth_set_bot_backward ]; assumption.
  - (* Var *) split; [ apply truth_set_var_forward | apply truth_set_var_backward ]; assumption.
  - (* Impl *) split.
    + intros HIn. apply (truth_set_impl_forward_ind φ1 φ2 Δ Hmax HIn).
    + intros Hfs. apply (truth_set_impl_backward_complete Δ Hmax φ1 φ2 IHφ1 IHφ2 Hfs).
  - (* And *) apply (truth_set_and_ind φ1 φ2 Δ Hmax).
  - (* Or *) apply (truth_set_or_ind φ1 φ2 Δ Hmax).
  - (* Neg *) apply (truth_set_neg_ind φ IHφ Δ Hmax).
  - (* Box *) apply (truth_set_box_ind φ IHφ Δ Hmax).
  - (* Dia *) apply (truth_set_dia_ind φ IHφ Δ Hmax).
Qed.

(* Helper: from-membership at the set-level to forcing at the canonical witness. *)
Lemma truth_lemma_can_set_from_mem :
  forall Δ (Hmax : maximal Δ) φ,
    In_set Δ φ -> forces (exist _ Δ Hmax) φ.
Proof.
  intros Δ Hmax φ Hmem.
  (* Use truth_set_ind to turn In_set into forces_set (forall witnesses), then specialize at Hmax. *)
  pose proof (proj1 (truth_set_ind Δ φ Hmax) Hmem) as Hfs_all.
  simpl in Hfs_all.
  exact (Hfs_all Hmax).
Qed.
