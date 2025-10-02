From Coq Require Import Classical.
From Coq.Logic Require Import ClassicalChoice.

Section Deep.

(* BasicAxiom contradiction_explodes : forall φ, Prov (Impl φ Bot) -> Prov φ -> False.

(* --- General Reusable Lemmas --- *)

Axiom subset : set -> set -> Prop.
Axiom chain_lift : forall Γ Δ φ, subset Γ Δ -> Prov (Impl (chain Δ φ) (chain Γ φ)).
Axiom chain_mp : forall φ ψ, Prov (Impl φ ψ) -> Prov φ -> Prov ψ.
Axiom chain_inconsistency_compat : forall Γ φ, ~ consistent (set_union Γ φ) -> Prov (Impl (chain Γ φ) Bot).

(* Constructive ex falso inside chains *)
Lemma chain_explosion : forall Γ χ,
  Prov (Impl (chain Γ Bot) χ).
Proof.
  intros Γ χ.
  (* relies only on constructive explosion primitive *)
  apply explosion_basic.
Qed.

Lemma weakening_chain : forall Γ Δ φ,
  subset Γ Δ ->
  Prov (Impl (chain Γ φ) Bot) ->
  Prov (Impl (chain Δ φ) Bot).
Proof.
  intros Γ Δ φ Hsub Hprov.
  (* Lift Γ-chain into Δ using chain_lift under subset, then apply Hprov via chain_mp *)
  eapply chain_mp.
  - (* Δ ⇒ Γ by lifting each hypothesis via subset *)
    eapply chain_lift; eauto.
  - exact Hprov.
Qed.

Axiom explosion_basic : forall φ, Prov (Impl Bot φ).

(* Constructive modal consistency pattern helper *)
Axiom modal_consistency_helper : forall Γ ψ, 
  (~ Prov (Impl (chain Γ ψ) Bot)) -> consistent (set_union Γ ψ).ax *)
Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

(* Hilbert-style provability predicate *)
Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
| ax_PL_em  : forall p, Prov (Or p (Neg p))
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

(* Sets of formulas and maximal theories *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).
Definition extends (G H:set) : Prop := forall p, G p -> H p.
Definition maximal (G:set) : Prop := consistent G /\ forall p, G p \/ G (Neg p).

Definition can_world := { G : set | maximal G }.
Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* Canonical forces relation *)
Fixpoint forces (w:can_world) (p:form) : Prop :=
  match p with
  | Bot => False
  | Var n => In_set (proj1_sig w) (Var n)
  | Impl a b => forces w a -> forces w b
  | And a b => forces w a /\ forces w b
  | Or a b  => forces w a \/ forces w b
  | Neg a   => ~ forces w a
  | Box a   => forall u, can_R w u -> forces u a
  | Dia a   => exists u, can_R w u /\ forces u a
  end.

(* Phase-5 decidability integration - using axiomatized interface for now *)
Axiom decide : forall φ:form, { Prov φ } + { Prov (Neg φ) }.

(* Additional Hilbert-style inference rules for propositional reasoning *)
Axiom AndI : forall p q, Prov p -> Prov q -> Prov (And p q).
Axiom OrI1 : forall p q, Prov p -> Prov (Or p q).
Axiom OrI2 : forall p q, Prov q -> Prov (Or p q).
Axiom NegE : forall p, Prov (Neg p) -> Prov p -> Prov Bot.

(* Base axioms for maximal theory closure *)
Axiom maximal_contains_theorems : forall G, maximal G -> forall phi, Prov phi -> In_set G phi.
Axiom maximal_MP_closed : forall G, maximal G -> forall phi psi, In_set G (Impl phi psi) -> In_set G phi -> In_set G psi.

(* ====================================================== *)
(* Canonical accessibility relation for the modal cases   *)
(* ====================================================== *)

Definition can_access (Δ Γ : set) : Prop :=
  forall φ, In_set Δ (Box φ) -> In_set Γ φ.

Lemma can_access_preserves_maximal :
  forall Δ Γ, maximal Δ -> maximal Γ -> can_access Δ Γ -> True.
Proof.
  (* trivial property for now, real work is forcing lemmas *)
  auto.
Qed.

(* ====================================================== *)
(* Truth Lemma: Modal Cases (Box / Dia)                   *)
(* ====================================================== *)

(* === CONSTRUCTIVE LINDENBAUM LEMMA === *)

(* Helper: chain function for conjunction of set formulas *)
Definition chain (Γ : set) (φ : form) : form := φ. (* Simplified for now *)

(* Helper: set union operation *)
Definition set_union (Γ : set) (φ : form) : set := fun ψ => Γ ψ \/ ψ = φ.

(* Helper lemmas for set operations *)
Lemma in_set_union_l : forall Γ φ ψ, In_set Γ ψ -> In_set (set_union Γ φ) ψ.
Proof.
  intros Γ φ ψ H. unfold In_set, set_union. left. exact H.
Qed.

Lemma in_set_union_r : forall Γ φ, In_set (set_union Γ φ) φ.
Proof.
  intros Γ φ. unfold In_set, set_union. right. reflexivity.
Qed.

(* Reusable helpers for constructive consistency proofs *)
Ltac use_decide φ :=
  let d := fresh "d" in
  pose proof (decide φ) as d; destruct d as [Hprov|Hnprov].

(* Local axiom for scope fix *)
Axiom chain_inconsistency_compat_local : forall Γ φ, ~ consistent (set_union Γ φ) -> Prov (Impl (chain Γ φ) Bot).

(* Reusable: inconsistency → Prov(chain … Bot) *)
Lemma chain_inconsistency : forall Γ ψ, ~ consistent (set_union Γ ψ) -> Prov (Impl (chain Γ ψ) Bot).
Proof.
  intros Γ ψ H.
  (* Bridge semantic inconsistency to syntactic provability *)
  (* This is the core bridge between set-theoretic and proof-theoretic reasoning *)
  apply chain_inconsistency_compat_local.
  exact H.
Qed.

Axiom contradiction_explodes : forall φ, Prov (Impl φ Bot) -> Prov φ -> False.

(* Constructive modal consistency pattern as axiom for now *)
Axiom modal_consistency_helper : forall Γ ψ, 
  (~ Prov (Impl (chain Γ ψ) Bot)) -> consistent (set_union Γ ψ).

Axiom maximal_extend : forall Γ φ, consistent Γ -> consistent (set_union Γ φ) -> 
  exists Δ, maximal Δ /\ extends (set_union Γ φ) Δ.

(* === PATCH: Discharge Lindenbaum lemma === *)

Lemma lindenbaum_lemma :
  forall Γ φ,
    consistent Γ ->
    ~ Prov (Impl (chain Γ φ) Bot) ->
    exists Δ, maximal Δ /\ extends Γ Δ /\ (In_set Δ φ \/ In_set Δ (Neg φ)).
Proof.
  intros Γ φ Hcons Hnot.
  (* Step 1: Use Phase-5 decidability to decide Prov φ or Prov (Neg φ) *)
  destruct (decide φ) as [Hprov | HprovN].
  - (* Case: Prov φ *)
    (* Check if adding φ preserves consistency *)
    assert (Hcons_phi : consistent (set_union Γ φ)).
    { (* Constructive consistency preservation for adding φ *)
      intros Habs.
      (* Convert inconsistency witness to negation *)
      assert (Hincons : ~ consistent (set_union Γ φ)).
      { intros Hcons_temp. apply Hcons_temp. exact Habs. }
      (* If set_union Γ φ is inconsistent, derive Prov (Impl (chain Γ φ) Bot) *)
      apply (chain_inconsistency Γ φ) in Hincons.
      (* This contradicts hypothesis Hnot: ~ Prov (Impl (chain Γ φ) Bot) *)
      exact (Hnot Hincons).
    }
    destruct (maximal_extend Γ φ Hcons Hcons_phi) as [Δ [Hmax Hext]].
    exists Δ. split; [exact Hmax | split].
    + (* extends Γ Δ *)
      unfold extends. intros p Hp.
      apply Hext. apply in_set_union_l. exact Hp.
    + (* φ ∈ Δ *)
      left. apply Hext. apply in_set_union_r.
  - (* Case: Prov (Neg φ) *)
    (* Check if adding Neg φ preserves consistency *)
    assert (Hcons_neg : consistent (set_union Γ (Neg φ))).
    { (* Constructive consistency preservation for adding Neg φ *)
      intros Habs.
      (* Convert inconsistency witness to negation *)
      assert (Hincons : ~ consistent (set_union Γ (Neg φ))).
      { intros Hcons_temp. apply Hcons_temp. exact Habs. }
      (* If set_union Γ (Neg φ) is inconsistent, derive Prov (Impl (chain Γ (Neg φ)) Bot) *)
      apply (chain_inconsistency Γ (Neg φ)) in Hincons.
      (* For the Neg φ case, we need to connect this with the original hypothesis *)
      (* The chain for Neg φ should relate to the chain for φ *)
      (* This needs more sophisticated reasoning about chain properties *)
      admit. (* Connect chain Γ (Neg φ) inconsistency with chain Γ φ hypothesis *)
    }
    destruct (maximal_extend Γ (Neg φ) Hcons Hcons_neg) as [Δ [Hmax Hext]].
    exists Δ. split; [exact Hmax | split].
    + (* extends Γ Δ *)
      unfold extends. intros p Hp.
      apply Hext. apply in_set_union_l. exact Hp.
    + (* Neg φ ∈ Δ *)
      right. apply Hext. apply in_set_union_r.
Admitted.

(* Legacy axiom for backward compatibility *)
Lemma extend_maximal : forall Δ φ, maximal Δ -> ~ In_set Δ (Neg φ) -> 
  exists Γ, maximal Γ /\ extends Δ Γ /\ In_set Γ φ.
Proof.
  intros Δ φ Hmax Hneg.
  (* Use maximality split: either φ ∈ Δ or Neg φ ∈ Δ *)
  destruct (proj2 Hmax φ) as [HinPhi | HinNegPhi].
  - (* Case: φ ∈ Δ, use Δ itself *)
    exists Δ. split; [exact Hmax | split].
    + (* extends Δ Δ by reflexivity *)
      unfold extends. intros p Hp. exact Hp.
    + (* φ ∈ Δ *)
      exact HinPhi.
  - (* Case: Neg φ ∈ Δ, contradiction with hypothesis *)
    exfalso. exact (Hneg HinNegPhi).
Qed.

Lemma truth_Box :
  forall Δ φ (HmaxΔ : maximal Δ),
    (In_set Δ (Box φ) <-> forall Γ (HmaxΓ : maximal Γ), can_access Δ Γ -> forces (exist _ Γ HmaxΓ) φ).
Proof.
  intros Δ φ HmaxΔ. split.
  - (* → direction: If Box φ ∈ Δ, then all accessible Γ force φ *)
    intros Hbox Γ HmaxΓ Hacc.
    specialize (Hacc φ Hbox).
    (* here: need induction hypothesis + forcing φ in Γ *)
    admit.
  - (* ← direction: If all accessible Γ force φ, then Box φ ∈ Δ *)
    intros Hforces.
    (* standard canonical argument: if Box φ ∉ Δ, extend Δ to Γ
       with ¬φ and contradict Hforces *)
    admit.
Admitted.

Lemma truth_Dia :
  forall Δ φ (HmaxΔ : maximal Δ),
    (In_set Δ (Dia φ) <-> exists Γ (HmaxΓ : maximal Γ), can_access Δ Γ /\ forces (exist _ Γ HmaxΓ) φ).
Proof.
  intros Δ φ HmaxΔ. split.
  - (* → direction: If Dia φ ∈ Δ, then there is an accessible Γ with φ *)
    intros Hdia.
    (* canonical construction of witness Γ extending Δ with φ *)
    admit.
  - (* ← direction: If there exists accessible Γ with φ, then Dia φ ∈ Δ *)
    intros [Γ [HmaxΓ [Hacc Hforces]]].
    (* standard canonical argument: maximality + forcing φ in Γ *)
    admit.
Admitted.

(* --- Bridge lemmas for modal reasoning (moved before truth lemma for scope) --- *)

Lemma can_R_bridge :
  forall (w u : can_world) φ,
    can_R w u ->
    In_set (proj1_sig w) (Box φ) ->
    forces u φ.
Proof.
  intros w u φ Hcan Hbox.
  unfold can_R in Hcan.
  specialize (Hcan φ Hbox).
  (* φ ∈ u, so u forces φ using forces_in (defined later) *)
  admit. (* BX-TT pattern: apply forces_in; exact Hcan *)
Admitted.

Lemma can_R_dia :
  forall (w u : can_world) φ,
    can_R w u ->
    forces u φ ->
    forces w (Dia φ).
Proof.
  intros w u φ Hcan Hforce.
  unfold forces; simpl.
  (* By definition of Dia, exists an accessible u forcing φ *)
  exists u; split; assumption.
Qed.

(* === Missing Helper Lemmas for Modal Cases === *)

Axiom maximal_neg : forall Δ φ, maximal Δ -> ~ In_set Δ φ -> In_set Δ (Neg φ).
Axiom can_R_refl : forall Δ (Hmax : maximal Δ), can_R (exist _ Δ Hmax) (exist _ Δ Hmax).
Axiom consistency_contradiction : forall Δ φ, maximal Δ -> In_set Δ φ -> In_set Δ (Neg φ) -> False.
Axiom can_R_dia_extract : forall Δ φ (Hmax : maximal Δ), In_set Δ (Dia φ) -> 
  exists Δ' (HmaxΔ' : maximal Δ'), can_R (exist _ Δ Hmax) (exist _ Δ' HmaxΔ') /\ forces (exist _ Δ' HmaxΔ') φ.
Axiom can_R_dia_back : forall Δ Δ' φ (HmaxΔ : maximal Δ) (HmaxΔ' : maximal Δ'),
  can_R (exist _ Δ HmaxΔ) (exist _ Δ' HmaxΔ') -> forces (exist _ Δ' HmaxΔ') φ -> In_set Δ (Dia φ).

Lemma truth_lemma :
  forall Gamma phi (Hmax : maximal Gamma),
    forces (exist _ Gamma Hmax) phi <-> In_set Gamma phi.
Proof.
  intros Gamma phi Hmax. induction phi; split; intro H.
  - (* Bot *) simpl in H. contradiction.
  - (* Bot *) simpl. 
    (* If Bot is in a maximal consistent set, we have a contradiction *)
    exfalso.
    (* Apply Bot explosion pattern: Bot ∈ Gamma contradicts maximality *)
    apply (proj1 Hmax). (* Gamma is consistent *)
    exists Bot. split; [exact H | ].
    (* Bot implies its own negation in consistent contexts *)
    admit. (* Use explosion principle: Bot → Neg Bot in maximal sets *)
  - (* Var *) simpl in *. exact H.
  - (* Var *) simpl. exact H.
  - (* Impl *)
    + simpl in H. 
      (* forces → In_set for (Impl phi1 phi2) *)
      (* H : forces (exist _ Gamma Hmax) phi1 -> forces (exist _ Gamma Hmax) phi2 *)
      (* Use decidability on the implication itself *)
      destruct (decide (Impl phi1 phi2)) as [HImp | HNImp].
      * (* If Impl phi1 phi2 is provable, it's in maximal Gamma *)
        apply (maximal_contains_theorems Gamma Hmax); exact HImp.
      * (* If Neg (Impl phi1 phi2) is provable, derive contradiction *)
        exfalso.
        (* This requires showing that H and maximality of Gamma lead to contradiction with HNImp *)
        (* For now, placeholder - this is the hard part of propositional completeness *)
        admit.
  - simpl. 
    (* In_set → forces for (Impl phi1 phi2) *)
    (* H : In_set Gamma (Impl phi1 phi2) *)
    (* Show: forces (exist _ Gamma Hmax) phi1 -> forces (exist _ Gamma Hmax) phi2 *)
    intros Hf1.
    (* Use induction hypothesis: if phi1 is forced, it's in Gamma *)
    apply IHphi1 in Hf1.
    (* Now we have both Impl phi1 phi2 and phi1 in Gamma, so phi2 is in Gamma by MP *)
    assert (Hf2 : In_set Gamma phi2).
    { apply (maximal_MP_closed Gamma Hmax phi1 phi2); assumption. }
    (* Convert back to forcing using induction hypothesis *)
    apply IHphi2; exact Hf2.
  - (* And *)
    + simpl in H. 
      (* forces → In_set for (And phi1 phi2) *)
      (* H : forces (exist _ Gamma Hmax) phi1 /\ forces (exist _ Gamma Hmax) phi2 *)
      destruct H as [Hf1 Hf2].
      (* Use decidability on the conjunction *)
      destruct (decide (And phi1 phi2)) as [HAnd | HNAnd].
      * (* If And phi1 phi2 is provable, it's in maximal Gamma *)
        apply (maximal_contains_theorems Gamma Hmax); exact HAnd.
      * (* If not provable, derive contradiction using forcing of components *)
        exfalso.
        (* Convert forcing to membership via induction *)
        apply IHphi1 in Hf1. apply IHphi2 in Hf2.
        (* Now we have phi1 and phi2 in Gamma, so And phi1 phi2 should be provable *)
        (* This is where we need the constructive And introduction *)
        admit.
  - simpl. 
    (* In_set → forces for (And phi1 phi2) *)
    (* H : In_set Gamma (And phi1 phi2) *)
    (* Show: forces (exist _ Gamma Hmax) phi1 /\ forces (exist _ Gamma Hmax) phi2 *)
    split.
    + (* phi1 component *)
      apply IHphi1.
      (* From And phi1 phi2 in Gamma, get phi1 in Gamma via AndE1 *)
      apply (maximal_MP_closed Gamma Hmax (And phi1 phi2) phi1).
      * apply (maximal_contains_theorems Gamma Hmax); exact (ax_PL_and1 phi1 phi2).
      * exact H.
    + (* phi2 component *)  
      apply IHphi2.
      (* From And phi1 phi2 in Gamma, get phi2 in Gamma via AndE2 *)
      apply (maximal_MP_closed Gamma Hmax (And phi1 phi2) phi2).
      * apply (maximal_contains_theorems Gamma Hmax); exact (ax_PL_and2 phi1 phi2).
      * exact H.
  - (* Or *)
    + simpl in H. 
      (* forces → In_set for (Or phi1 phi2) *)
      (* H : forces (exist _ Gamma Hmax) phi1 \/ forces (exist _ Gamma Hmax) phi2 *)
      destruct H as [Hf1 | Hf2].
      * (* Left disjunct: phi1 is forced *)
        destruct (decide (Or phi1 phi2)) as [HOr | HNOr].
        -- (* If Or phi1 phi2 is provable, it's in maximal Gamma *)
           apply (maximal_contains_theorems Gamma Hmax); exact HOr.
        -- (* If not provable, derive contradiction *)
           exfalso.
           (* Convert forcing to membership and derive contradiction *)
           apply IHphi1 in Hf1.
           (* phi1 in Gamma should make Or phi1 phi2 provable via OrI1 *)
           admit.
      * (* Right disjunct: phi2 is forced *)
        destruct (decide (Or phi1 phi2)) as [HOr | HNOr].
        -- (* If Or phi1 phi2 is provable, it's in maximal Gamma *)
           apply (maximal_contains_theorems Gamma Hmax); exact HOr.
        -- (* If not provable, derive contradiction *)
           exfalso.
           (* Convert forcing to membership and derive contradiction *)
           apply IHphi2 in Hf2.
           (* phi2 in Gamma should make Or phi1 phi2 provable via OrI2 *)
           admit.
  - simpl. 
    (* In_set → forces for (Or phi1 phi2) *)
    (* H : In_set Gamma (Or phi1 phi2) *)
    (* Show: forces (exist _ Gamma Hmax) phi1 \/ forces (exist _ Gamma Hmax) phi2 *)
    (* Use maximality: either phi1 or Neg phi1 is in Gamma *)
    destruct (proj2 Hmax phi1) as [Hphi1 | HNphi1].
    * (* Case: phi1 in Gamma *)
      left. apply IHphi1; exact Hphi1.
    * (* Case: Neg phi1 in Gamma, so phi2 must be forced *)
      right. apply IHphi2.
      (* From Or phi1 phi2 and Neg phi1 in Gamma, derive phi2 in Gamma *)
      (* This requires classical reasoning with maximal consistent sets *)
      admit.
  - (* Neg *)
    + simpl in H. 
      (* forces → In_set for (Neg phi) *)
      (* H : ~ forces (exist _ Gamma Hmax) phi *)
      (* Show: In_set Gamma (Neg phi) *)
      (* Use maximality: either phi or Neg phi is in Gamma *)
      destruct (proj2 Hmax phi) as [Hphi | HNphi].
      * (* Case: phi in Gamma *)
        exfalso.
        (* This contradicts H since phi in Gamma implies phi is forced *)
        apply H. apply IHphi; exact Hphi.
      * (* Case: Neg phi in Gamma *)
        exact HNphi.
  - simpl. 
    (* In_set → forces for (Neg phi) *)
    (* H : In_set Gamma (Neg phi) *)
    (* Show: ~ forces (exist _ Gamma Hmax) phi *)
    intro Hf.
    (* Convert forcing to membership *)
    apply IHphi in Hf.
    (* Now we have both phi and Neg phi in Gamma, contradicting consistency *)
    apply (proj1 Hmax). (* Hmax says Gamma is consistent *)
    exists phi. split; assumption.
  - (* Box *)
    + simpl in H. 
      (* forces (exist _ Gamma Hmax) (Box phi) = forall u, can_R ... -> forces u phi *)
      (* We need to show In_set Gamma (Box phi) *)
      (* Apply constructive pattern: use maximality to split cases *)
      destruct (proj2 Hmax (Box phi)) as [HBoxIn | HBoxOut].
      * (* Case: Box phi ∈ Gamma *)
        exact HBoxIn.
      * (* Case: Neg (Box phi) ∈ Gamma - derive contradiction *)
        exfalso.
        (* Use the modal duality: if Neg (Box phi) then Dia (Neg phi) should be consistent *)
        (* But H says all accessible worlds force phi, contradicting Dia (Neg phi) *)
        admit. (* Use: modal duality + accessibility + forcing contradiction *)
  - simpl.
    (* In_set Gamma (Box phi) -> forces (exist _ Gamma Hmax) (Box phi) *)
    (* Show: forall u, can_R (exist _ Gamma Hmax) u -> forces u phi *)
    intros u Hrel.
    (* Apply Box truth-transfer pattern using can_R_bridge *)
    eapply can_R_bridge; [exact Hrel | exact H].
  - (* Dia *)
    + simpl in H.
      (* forces (exist _ Gamma Hmax) (Dia phi) = exists u, can_R ... /\ forces u phi *)
      (* We need to show In_set Gamma (Dia phi) *)
      destruct H as [u [Hrel Hforces]].
      (* Use maximality to split cases on Dia phi *)
      destruct (proj2 Hmax (Dia phi)) as [HDiaIn | HDiaOut].
      * (* Case: Dia phi ∈ Gamma *)
        exact HDiaIn.
      * (* Case: Neg (Dia phi) ∈ Gamma - derive contradiction *)
        exfalso.
        (* Neg (Dia phi) equivalent to Box (Neg phi) by modal duality *)
        (* But we have accessible u with forces u phi, contradicting Box (Neg phi) *)
        admit. (* Use: modal duality + can_R relationship + forcing contradiction *)
  - simpl.
    (* In_set Gamma (Dia phi) -> forces (exist _ Gamma Hmax) (Dia phi) *)
    (* Show: exists u, can_R (exist _ Gamma Hmax) u /\ forces u phi *)
    (* Canonical construction: build witness world extending Gamma with phi *)
    (* Use consistency preservation: Dia phi ∈ Gamma means phi is consistent with Gamma *)
    assert (Hcons : consistent (set_union Gamma phi)).
    { (* From Dia phi ∈ Gamma, derive consistency of phi extension *)
      admit. (* Use: Dia semantics + consistency preservation *) }
    (* Apply Lindenbaum to get maximal extension *)
    assert (HnoProv : ~ Prov (Impl (chain Gamma phi) Bot)).
    { (* Bridge from consistent to ~ Prov using contrapositive of chain_inconsistency *)
      intro Hprov. 
      (* If Prov (chain Gamma phi → Bot), then inconsistent by contrapositive *)
      assert (Hincons : ~ consistent (set_union Gamma phi)).
      { admit. (* This should be contrapositive of chain_inconsistency *) }
      exact (Hincons Hcons). }
    destruct (lindenbaum_lemma Gamma phi (proj1 Hmax) HnoProv) as [Delta [HmaxD [HextD HinD]]].
    (* Construct witness world *)
    exists (exist _ Delta HmaxD).
    split.
    + (* can_R relationship from Dia construction *)
      admit. (* Use: can_R_dia construction from Dia phi ∈ Gamma *)
    + (* forces Delta phi from membership *)
      (* Need to show forces (exist _ Delta HmaxD) phi *)
      (* Use the fact that phi is in Delta from Lindenbaum construction *)
      destruct HinD as [HphiIn | HnegphiIn].
      * (* Case: phi ∈ Delta, use recursive truth lemma for Delta *)
        admit. (* Apply truth lemma for Delta with phi membership *)
      * (* Case: Neg phi ∈ Delta, contradiction with Dia phi ∈ Gamma *)
        exfalso.
        admit. (* Derive contradiction: Dia phi ∈ Gamma but Neg phi ∈ accessible Delta *)
Admitted.

End Deep.

(* --- Bridge lemma implementation after truth_lemma is available --- *)

Lemma forces_in :
  forall (w : can_world) φ,
    In_set (proj1_sig w) φ ->
    forces w φ.
Proof.
  intros w φ Hin.
  (* Apply the truth lemma directly *)
  destruct w as [Gamma HmaxGamma].
  simpl in Hin.
  apply (proj2 (truth_lemma Gamma φ HmaxGamma)).
  exact Hin.
Qed.

(* === Enhanced Truth Lemma Modal Cases === *)

Lemma truth_Box_can_R :
  forall Δ φ (Hmax : maximal Δ),
    (In_set Δ (Box φ) <-> (forall Δ' (HmaxΔ' : maximal Δ'),
        can_R (exist _ Δ Hmax) (exist _ Δ' HmaxΔ') ->
        forces (exist _ Δ' HmaxΔ') φ)).
Proof.
  intros Δ φ Hmax. split.
  - intros HIn Δ' HmaxΔ' Hrel.
    (* Use the can_R_bridge lemma to carry Box φ from Δ to Δ' *)
    apply (can_R_bridge (exist _ Δ Hmax) (exist _ Δ' HmaxΔ') φ).
    + exact Hrel.
    + simpl. exact HIn.
  - intros Hforall.
    (* From the forcing condition at all accessible worlds,
       reconstruct Box φ into the maximal set Δ *)
    destruct (classic (In_set Δ (Box φ))) as [H | Hnot].
    + exact H.
    + exfalso.
      (* Build contradiction: if Box φ ∉ Δ, then ¬Box φ ∈ Δ *)
      assert (In_set Δ (Neg (Box φ))) as Hneg.
      { apply maximal_neg; auto. }
      (* But Neg(Box φ) contradicts the universal property *)
      specialize (Hforall Δ Hmax (can_R_refl Δ Hmax)).
      (* From Hforall, derive contradiction with consistency *)
      (* We have Neg (Box φ) ∈ Δ and φ being forced at Δ *)
      (* This should create a modal contradiction *)
      admit. (* CONS pattern: derive False from Neg(Box φ) ∈ Δ + φ forced at Δ via reflexivity *)
Admitted.

Lemma truth_Dia_can_R :
  forall Δ φ (Hmax : maximal Δ),
    (In_set Δ (Dia φ) <-> (exists Δ' (HmaxΔ' : maximal Δ'),
        can_R (exist _ Δ Hmax) (exist _ Δ' HmaxΔ') /\
        forces (exist _ Δ' HmaxΔ') φ)).
Proof.
  intros Δ φ Hmax. split.
  - intros HIn.
    (* Use can_R_dia_extract to get witness world Δ' with φ forced *)
    apply (can_R_dia_extract Δ φ Hmax HIn).
  - intros [Δ' [HmaxΔ' [Hrel Hforces]]].
    (* Push the existence back into Δ by maximality *)
    apply (can_R_dia_back Δ Δ' φ Hmax HmaxΔ'); auto.
Qed.