From Coq Require Import List.
Import ListNotations.
From PXLs R(* Modal duals as lemmas *)
Lemma modal_dual_dia_box1 φ :
  Prov (Impl (Dia φ) (Neg (Box (Neg φ)))).
Proof. exact (ax_dual_dia_box φ). Qed.

Lemma modal_dual_box_dia2 φ :
  Prov (Impl (Neg (Box φ)) (Dia (Neg φ))).
Proof. exact (ax_dual_box_dia φ). Qed.
Lemma can_R_box_elim Γ Δ (HΓ:mct Γ) (HΔ:mct Δ) φ :
  can_R (exist _ Γ HΓ) (exist _ Δ HΔ) -> In_set Γ (Box φ) -> In_set Δ φ.
Proof. unfold can_R. simpl. firstorder. Qed.
Axiom dia_membership_to_successor :
  forall Γ (HΓ:mct Γ) φ : form,
    In_set Γ (Dia φ) ->
    {Δ : set & {HΔ : mct Δ & { HR : can_R (exist _ Γ HΓ) (exist _ Δ HΔ)
                              & In_set Δ φ }}}.
Axiom explosion_from_neg_and_pos :
  forall Δ φ : form, In_set Δ (Neg φ) -> In_set Δ φ -> False. PXLv3.

Set Implicit Arguments.

(* --- Basic sets and MCT structure with Hilbert closure --- *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

Record mct (G:set) : Prop := {
  mct_cons  : consistent G;
  mct_thm   : forall φ : form, Prov φ -> G φ;                    (* theorems in the set *)
  mct_mp    : forall φ ψ : form, G (Impl φ ψ) -> G φ -> G ψ;     (* closed under MP *)
  mct_total : forall φ : form, G φ \/ G (Neg φ)                  (* maximality *)
}.

(* --- Canonical worlds, accessibility --- *)
Definition world := { G : set | mct G }.
Definition can_R (w u:world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* --- Kripke forcing aligned with membership for Var --- *)
Fixpoint forces (w:world) (p:form) : Prop :=
  match p with
  | Bot      => False
  | Var n    => In_set (proj1_sig w) (Var n)
  | Impl a b => (forces w a -> forces w b)
  | And a b  => forces w a /\ forces w b
  | Or  a b  => forces w a \/ forces w b
  | Neg a    => ~ forces w a
  | Box a    => forall u, can_R w u -> forces u a
  | Dia a    => exists u, can_R w u /\ forces u a
  end.

(* --- Propositional helpers (from PXLv3 constructors) --- *)
Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
Proof. exact (ax_K b a). Qed.

Lemma prov_or_imp_negL (a b : form) : Prov (Impl (Or a b) (Impl (Neg a) b)).
Proof.
  (* Use ax_or_elim with r := Impl (Neg a) b *)
  (* Need: Prov (Impl a (Impl (Neg a) b)) and Prov (Impl b (Impl (Neg a) b)) *)
  pose proof (prov_imp_weaken (Neg a) b) as Hb.
  (* For a -> (a -> b): from neg_imp_to_any we have (a -> a -> b),
     use ax_PL_imp to rotate/compose: (a -> (a -> a)) then chain to b *)
  pose proof (neg_imp_to_any a b) as Hna.    (* (a) -> (a -> b) *)
  (* derive a -> (a -> b) using ax_PL_imp *)
  (* ax_PL_imp p q r : ((p->q)->((q->r)->(p->r))) *)
  pose proof (ax_PL_imp (Neg a) a b) as Hcomp.
  (* First build (a -> (a -> a)) *)
  pose proof (prov_imp_weaken a (Neg a)) as Ha_na_a.    (* a -> (a -> a) *)
  (* Now compose (a -> (a -> a)) with ((a)->(a->b)) to get (a -> (a -> b)) *)
  apply (mp _ _ (ax_or_elim a b (Impl (Neg a) b)));
  [ (* left branch: a -> (a -> b) *)
    eapply mp; [exact (mp _ _ Hcomp Ha_na_a)|]; exact Hna
  | (* right branch: b -> (?a -> b) *)
    exact Hb
  ].
Qed.



(* --- Box/Dia intro from canonical machinery --- *)
Lemma box_intro (G:set) (HG:mct G) φ :
  (forall Δ (HΔ:mct Δ), can_R (exist _ G HG) (exist _ Δ HΔ) -> In_set Δ φ) ->
  In_set G (Box φ).
Proof.
  destruct (mct_total HG (Box φ)) as [HBox|HnegBox]; [assumption|].
  pose proof (mct_thm HG _ (modal_dual_box_dia2 φ)) as Hdual.
  specialize (mct_mp HG _ _ Hdual HnegBox) as HDiaNeg.
  destruct (dia_membership_to_successor G HG (Neg φ) HDiaNeg) as [Δ [HΔ [HR Hnegφ]]].
  specialize (H Δ HΔ HR).
  exfalso. apply (explosion_from_neg_and_pos Δ φ Hnegφ H).
Qed.

Lemma dia_intro (G U:set) (HG:mct G) (HU:mct U) φ :
  can_R (exist _ G HG) (exist _ U HU) ->
  In_set U φ ->
  In_set G (Dia φ).
Proof.
  destruct (mct_total HG (Dia φ)) as [HDia|HnegDia]; [assumption|].
  pose proof (mct_thm HG _ (modal_dual_dia_box1 φ)) as Hdual.
  specialize (mct_mp HG _ _ Hdual HnegDia) as HBoxNeg.
  pose proof (can_R_box_elim G U HG HU φ HR HBoxNeg) as Hnegφ.
  exact (False_rect _ (explosion_from_neg_and_pos U φ Hnegφ H)).
Qed.

(* --- Structural lemmas for constructive MCS --- *)
Parameter enum : nat -> form.               (* fixed enumeration *)
Axiom enum_complete : forall φ, exists n, enum n = φ.

Lemma prov_finite_support Γ φ :
  Prov Γ φ -> exists Γ0, finite Γ0 /\ incl Γ0 Γ /\ Prov Γ0 φ.
Proof. Admitted.

Lemma cons_add_l Γ φ :
  consistent Γ -> ~ Prov Γ φ -> consistent (cons Γ φ).
Proof. Admitted.

Lemma cons_add_r Γ φ :
  consistent Γ -> ~ Prov Γ (Neg φ) -> consistent (cons Γ (Neg φ)).
Proof. Admitted.

Parameter dec_cons : forall (Σ:set form), { ~ Prov Σ Bot } + { Prov Σ Bot }.

Definition step (Σ : set form) (n : nat) : set form :=
  let ψ := enum n in
  match dec_cons (fun φ => Σ φ \/ φ = ψ) with
  | left _  => fun φ => Σ φ \/ φ = ψ
  | right _ => fun φ => Σ φ \/ φ = Neg ψ
  end.

Fixpoint extend (n:nat) (Σ:set form) : set form :=
  match n with 0 => step Σ 0 | S k => step (extend k Σ) (S k) end.

Definition Δ∞ := fun φ => exists n, In_set (extend n (fun _ => False)) φ.

Lemma lindenbaum_constructive : maximal Δ∞ /\ consistent Δ∞.
Proof. Admitted.

(* --- Truth Lemma --- *)
Theorem truth_lemma :
  forall (w:world) (φ : form), forces w φ <-> In_set (proj1_sig w) φ.
Proof.
  intros w φ; revert w.
  induction φ; intro w; split; simpl.

  (* Bot *)
  - intros []; contradiction.
  - intros [p [Hp Hnp]]; exact Hnp.

  (* Var *)
  - exact (fun H => H).
  - exact (fun H => H).

  (* Impl *)
  - intros Himp.
    destruct (mct_total (proj2_sig w) a) as [Ha|Hna].
    + specialize (Himp (proj1 (IH a w) Ha)).
      apply (proj1 (IH b w)); exact Himp.
    + pose proof (mct_thm (proj2_sig w) _ (ax_PL_neg2 a)) as Hneg2.  (* a -> (a -> ⊥) *)
      pose proof (mct_thm (proj2_sig w) _ (ax_PL_imp _ _ b)) as Hcomp.
      (* Using propositional axioms we can derive (a -> (a -> b)) then MP with a *)
      specialize (mct_mp (proj2_sig w) _ _ Hneg2 Hna) as Himpl.
      specialize (mct_mp (proj2_sig w) _ _ Hcomp Himpl) as Himpl'.
      apply (proj1 (IH b w)). apply (mct_mp (proj2_sig w) _ _ Himpl' Ha).
  - intros Hin Ha. apply (proj1 (IH b w)).
    apply (mct_mp (proj2_sig w) _ _ Hin).
    apply (proj2 (IH a w)); exact Ha.

  (* And *)
  - intros [Ha Hb].
    pose proof (mct_thm (proj2_sig w) _ (ax_PL_and _ _)) as HandIntro.
    specialize (mct_mp (proj2_sig w) _ _ HandIntro (proj2 (IH a w) Ha)) as H1.
    exact (mct_mp (proj2_sig w) _ _ H1 (proj2 (IH b w) Hb)).
  - intros H. split.
    + apply (proj1 (IH a w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_and1 _ _)) H).
    + apply (proj1 (IH b w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_and2 _ _)) H).

  (* Or *)
  - intros Hor.
    destruct Hor as [Ha|Hb].
    + left.  apply (proj1 (IH?1 w)); exact Ha.
    + right. apply (proj1 (IH?2 w)); exact Hb.
  - intros HOr.
    destruct (mct_total (proj2_sig w) ?1) as [Ha|Hna].
    + left.  apply (proj1 (IH?1 w)); exact Ha.
    + right.
      pose proof (mct_thm (proj2_sig w) _ (prov_or_imp_negL ?1 ?2)) as HorImp.
      apply (proj1 (IH?2 w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_mp (proj2_sig w) _ _ HorImp HOr) Hna).

  (* Neg *)
  - intros Hn.
    destruct (mct_total (proj2_sig w) ?) as [Ha|Hna].
    + exfalso. apply Hn. apply (proj2 (IH? w)); exact Ha.
    + exact Hna.
  - intros Hneg Hfa.
    apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_neg2 _)) Hneg).
    apply (proj2 (IH? w)); exact Hfa.

  (* Box *)
  - intros Hall.
    (* Box-intro using canonical condition: if all successors force ? *)
    (* To use box_intro we need successor-membership of ?; we obtain from IH *)
    apply box_intro with (H?:=proj2_sig w).
    intros ? H? HR. apply (proj1 (IH? (exist _ ? H?))).
    apply Hall; exact HR.
  - intros HBox u HR.
    (* Elim along can_R and IH *)
    apply (proj2 (IH? u)).
    apply (can_R_box_elim _ _ (proj2_sig w) (proj2_sig u) ? HR HBox).

  (* Dia *)
  - intros [u [HR Hu]].
    (* Dia-intro from successor membership via IH *)
    apply (dia_intro (proj1_sig w) (proj1_sig u) (proj2_sig w) (proj2_sig u) ?); auto.
    apply (proj2 (IH? u)); exact Hu.
  - intros HDia.
    (* From membership of ?, produce successor and IH to get forces *)
    destruct (dia_membership_to_successor _ (proj2_sig w) ? HDia) as [? [H? [HR H?]]].
    exists (exist _ ? H?). split; [assumption|].
    apply (proj1 (IH? (exist _ ? H?))); exact H?.
Qed.
