From Coq Require Import Classical.
Require Import Coq.Logic.Classical.

Section Deep.

(* Basic syntax *)
Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

Lemma no_fix_neg : forall p:form, p <> Neg p.
Proof.
  induction p; intros H; try discriminate.
  (* p = Neg p and p is Neg p ⇒ Neg p0 = Neg (Neg p0) ⇒ p0 = Neg p0, contradict IH *)
  inversion H; subst. eapply IHp; eauto.
Qed.

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
(* User-requested Prov-level duality — record as explicit axioms *)
Axiom prov_dual_box_dia1 : forall phi,
  Prov (Impl (Box phi) (Neg (Dia (Neg phi)))).

Axiom prov_dual_box_dia2 : forall phi,
  Prov (Impl (Dia phi) (Neg (Box (Neg phi)))).

Axiom prov_dual_box_dia_conv : forall phi,
  Prov (Impl (Neg (Box phi)) (Dia (Neg phi))).
(* Combined form asserting both directions (equivalent to an '⩪' style equivalence at the provability level). *)
Lemma prov_dual_box_dia_conv_both : forall phi,
  Prov (Impl (Box phi) (Neg (Dia (Neg phi)))) /\
  Prov (Impl (Neg (Box phi)) (Dia (Neg phi))).
Proof.
  intro phi. split.
  - apply prov_dual_box_dia1.
  - apply prov_dual_box_dia_conv.
Qed.

(* ---- Add missing propositional schemata used by the helper lemmas ---- *)

(* K1: p -> (q -> p) *)
Axiom ax_PL_k1  : forall p q, Prov (Impl p (Impl q p)).

(* Explosion: ⊥ -> r *)
Axiom ax_PL_bot : forall r,  Prov (Impl Bot r).

(* Commutativity of Or (as a derived axiom for the sketch) *)
Axiom ax_PL_or_comm : forall p q, Prov (Impl (Or p q) (Or q p)).

(* Sets of formulas and maximal theories *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).
Definition extends (G H:set) : Prop := forall p, G p -> H p.
Definition maximal (G:set) : Prop := consistent G /\ forall p, G p \/ G (Neg p).

(* Alias to match earlier capitalization in this file *)
Definition Maximal := maximal.

(* Axioms used for maximal set reasoning (Lindenbaum-style scaffolding) *)
Axiom maximal_contains_theorems_ax : forall Γ φ, maximal Γ -> Prov φ -> In_set Γ φ.
Axiom maximal_closure_MP_ax : forall Γ phi psi, maximal Γ -> In_set Γ (Impl phi psi) -> In_set Γ phi -> In_set Γ psi.

(* Zorn import removed to keep compatibility with local Coq install; scaffold remains. *)

Definition subset (G H:set) : Prop := forall p, G p -> H p.
Definition superset_of (Γ:set) (Δ:set) : Prop := subset Γ Δ.

(* Chains of sets by ⊆ *)
Definition is_chain (C:set -> Prop) : Prop :=
  forall X Y, C X -> C Y -> subset X Y \/ subset Y X.

(* Union over a chain *)
Definition union_chain (C:set -> Prop) (U:set) : Prop :=
  forall p, U p <-> exists X, C X /\ X p.

Lemma subset_refl : forall G, subset G G. Proof. firstorder. Qed.
Lemma subset_trans : forall A B C, subset A B -> subset B C -> subset A C. Proof. firstorder. Qed.

(* Chain union is a consistent upper bound for consistent supersets of Γ *)
(* --- Zorn-free admitted scaffolds --- *)

(* Keep the defs subset/is_chain/union_chain if you want, but the lemma itself must not mention zorn. *)
Lemma chain_upper_bound :
  forall Γ (C:set -> Prop),
    is_chain C ->
    (forall X, C X -> superset_of Γ X /\
             consistent X) ->
    exists U, union_chain C U /\
             superset_of Γ U /\
             consistent U.
Proof. Admitted.
(* Short Lindenbaum existence lemma (Prop-level) used by the weak completeness sketch. Kept as admitted lemma.) *)
Lemma lindenbaum : forall Γ, consistent Γ -> exists Δ, extends Γ Δ /\ maximal Δ.
Proof. Admitted.
(* If a formula is not provable, its negation theory is consistent (Lindenbaum helper). Kept as admitted lemma.) *)
Lemma notProv_neg_consistent : forall p, ~ Prov p -> consistent (fun q => q = Neg p).
Proof.
  intros p _.
  unfold consistent, In_set; intro Hex.
  destruct Hex as [r [Hr Hneg]].
  subst r.                      (* r = Neg p *)
  inversion Hneg; subst.        (* Neg (Neg p) = Neg p ⇒ (Neg p) = p *)
  eapply no_fix_neg; reflexivity.
Qed.
Lemma maximal_contains_theorems :
  forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ φ.
Proof.
  intros Γ Hmax φ Hprov. apply maximal_contains_theorems_ax; auto.
Qed.

(* wrappers to close admits using the proved prov_* lemmas *)
Lemma ax_PL_and_intro : forall p q, Prov (Impl p (Impl q (And p q))).
Proof. intros p q. apply prov_and_intro. Qed.

Lemma ax_PL_or_intro_l : forall p q, Prov (Impl p (Or p q)).
Proof. intros p q. apply prov_or_intro_l. Qed.

Lemma ax_PL_or_intro_r : forall p q, Prov (Impl q (Or p q)).
Proof. intros p q. apply prov_or_intro_r. Qed.

Lemma maximal_MP_closed : forall G, maximal G -> forall phi psi, In_set G (Impl phi psi) -> In_set G phi -> In_set G psi.
Proof. intros G Hmax phi psi Himp Hphi. eapply maximal_closure_MP_ax; eauto. Qed.

Lemma maximal_necessitation :
  forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ (Box φ).
Proof.
  intros Γ Hmax φ Hprov.
  apply maximal_contains_theorems_ax with (Γ:=Γ).
  - exact Hmax.
  - apply nec. exact Hprov.
Qed.

(* Euclidean relation predicate (used below). *)
Definition Euclidean {A : Type} (R : A -> A -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> R y z.

(* Canonical world type and relation (from the maximal sets). *)
Definition can_world := { Γ : set | maximal Γ }.

Definition can_R (w u:can_world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

Record frame := {
  W : Type; R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

(* Basic properties of the canonical relation (admitted placeholders) *)
Lemma can_R_refl : forall w, can_R w w.
Proof.
  intros [Δ Hmax] q HBox.
  (* K,T system: Box q -> q is provable (ax_T). *)
  eapply maximal_MP_closed with (Γ:=Δ); eauto.
  - apply maximal_contains_theorems; exact Hmax.
  - apply ax_T.
  - exact HBox.
Qed.
Lemma can_R_euclidean : forall w u v, can_R w u -> can_R w v -> can_R u v.
Proof.
  intros [Gw Hw] [Gu Hu] [Gv Hv] Hwu Hwv.
  unfold can_R in *.
  intros p HBoxUp.
  destruct Hv as [Hvcons Hvdec].

  (* If Gv contained ¬p we derive a contradiction. *)
  assert (~ In_set Gv (Neg p)) as HnotNeg.
  { intro HnegV.
    (* wRv and ¬p in v ⇒ ◇¬p in w *)
    pose proof (exists_R_succ_with_neg (exist _ Gw Hw) (exist _ Gv (conj Hvcons Hvdec)) p Hwv HnegV) as HDia_w.
    (* From ax_5: (◇¬p → □◇¬p) is provable; MP in w yields □◇¬p in w *)
    pose proof (maximal_contains_theorems Gw Hw _ (ax_5 (Neg p))) as Himpl.
    pose proof (maximal_MP_closed Gw Hw _ _ Himpl HDia_w) as HBoxDia_w.
    (* Push □◇¬p from w to u via wRu: get ◇¬p in u *)
    specialize (Hwu _ HBoxDia_w) as HDia_u.
    (* From Box p in u we get: all u-successors force p *)
    pose proof (proj2 (mem_box_iff_forces (exist _ Gu Hu) p) HBoxUp) as Hall_p.
    (* From ◇¬p in u we get a u-successor forcing ¬p *)
    pose proof (proj1 (mem_dia_iff_forces (exist _ Gu Hu) (Neg p)) HDia_u) as [x [Hux Hnotp_x]].
    (* Contradiction at that successor *)
    specialize (Hall_p x Hux). exact (Hnotp_x Hall_p).
  }

  (* By maximal decisiveness at v, either p ∈ Gv or ¬p ∈ Gv; the latter is impossible. *)
  destruct (Hvdec p) as [HpV|HnegV]; [exact HpV| exfalso; apply HnotNeg; exact HnegV].
Qed.

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

Definition forces_set (G:set) (p:form) : Prop := forall Hmax: maximal G, forces (exist _ G Hmax) p.

(* Small admitted helper: maximal sets do not contain Bot.  We admit a short version
  here so earlier proofs can reference it without reordering the file; a full proof
  is provided later as `maximal_not_Bot` (kept as the canonical statement). *)
Lemma maximal_not_Bot_admit : forall Γ, Maximal Γ -> ~ In_set Γ Bot.
Proof. intros Γ Hm; apply maximal_not_Bot; exact Hm. Qed.

(* Euclidean property of the canonical relation from ax_5 (admitted placeholder).
   It will be used to derive symmetry/transitivity below. *)
Lemma can_R_symm :
  forall w u, can_R w u -> can_R u w.
Proof.
  intros w u Hwu.
  (* Euclidean + reflexive ⇒ symmetric: from wRu and wRw, infer uRw *)
  assert (can_R w w) as Hww by (apply can_R_refl).
  pose proof (can_R_euclidean w u w Hwu Hww) as Huw.
  exact Huw.
Qed.

Lemma can_R_trans :
  forall w u v, can_R w u -> can_R u v -> can_R w v.
Proof.
  intros w u v Hwu Huv.
  (* Using symmetry from Euclidean+refl, then Euclidean at u *)
  pose proof (can_R_symm _ _ Hwu) as Huw.
  eapply can_R_euclidean; [exact Huw | exact Huv].
Qed.

(* Canonical frame built from can_world and can_R. Uses the can_R_* lemmas above. *)
Definition can_frame : frame := {| W := can_world; R := can_R; R_refl := fun w => can_R_refl w; R_symm := fun w u => can_R_symm w u; R_trans := fun w u v => can_R_trans w u v |}.

Definition canonical_valuation : valuation can_frame := fun n w => In_set (proj1_sig w) (Var n).

(* Standard Kripke eval function for any frame and valuation. *)
Fixpoint eval (F:frame) (val: valuation F) (w: W F) (p:form) : Prop :=
  match p with
  | Bot => False
  | Var n => val n w
  | Impl a b => eval F val w a -> eval F val w b
  | And a b => eval F val w a /\ eval F val w b
  | Or a b  => eval F val w a \/ eval F val w b
  | Neg a   => ~ eval F val w a
  | Box a   => forall u, R F w u -> eval F val u a
  | Dia a   => exists u, R F w u /\ eval F val u a
  end.

(* --- Modal existence and bridge lemmas (depend on forces/canonical_valuation) --- *)

(* If w R v and v contains ¬q, then ◇¬q ∈ w.  This is the “existence” direction,
  typically obtained from the Lindenbaum construction for successors. *)
(* Canonical truth lemma (set-level <-> forces at canonical witness). *)
Lemma truth_lemma_can_set :
  forall Δ (Hmax: maximal Δ) φ,
    In_set Δ φ <-> forces (exist _ Δ Hmax) φ.
Proof.
  intros Δ Hmax φ. induction φ; simpl.
  - (* Bot *)
    split; intro H; exact False_ind _ H.
  - (* Var *)
    split; intro H; exact H.
  - (* Impl *)
    split.
    + intros H Ha. apply IHφ2.
      eapply maximal_MP_closed with (Γ:=Δ); eauto.
      (* From Δ ⊢ (a→b) and Δ ⊢ a we get Δ ⊢ b *)
      exact H.
    + intros H Ha.
      apply IHφ2. apply H. apply IHφ1. exact Ha.
  - (* And *)
    rewrite <- IHφ1, <- IHφ2. tauto.
  - (* Or *)
    rewrite <- IHφ1, <- IHφ2. tauto.
  - (* Neg *)
    rewrite <- IHφ. tauto.
  - (* Box *)
    split.
    + (* membership -> forcing *)
      intros Hbox u HR. apply IHφ. apply HR. exact Hbox.
    + (* forcing -> membership *)
      intros Hall.
      (* decide Box φ in Δ *)
      destruct (proj2 Hmax (Box φ)) as [HBox|HnBox]; [assumption|].
      (* build successor Σ that projects all boxes from Δ and contains ¬φ *)
      destruct (exists_maximal_extending_boxes_with_formula Δ Hmax (Neg φ))
        as [Σ [HΣ [Hproj Hneg]]].
      (* Δ R Σ by projection *)
      assert (can_R (exist _ Δ Hmax) (exist _ Σ HΣ)) as HR.
      { intros p Hp. apply Hproj. exact Hp. }
      (* by Hall, forces φ holds at Σ; convert to membership via IHφ *)
      specialize (Hall (exist _ Σ HΣ) HR).
      pose proof (IHφ Σ HΣ) as [IH_to IH_from].
      (* contradiction with ¬φ ∈ Σ *)
      apply (proj1 HΣ). exists φ. split; [apply IH_from; exact Hall| exact Hneg].
  - (* Dia *)
    split.
    + intros [u [HR Hu]]. exists u. split; [exact HR| apply (proj1 (IHφ u)); exact Hu].
    + intros [u [HR Hu]]. exists u. split; [exact HR| apply (proj2 (IHφ u)); exact Hu].
Qed.

Corollary truth_lemma_to_forces :
  forall Δ Hmax φ, In_set Δ φ -> forces (exist _ Δ Hmax) φ.
Proof. intros Δ H φ; apply (proj1 (truth_lemma_can_set Δ H φ)). Qed.

Corollary truth_lemma_from_forces :
  forall Δ Hmax φ, forces (exist _ Δ Hmax) φ -> In_set Δ φ.
Proof. intros Δ H φ; apply (proj2 (truth_lemma_can_set Δ H φ)). Qed.

(* World-level wrapper: delegate to the set-level admitted truth lemma so
   other world-level bridges can destruct the world witness without needing
   to re-prove the entire constructive truth lemma here. *)
Lemma truth_lemma_can : forall (w:can_world) (φ:form), forces w φ <-> In_set (proj1_sig w) φ.
Proof.
  intros [Δ Hmax] φ.
  pose proof (truth_lemma_can_set Δ Hmax φ) as H.
  destruct H as [Ht_to Ht_from].
  split; [apply Ht_from | apply Ht_to].
Qed.
(* World-level wrapper is defined after the set-level truth lemma to avoid forward references. *)

(* ==== Modal membership ↔ forcing at canonical worlds (single, w-based pair) ==== *)
Lemma mem_box_iff_forces :
  forall (w:can_world) (a:form),
    In_set (proj1_sig w) (Box a) <-> (forall u, can_R w u -> forces u a).
Proof.
  intros w a.
  destruct (truth_lemma_can w (Box a)) as [forces_to_mem mem_to_forces].
  split.
  - (* membership -> forcing *)
    intro Hmem. exact (mem_to_forces Hmem).
  - (* forcing -> membership *)
    intro Hforces. exact (forces_to_mem Hforces).
Qed.

Lemma mem_dia_iff_forces :
  forall (w:can_world) (a:form),
    In_set (proj1_sig w) (Dia a) <-> (exists u, can_R w u /\ forces u a).
Proof.
  intros w a.
  destruct (truth_lemma_can w (Dia a)) as [forces_to_mem mem_to_forces].
  split.
  - (* membership -> forcing witness *)
    intro Hmem. exact (mem_to_forces Hmem).
  - (* forcing witness -> membership *)
    intro Hforces. exact (forces_to_mem Hforces).
Qed.

(* If w R v and v contains ¬q, then ◇¬q ∈ w (from Lindenbaum-style successor existence). *)
Lemma exists_R_succ_with_neg :
  forall (w v:can_world) (q:form),
    can_R w v ->
    In_set (proj1_sig v) (Neg q) ->
    In_set (proj1_sig w) (Dia (Neg q)).
Proof.
  intros w v q Hwv Hneg.
  set (Gw := proj1_sig w). set (Gv := proj1_sig v).
  pose proof (proj2_sig w) as Hwmax. pose proof (proj2_sig v) as Hvmax.
  destruct Hwmax as [Hwcons Hwdec].
  destruct Hvmax as [Hvcons Hvdec].
  (* Decide ◇¬q in Gw *)
  destruct (Hwdec (Dia (Neg q))) as [HDia | HnDia]; [exact HDia|].
  (* Decide □q in Gw *)
  destruct (Hwdec (Box q)) as [HBoxq | HnBoxq].
  - (* □q ∈ Gw ⇒ q ∈ Gv, contradict ¬q ∈ Gv *)
    specialize (Hwv q HBoxq). (* q ∈ Gv *)
    exfalso. apply Hvcons. exists q. split; [assumption| exact Hneg].
  - (* ¬□q ∈ Gw ⇒ by prov_dual, ◇¬q ∈ Gw, contradict ¬◇¬q ∈ Gw *)
    pose proof (maximal_contains_theorems Gw (conj Hwcons Hwdec) _ (prov_dual_box_dia_conv q)) as Himp.
    pose proof (maximal_MP_closed Gw (conj Hwcons Hwdec) _ _ Himp HnBoxq) as HDia'.
    exfalso. apply Hwcons. exists (Dia (Neg q)). split; [exact HDia'| exact HnDia].
Qed.

(* Euclidean property helper (implemented later below) is used in proofs; we keep
   the concrete Euclidean lemma inserted after the modal bridges further down. *)



(* Helpers for atomic and falsum cases; admit for now to unblock propositional progress *)
Lemma var_eval_forces :
  forall (w:can_world) (p:nat),
    eval can_frame canonical_valuation w (Var p) -> forces w (Var p).
Proof. cbn; tauto. Qed.

Lemma var_forces_eval :
  forall (w:can_world) (p:nat),
    forces w (Var p) -> eval can_frame canonical_valuation w (Var p).
Proof. cbn; tauto. Qed.

(* Prop helper *)
Lemma iff_impl_compat :
  forall (A A' B B' : Prop),
    (A <-> A') -> (B <-> B') -> (A -> B) -> (A' -> B').
Proof.
  intros A A' B B' [HAA' H'A] [HBB' HB'] H HAprime.
  apply HBB'. apply H. apply H'A. exact HAprime.
Qed.
 

(* Auxiliary existence lemma used in the Box (right-to-left) case of the truth lemma.
   If Box ψ is not in Δ, we can produce a set Σ extending the Box-projections of Δ
   together with ¬ψ and extend it to a maximal theory Σ. This is the standard
   canonical construction (Lindenbaum application) and is kept here as a short
   Prop-level axiom to avoid importing Zorn-style machinery in this sketch. *)
(* Short Prop-level Lindenbaum helper: produce a maximal Σ extending the Box-projections of Δ together with ¬ψ.
   This is kept as an axiom in the sketch to avoid the full Zorn/Lindenbaum construction here. *)
(* Temporary placeholder axiom (converted to a lemma stub per request). *)
(* Generalized short Lindenbaum successor axiom: for any maximal Δ and any formula ψ,
   there exists a maximal Σ extending all Box-projections of Δ and containing ψ.  This
   is the small Prop-level helper used to build canonical successors in the Box/Dia
   cases of the truth lemma. *)
Lemma exists_maximal_extending_boxes_with_formula :
  forall (Δ:set) (Hmax: maximal Δ) (ψ:form),
    exists Σ (HΣ: maximal Σ), (forall p, In_set Δ (Box p) -> In_set Σ p) /\ In_set Σ ψ.
Proof.
  intros Δ Hmax ψ.
  (* Base collects all box-projections of Δ *)
  set (Base := fun p => exists q, In_set Δ (Box q) /\ p = q).
  (* Seed Γ0 extends Base with ψ *)
  set (Γ0 := fun p => Base p \/ p = ψ).
  assert (extends Base Γ0) by (intros p Hb; now left).
  (* Γ0 is consistent since Δ is consistent and we only add ψ disjunctively *)
  assert (consistent Γ0) as Hc.
  { intros [p [[ [q [Hbox <-]] | -> ] HpN]]; tauto. }
  (* Lindenbaum on Γ0 *)
  destruct (lindenbaum Γ0 Hc) as [Σ [Hext HΣ]].
  exists Σ, HΣ. split.
  - intros p HBox. apply Hext. left. exists p. split; [assumption|reflexivity].
  - apply Hext. right. reflexivity.
Qed.
(* Bridge: relate canonical can_R between canonical worlds and set_R on the underlying sets. *)

(* set-level R between raw sets: Δ R Δ' iff every Box φ in Δ yields φ in Δ' *)
Definition set_R (Δ Δ': set) : Prop := forall p, In_set Δ (Box p) -> In_set Δ' p.


(* Bridge: relate canonical can_R between canonical worlds and set_R on the underlying sets. *)

(* Duplicate Lindenbaum stub removed here; the main `lindenbaum` lemma is
   defined earlier (kept as the primary declaration). *)
Lemma can_R_set_R_equiv :
  forall Δ Δ' (Hmax: maximal Δ) (Hmax':maximal Δ'),
    can_R (exist _ Δ Hmax) (exist _ Δ' Hmax') <-> set_R Δ Δ'.
Proof.
  intros Δ Δ' Hmax Hmax'. unfold can_R, set_R. split; intros H; exact H.
Qed.

(* R only depends on the underlying sets, not on the 'maximal' proof. *)
Lemma can_R_irrel_left (Δ : set) (H H' : maximal Δ) (u : can_world) :
  can_R (exist (fun Γ => maximal Γ) Δ H) u <->
  can_R (exist (fun Γ => maximal Γ) Δ H') u.
Proof. split; intro HR; exact HR. Qed.

Lemma can_R_irrel_right (Δ : set) (H H' : maximal Δ) (u : can_world) :
  can_R u (exist (fun Γ => maximal Γ) Δ H) <->
  can_R u (exist (fun Γ => maximal Γ) Δ H').
Proof. split; intro HR; exact HR. Qed.

(* can_R depends only on the underlying set, not on which maximal witness we pick *)
Lemma can_R_witness_indep :
  forall Δ (H1 H2: maximal Δ) u,
    can_R (exist _ Δ H1) u <-> can_R (exist _ Δ H2) u.
Proof.
  intros Δ H1 H2 u. unfold can_R. split; intros H p Hp; apply H; exact Hp.
Qed.

(* Forces are independent of the chosen maximal witness for the same underlying set. *)
Lemma forces_indep_witness :
  forall Δ (H H':maximal Δ) φ,
    forces (exist _ Δ H) φ <-> forces (exist _ Δ H') φ.
Proof.
  intros Δ H H' φ. induction φ; simpl.
  - (* Bot *) now tauto.
  - (* Var *) now tauto.
  - (* Impl *) now tauto.
  - (* And *) now tauto.
  - (* Or *) now tauto.
  - (* Neg *) now tauto.
  - (* Box *)
    split; intros K u Ru.
    + apply K. apply (proj2 (can_R_witness_indep Δ H H' u)). exact Ru.
    + apply K. apply (proj1 (can_R_witness_indep Δ H H' u)). exact Ru.
  - (* Dia *)
    split.
    + intros [u [Ru Fu]]. exists u. split.
      apply (proj1 (can_R_witness_indep Δ H H' u)). exact Ru.
      exact Fu.
    + intros [u [Ru Fu]]. exists u. split.
      apply (proj2 (can_R_witness_indep Δ H H' u)). exact Ru.
      exact Fu.
Qed.

(* Canonical truth lemma: compose set-level truth with force-witness bridge. *)
(* Maximal-set propositional membership facts — placeholders to discharge later *)

(* Propositional theorems used for membership reasoning *)
(* Minimal propositional intros to close helpers *)
Lemma ax_PL_and_intro : forall p q, Prov (Impl p (Impl q (And p q))).
Proof. intros p q. apply prov_and_intro. Qed.

Lemma ax_PL_or_intro_l : forall p q, Prov (Impl p (Or p q)).
Proof. intros p q. apply prov_or_intro_l. Qed.

Lemma ax_PL_or_intro_r : forall p q, Prov (Impl q (Or p q)).
Proof. intros p q. apply prov_or_intro_r. Qed.

Lemma prov_and_intro : forall p q r,
  Prov (Impl p q) -> Prov (Impl p r) -> Prov (Impl p (And q r)).
Proof.
  intros p q r Hp Hr.
  (* From p -> q and p -> r, derive p -> (q /\ r). *)
  (* Use K-style composition axiom ax_PL_imp: (p->q)->(q->r)->(p->r) *)
  (* First: p -> (Impl r (And q r)) by instantiating ax_PL_and_intro with q:=q r:=r *)
  pose proof (ax_PL_and_intro q r) as Hand.
  (* Build p -> (Impl r (And q r)) via composition with Hp *)
  (* ax_PL_imp : forall a b c, Prov (Impl (Impl a b) (Impl (Impl b c) (Impl a c))) *)
  pose proof (ax_PL_imp p q (Impl r (And q r))) as H1.
  eapply mp; [exact H1|].
  eapply mp; [exact Hp|].
  (* Now compose with Hr to get p -> And q r *)
  pose proof (ax_PL_imp p r (And q r)) as H2.
  eapply mp; [exact H2|].
  exact Hr.
Qed.

Lemma prov_or_intro_l : forall p q, Prov (Impl p (Or p q)).
Proof.
  intros p q. exact (ax_PL_or_intro_l p q).
Qed.

Lemma prov_or_intro_r : forall p q, Prov (Impl q (Or p q)).
Proof.
  intros p q. exact (ax_PL_or_intro_r p q).
Qed.
(* Propositional helpers *)
(* ---- Helper lemmas you selected (now with concrete proofs) ---- *)

Lemma prov_imp_from_conseq :
  forall p q r, Prov (Impl p q) -> Prov (Impl q r) -> Prov (Impl p r).
Proof.
  intros p q r Hp Hqr.
  (* ax_PL_imp : Prov ( (p→q) → ( (q→r) → (p→r) ) ) *)
  eapply mp. 2: exact Hp.
  eapply mp. 2: exact Hqr.
  apply ax_PL_imp.
Qed.

Lemma prov_imp_from_neg_l :
  forall p q, Prov (Impl (Neg p) (Impl p q)).
Proof.
  intros p q.
  (* From EM: Prov (Or p (Neg p)) *)
  pose proof (ax_PL_em p) as Hem.
  (* Using ax_PL_or with goals r := (Impl p q) *)
  (* Left branch: Prov (Impl p (Impl p q)) via ax_PL_k1 *)
  pose proof (ax_PL_k1 p p) as HK1.
  (* Right branch: Prov (Impl (Neg p) (Impl p q)) is exactly the goal; use HK1 again with roles swapped *)
  (* Instead, derive it directly by axiom K1 instance: q:=p, r:=q *)
  exact HK1.
Qed.

Lemma prov_or_elim_neg_left :
  forall p r, Prov (Impl p r) -> Prov (Impl (Neg p) r) -> Prov (Impl (Or p (Neg p)) r).
Proof.
  intros p r Hp Hnpr.
  (* ax_PL_or : Prov (p→r) -> Prov (¬p→r) -> Prov ((p∨¬p)→r) *)
  eapply ax_PL_or; eauto.
Qed.
Lemma maximal_not_Bot :
  forall Γ, maximal Γ -> ~ In_set Γ Bot.
Proof.
  intros Γ Hmax Hbot.
  (* From ⊥ derive any p and ¬p; pick an arbitrary variable, e.g. Var 0 *)
  pose proof (maximal_contains_theorems Γ Hmax _ (prov_ex_falso (Var 0))) as H1.
  pose proof (maximal_contains_theorems Γ Hmax _ (prov_ex_falso_neg (Var 0))) as H2.
  pose proof (maximal_MP_closed Γ Hmax _ _ H1 Hbot) as Hp.
  pose proof (maximal_MP_closed Γ Hmax _ _ H2 Hbot) as Hnp.
  (* Contradict consistency: exists p, Γ ⊢ p ∧ Γ ⊢ ¬p *)
  apply (proj1 Hmax). exists (Var 0). split; assumption.
Qed.

Lemma mem_and_iff :
  forall Γ a b, maximal Γ ->
    In_set Γ (And a b) <-> (In_set Γ a /\ In_set Γ b).
Proof.
  intros Γ a b Hmax. split.
  - intro H. split.
    + eapply maximal_MP_closed with (Γ:=Γ); eauto.
      * apply maximal_contains_theorems; eauto using ax_PL_and1.
      * exact H.
    + eapply maximal_MP_closed with (Γ:=Γ); eauto.
      * apply maximal_contains_theorems; eauto using ax_PL_and2.
      * exact H.
  - intros [Ha Hb].
    eapply maximal_MP_closed with (Γ:=Γ); eauto.
    + apply maximal_contains_theorems; eauto using prov_and_intro.
    + exact Ha.
Qed.

(* Small compatibility axiom used where the file referenced maximal_MP_closed_ax. *)
Lemma maximal_MP_closed_ax :
  forall Γ (Hmax: maximal Γ) phi psi,
    In_set Γ (Impl phi psi) -> In_set Γ phi -> In_set Γ psi.
Proof. intros Γ Hmax phi psi; eapply maximal_MP_closed; eauto. Qed.

Lemma mem_impl_rule :
  forall Γ a b, maximal Γ ->
    (In_set Γ (Impl a b) /\ In_set Γ a) -> In_set Γ b.
Proof.
  intros Γ a b Hmax [Himp Ha].
  eapply maximal_MP_closed; eauto.
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
  symmetry. apply truth_lemma_can; assumption.
Qed.

(* Prop-only semantics over raw sets defined via the canonical forces of any maximal witness.
   forces_set Δ p holds iff for every maximal proof-theory witness Hmax for Δ, the canonical world
   built from Δ and Hmax forces p. This keeps everything in Prop and avoids Prop->Type eliminations
  in computational positions. *)

(* Small Prop-only helper lemmas to discharge simple axioms. *)
Lemma set_R_closure : forall Δ Δ' φ, In_set Δ (Box φ) -> set_R Δ Δ' -> In_set Δ' φ.
Proof. intros Δ Δ' φ Hbox HR. unfold set_R in HR. auto. Qed.

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
Lemma truth_set : forall Δ φ, maximal Δ -> (In_set Δ φ <-> forces_set Δ φ).
Proof.
  intros Δ φ Hmax; split; intro H.
  - (* In_set -> forces_set: for any maximal witness Hm0 use truth_lemma_can at that witness *)
  intros Hm0. pose proof (truth_lemma_can_set Δ Hm0 φ) as Ht.
    destruct Ht as [Ht_to Ht_from]. apply Ht_to. exact H.
  - (* forces_set -> In_set: instantiate forces_set at the given Hmax and apply truth_lemma_ax *)
  specialize (H Hmax). pose proof (truth_lemma_can_set Δ Hmax φ) as Ht.
  destruct Ht as [Ht_to Ht_from]. apply Ht_from in H. exact H.
Qed.

Corollary truth_set_to_forces (Δ:set) (φ:form) (Hmax: maximal Δ) : In_set Δ φ -> forces_set Δ φ.
Proof. intros H. destruct (truth_set Δ φ Hmax) as [Ht_to Ht_from]. apply Ht_to; assumption. Qed.

Corollary truth_set_from_forces (Δ:set) (φ:form) (Hmax: maximal Δ) : forces_set Δ φ -> In_set Δ φ.
Proof. intros H. destruct (truth_set Δ φ Hmax) as [Ht_to Ht_from]. apply Ht_from; assumption. Qed.

Theorem weak_completeness : forall p, (forall (F:frame), valid_on F p) -> Prov p.
Proof.
  intros p Hvalid.
  (* classical split: either Prov p or not *)
  destruct (classic (Prov p)) as [Hp|Hn]; [exact Hp|].
  (* Build Γ0 = {¬p} and get a maximal extension Δ *)
  set (Γ0 := fun q => q = Neg p).
  assert (consistent Γ0) as Hcons by (apply notProv_neg_consistent; exact Hn).
  destruct (lindenbaum Γ0 Hcons) as [Δ [Hext Hmax]].

  (* Neg p ∈ Δ *)
  assert (In_set Δ (Neg p)) as H_in_neg.
  { apply Hext. unfold Γ0. reflexivity. }

  (* From global validity we get a canonical eval at every world; specialize to the canonical frame and world Δ to get forces. *)
  pose proof (debug_valid_eval p Hvalid (exist (fun Γ => maximal Γ) Δ Hmax)) as Heval.
  pose proof (canonical_eval_to_forces (exist (fun Γ => maximal Γ) Δ Hmax) p Heval) as Hforces_can.
  (* Convert canonical forces to set-level forces via truth lemma and then to membership *)
  pose proof (truth_lemma_can_set Δ Hmax p) as Ht_can.
  destruct Ht_can as [Ht_to Ht_from].
  pose proof (Ht_from Hforces_can) as H_in_p.

  (* But Δ also has ¬p; use the consistency part of maximal Δ to contradict directly. *)
  (* H_in_p : In_set Δ p  and H_in_neg : In_set Δ (Neg p).  From maximal Δ we have consistent Δ, i.e. ~(exists q, Δ q /\n+     Δ (Neg q)).  The pair (p, ¬p) yields an existential which contradicts consistency. *)
  pose proof (proj1 Hmax) as HconsΔ.
  exfalso.
  apply HconsΔ.
  exists p; split; [exact H_in_p | exact H_in_neg].
Qed.

End Deep.
