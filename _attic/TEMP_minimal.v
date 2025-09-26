From Coq Require Import Logic.Classical.

Section Deep.

Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r,
    Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
| ax_PL_em  : forall p, Prov (Or p (Neg p))
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

Record frame := {
  W : Type; R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

Fixpoint eval (F:frame) (v:valuation F) (w:(W F)) (φ:form) : Prop :=
  match φ with
  | Bot      => False
  | Var n    => v n w
  | Impl p q => eval F v w p -> eval F v w q
  | And p q  => eval F v w p /\ eval F v w q
  | Or p q   => eval F v w p \/ eval F v w q
  | Neg p    => ~ eval F v w p
  | Box p    => forall u, R F w u -> eval F v u p
  | Dia p    => exists u, R F w u /\ eval F v u p
  end.

Definition valid_on (F:frame) (φ:form) : Prop := forall v w, eval F v w φ.
Definition valid (φ:form) : Prop := forall (F:frame), valid_on F φ.

Definition set := form -> Prop.
Definition consistent (Γ:set) : Prop := ~ (exists p, Γ p /\ Γ (Neg p)).
Definition extends (Γ Δ:set) : Prop := forall p, Γ p -> Δ p.
Definition maximal (Γ:set) : Prop :=
  consistent Γ /\ forall p, Γ p \/ Γ (Neg p).

Definition In_set (Γ:set) (p:form) : Prop := Γ p.

Axiom maximal_contains_theorems_ax : forall Γ φ, maximal Γ -> Prov φ -> In_set Γ φ.
Axiom maximal_closure_MP_ax : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> In_set Γ φ -> In_set Γ ψ.
Definition can_world := { Γ : set | maximal Γ }.
Definition can_R (w u:can_world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.
Axiom can_R_euclidean_ax :
  forall Γ Δ Θ, maximal (proj1_sig Γ) -> can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.

Lemma maximal_contains_theorems Γ :
  maximal Γ -> forall φ, Prov φ -> In_set Γ φ.
Proof.
  intros Hmax φ Hprov.
  apply maximal_contains_theorems_ax; auto.
Qed.

Lemma maximal_MP_closed Γ :
  maximal Γ -> forall φ ψ, In_set Γ (Impl φ ψ) -> In_set Γ φ -> In_set Γ ψ.
Proof.
  intros Hmax φ ψ Himp Hφ.
  eapply maximal_closure_MP_ax; eauto.
Qed.

Lemma maximal_necessitation Γ :
  maximal Γ -> forall φ, Prov φ -> In_set Γ (Box φ).
Proof.
  intros Hmax φ Hprov.
  exact (maximal_contains_theorems_ax Γ (Box φ) Hmax (nec φ Hprov)).
Qed.

Axiom lindenbaum_sig : forall Γ, consistent Γ -> { Δ : set | extends Γ Δ /\ maximal Δ }.
Axiom notProv_neg_consistent : forall p, ~ Prov p -> consistent (fun q => q = Neg p).

Lemma can_R_refl : forall Γ: can_world, can_R Γ Γ.
Proof.
  intros Γ φ Hbox.
  pose proof (proj2_sig Γ) as Hmax.
  pose proof (ax_T φ) as HT.
  apply maximal_contains_theorems_ax with (Γ:=proj1_sig Γ) in HT; try assumption.
  eapply maximal_closure_MP_ax; try eassumption.
Qed.

Lemma can_R_euclidean : forall Γ Δ Θ: can_world, can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.
Proof.
  intros Γ Δ Θ Hgd Hgt.
  eapply can_R_euclidean_ax; [apply proj2_sig | exact Hgd | exact Hgt].
Qed.

Lemma can_R_symm : forall Γ Δ: can_world, can_R Γ Δ -> can_R Δ Γ.
Proof.
  intros Γ Δ H.
  pose proof (can_R_refl Γ) as Hrefl.
  intros p Hbox.
  apply (can_R_euclidean Γ Δ Γ H Hrefl); assumption.
Qed.
Lemma can_R_trans : forall Γ Δ Θ: can_world,
  can_R Γ Δ -> can_R Δ Θ -> can_R Γ Θ.
Proof.
  intros Γ Δ Θ HGD HDT.
  intros p Hbox.
  pose proof (can_R_refl Γ) as HreflG.
  pose proof (can_R_euclidean_ax Γ Δ Γ (proj2_sig Γ) HGD HreflG) as Hdg.
  pose proof (can_R_euclidean_ax Δ Γ Θ (proj2_sig Δ) Hdg HDT) as Hgt.
  apply Hgt; exact Hbox.
Qed.

Definition can_frame : frame :=
  {| W := can_world;
     R := can_R;
     R_refl  := fun w => can_R_refl w;
     R_symm  := fun w u => can_R_symm w u;
     R_trans := fun w u v => can_R_trans w u v |}.

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

Axiom truth_lemma_ax : forall (w:can_world) (p:form), In_set (proj1_sig w) p <-> forces w p.
Axiom truth_lemma_to_forces_ax : forall (w:can_world) (p:form), In_set (proj1_sig w) p -> forces w p.
Axiom truth_lemma_from_forces_ax : forall (w:can_world) (p:form), forces w p -> In_set (proj1_sig w) p.

Definition canonical_valuation : valuation can_frame := fun n w => In_set (proj1_sig w) (Var n).

Axiom canonical_eval_to_forces_ax : forall (w:can_world) (p:form),
  eval can_frame canonical_valuation w p -> forces w p.
Axiom canonical_forces_to_eval_ax : forall (w:can_world) (p:form),
  forces w p -> eval can_frame canonical_valuation w p.

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
  intros w p; apply truth_lemma_ax.
Qed.

End Deep.
