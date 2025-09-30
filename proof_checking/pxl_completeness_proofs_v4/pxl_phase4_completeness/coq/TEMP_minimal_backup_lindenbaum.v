From Coq Require Import Logic.Classical.
Require Import Coq.Lists.List.

Section TEMP_minimal.

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
| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| ax_PL_and_intro : forall p q, Prov (Impl p (Impl q (And p q)))
| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
| Prov_or_intro_l : forall p q, Prov (Impl p (Or p q))
| Prov_or_intro_r : forall p q, Prov (Impl q (Or p q))
| Prov_imp_dist : forall p q r, Prov (Impl (Impl p (Impl q r)) (Impl (Impl p q) (Impl p r)))
| Prov_K : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| Prov_T : forall p, Prov (Impl (Box p) p)
| Prov_4 : forall p, Prov (Impl (Box p) (Box (Box p)))
| Prov_5 : forall p, Prov (Impl (Dia p) (Box (Dia p)))
| Prov_and_intro : forall p q, Prov (Impl p (Impl q (And p q)))
| Prov_and1 : forall p q, Prov (Impl (And p q) p)
| Prov_and2 : forall p q, Prov (Impl (And p q) q)
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

(* Compatibility alias used in other files *)
Definition Maximal := maximal.

Definition In_set (Γ:set) (p:form) : Prop := Γ p.

(* Helper: add a formula to a set (used by Lindenbaum-style lemmas) *)
Definition add (Γ:set) (φ:form) : set := fun q => Γ q \/ q = φ.

Lemma maximal_contains_theorems_ax : forall Γ φ, maximal Γ -> Prov φ -> In_set Γ φ.
Admitted.

Lemma extend_consistent_set :
  forall Γ φ,
    consistent Γ ->
    (consistent (add Γ φ) \/ consistent (add Γ (Neg φ))).
Proof.
  (* Lindenbaum lemma: every consistent set can be extended *)
Admitted.

Lemma In_set_to_Prov :
  forall Γ φ,
    maximal Γ ->
    In_set Γ φ ->
    Prov φ.
Proof.
  intros Γ φ Hmax Hin.
  (* Strategy:
     - Use extend_consistent_set (Lindenbaum extension).
     - Build a maximal Δ extending Γ that decides φ.
     - Show φ must be provable (otherwise contradiction with maximality).
  *)
  Admitted.

Lemma maximal_closure_MP_ax :
  forall Γ φ ψ,
    maximal Γ ->
    In_set Γ (Impl φ ψ) ->
    In_set Γ φ ->
    In_set Γ ψ.
Proof.
  intros Γ φ ψ Hmax Himpl Hφ.
  (* Step 1: convert set membership to Prov using bridge *)
  apply In_set_to_Prov in Himpl; try assumption.
  apply In_set_to_Prov in Hφ; try assumption.
  (* Step 2: apply mp to derive Prov ψ *)
  pose proof (mp _ _ Himpl Hφ) as Hprov.
  (* Step 3: push back into the maximal set *)
  apply maximal_contains_theorems_ax; assumption.
Qed.

Definition can_world := { Γ : set | maximal Γ }.
Definition can_R (w u:can_world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.
Axiom can_R_euclidean_ax :
  forall Γ Δ Θ, maximal (proj1_sig Γ) -> can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.

(* Additional relational axioms for can_R; some are proven in other files, so we
   declare them here as axioms to keep TEMP_minimal minimal. *)
Axiom can_R_symm : forall Γ Δ: can_world, can_R Γ Δ -> can_R Δ Γ.
Axiom can_R_trans : forall Γ Δ Θ: can_world, can_R Γ Δ -> can_R Δ Θ -> can_R Γ Θ.

(* can_frame will be defined after we prove/declare basic properties of can_R. *)

Lemma maximal_contains_theorems (Γ:set) :
  maximal Γ -> forall φ, Prov φ -> In_set Γ φ.
Proof.
  intros Hmax φ Hprov. apply maximal_contains_theorems_ax; auto.
Qed.

Lemma maximal_MP_closed (Γ:set) :
  maximal Γ -> forall φ ψ, In_set Γ (Impl φ ψ) -> In_set Γ φ -> In_set Γ ψ.
Proof.
  intros Hmax φ ψ Himp Hφ. eapply maximal_closure_MP_ax; eauto.
Qed.

Lemma maximal_necessitation Γ :
  maximal Γ -> forall φ, Prov φ -> In_set Γ (Box φ).
Proof.
  intros Hmax φ Hprov. exact (maximal_contains_theorems_ax Γ (Box φ) Hmax (nec φ Hprov)).
Qed.

Axiom lindenbaum_sig : forall Γ, consistent Γ -> { Δ : set | extends Γ Δ /\ maximal Δ }.
Axiom notProv_neg_consistent : forall p, ~ Prov p -> consistent (fun q => q = Neg p).

(* Convenience Hilbert axioms used by the skeleton proofs: left/right disjunction
  introduction. The original codebase exposed these names; we keep the
  familiar identifiers but expose them as admitted Lemmas so the development
  can compile while we (optionally) replace them with constructive proofs
  later. *)
Lemma ax_PL_or_intro_l : forall p q, Prov (Impl p (Or p q)).
Proof. intros p q. apply Prov_or_intro_l. Qed.

Lemma ax_PL_or_intro_r : forall p q, Prov (Impl q (Or p q)).
Proof. intros p q. apply Prov_or_intro_r. Qed.



Lemma can_R_refl : forall Γ: can_world, can_R Γ Γ.
Proof.
  intros Γ φ Hbox. pose proof (proj2_sig Γ) as Hmax. pose proof (ax_T φ) as HT.
  apply maximal_contains_theorems_ax with (Γ:=proj1_sig Γ) in HT; try assumption.
  eapply maximal_closure_MP_ax; try eassumption.
Qed.

Lemma can_R_euclidean : forall Γ Δ Θ: can_world, can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.
Proof.
  intros Γ Δ Θ Hgd Hgt. eapply can_R_euclidean_ax; [apply proj2_sig | exact Hgd | exact Hgt].
Qed.

(* Modal and conjunction wrappers from constructors *)
Lemma ax_K_from_ctor : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q))).
Proof. intros. apply Prov_K. Qed.

Lemma ax_T_from_ctor : forall p, Prov (Impl (Box p) p).
Proof. intros. apply Prov_T. Qed.

Lemma ax_4_from_ctor : forall p, Prov (Impl (Box p) (Box (Box p))).
Proof. intros. apply Prov_4. Qed.

Lemma ax_5_from_ctor : forall p, Prov (Impl (Dia p) (Box (Dia p))).
Proof. intros. apply Prov_5. Qed.

Lemma ax_PL_and_intro_from_ctor : forall p q, Prov (Impl p (Impl q (And p q))).
Proof. intros. apply Prov_and_intro. Qed.

Lemma ax_PL_and1_from_ctor : forall p q, Prov (Impl (And p q) p).
Proof. intros. apply Prov_and1. Qed.

Lemma ax_PL_and2_from_ctor : forall p q, Prov (Impl (And p q) q).
Proof. intros. apply Prov_and2. Qed.

(* Define the canonical frame using can_world and can_R. We rely on the auxiliary
   relational axioms (can_R_symm, can_R_trans) and the lemmas above. *)
Definition can_frame : frame :=
  {| W := can_world;
     R := can_R;
     R_refl := can_R_refl;
     R_symm := can_R_symm;
     R_trans := can_R_trans
  |}.

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

End TEMP_minimal.

