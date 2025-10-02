PHASE4_TODO.md
2025-09-26 11:31:09Z

Placeholders in PXL_Completeness_Sketch.v:

* Axiom prov_dual_box_dia1 : forall phi, Prov (Impl (Box phi) (Neg (Dia (Neg phi)))).
* Axiom prov_dual_box_dia2 : forall phi, Prov (Impl (Dia (Neg phi)) (Neg (Box phi))).
* Axiom prov_dual_box_dia_conv : forall phi, Prov (Impl (Neg (Box phi)) (Dia (Neg phi))).
* Axiom maximal_contains_theorems : forall G, maximal G -> forall phi, Prov phi -> In_set G phi.
* Axiom maximal_MP_closed : forall G, maximal G -> forall phi psi, In_set G (Impl phi psi) -> In_set G phi -> In_set G psi.
* (* Euclidean helper axiom derived from ax_5 (kept as Axiom placeholder). *)
* Lemma maximal_contains_theorems_ax : forall Γ φ, maximal Γ -> Prov φ -> In_set Γ φ.
* Lemma maximal_closure_MP_ax : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> In_set Γ φ -> In_set Γ ψ.
* Axiom can_R_euclidean_ax :
* exact (maximal_contains_theorems_ax Γ (Box φ) Hmax (nec φ Hprov)).
* Axiom lindenbaum : forall Γ, consistent Γ -> exists Δ, extends Γ Δ /\ maximal Δ.
* (* From maximal_contains_theorems_ax and ax_T we can get (Box φ -> φ) in Γ *)
* apply maximal_contains_theorems_ax with (Γ:=proj1_sig Γ) in HT; try assumption.
* eapply maximal_closure_MP_ax; try eassumption.
* apply (can_R_euclidean_ax Γ Δ Θ (proj2_sig Γ) (proj2_sig Δ) (proj2_sig Θ) Hgd Hgt).
* Axiom iff_impl_compat : forall A A' B B' : Prop,
* Prop-level axiom to avoid importing Zorn-style machinery in this sketch. *)
* This is kept as an axiom in the sketch to avoid the full Zorn/Lindenbaum construction here. *)
* (* Temporary placeholder axiom to avoid parser issues while iterating. *)
* Axiom exists_R_succ_with_neg :
* Axiom truth_lemma_can :
* Axiom eval_forces_equiv : forall (w: can_world) (φ: form), eval can_frame canonical_valuation w φ <-> forces w φ.
* - (* forces_set -> In_set: instantiate forces_set at the given Hmax and apply truth_lemma_ax *)
