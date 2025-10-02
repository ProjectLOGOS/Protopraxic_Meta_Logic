Axiom constructive_lindenbaum : forall Γ (H:maximal Γ) φ, ~ In_set Γ (Box φ) -> exists Δ (HΔ:maximal Δ), can_R (exist _ Γ H) (exist _ Δ HΔ) /\ In_set Δ (Neg φ).

Axiom maximal_contains_theorems : forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ φ.

Axiom max_and : forall Γ φ ψ, maximal Γ -> In_set Γ (And φ ψ) -> (In_set Γ φ /\ In_set Γ ψ).

Axiom max_orL : forall Γ φ ψ, maximal Γ -> In_set Γ (Or φ ψ) -> (In_set Γ φ \/ In_set Γ ψ).

Axiom max_impl : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> (In_set Γ φ -> In_set Γ ψ).

Axiom max_neg : forall Γ φ, maximal Γ -> In_set Γ (Neg φ) -> ~ In_set Γ φ.

Axiom decide : forall φ, Prov φ \/ ~ Prov φ.

Axiom maximal_In_set_Prov : forall Γ (H: maximal Γ) φ, In_set Γ φ -> Prov φ.

Axiom truth_bot : forces (exist _ Γ H) Bot <-> In_set Γ Bot.

Axiom truth_var : forall n, forces (exist _ Γ H) (Var n) <-> In_set Γ (Var n).

Axiom truth_neg : forall φ, forces (exist _ Γ H) (Neg φ) <-> In_set Γ (Neg φ).

Axiom dia_truth : forall φ, forces (exist _ Γ H) (Dia φ) <-> In_set Γ (Dia φ).

Include PXL_Completeness_Truth_WF.