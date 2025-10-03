Require Import PXLs.PXL_Completeness_Truth_WF.

Axiom Γ : set.
Axiom H : maximal Γ.

Axiom maximal_contains_theorems : forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ φ.

Axiom max_and : forall Γ φ ψ, maximal Γ -> In_set Γ (And φ ψ) -> (In_set Γ φ /\ In_set Γ ψ).

Axiom max_orL : forall Γ φ ψ, maximal Γ -> In_set Γ (Or φ ψ) -> (In_set Γ φ \/ In_set Γ ψ).

Axiom max_impl : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> (In_set Γ φ -> In_set Γ ψ).

Axiom max_neg : forall Γ φ, maximal Γ -> In_set Γ (Neg φ) -> ~ In_set Γ φ.

Axiom decide : forall φ, Prov φ \/ ~ Prov φ.

Axiom add : set -> form -> set.

Axiom enum : nat -> form.

Axiom enum_surj : forall ψ, exists n, enum n = ψ.

Axiom cons_add_l : forall Γ φ, consistent Γ -> consistent (add Γ φ).

Axiom cons_add_r : forall Γ φ, consistent Γ -> consistent (add Γ (Neg φ)).

Axiom In_set_add_l : forall Γ φ ψ, In_set Γ ψ -> In_set (add Γ φ) ψ.

Axiom In_set_add_here : forall Γ φ, In_set (add Γ φ) φ.

Axiom decide_cons : forall Γ φ, {consistent (add Γ φ)} + {consistent (add Γ (Neg φ))}.

Axiom maximal_from_consistent_total :
  forall Σ, consistent Σ ->
    (forall ψ, In_set Σ ψ \/ In_set Σ (Neg ψ)) ->
    maximal Σ.

Axiom chain_limit_consistent :
  forall (G:nat->set),
    (forall n, consistent (G n)) ->
    (forall n ψ, In_set (G n) ψ -> In_set (G (S n)) ψ) ->
    consistent (fun ψ => exists n, In_set (G n) ψ).

Axiom maximal_In_set_Prov : forall Γ (H: maximal Γ) φ, In_set Γ φ -> Prov φ.

Axiom truth_bot : forces (exist _ Γ H) Bot <-> In_set Γ Bot.

Axiom truth_var : forall n, forces (exist _ Γ H) (Var n) <-> In_set Γ (Var n).

Axiom truth_neg : forall φ, forces (exist _ Γ H) (Neg φ) <-> In_set Γ (Neg φ).

Axiom dia_truth : forall φ, forces (exist _ Γ H) (Dia φ) <-> In_set Γ (Dia φ).
