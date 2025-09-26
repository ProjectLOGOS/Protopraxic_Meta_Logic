From Coq Require Import Logic.Classical.

Section Repro.

Variable A : Type.
Definition pred := A -> Prop.
Definition consistent (Γ:pred) : Prop := True.
Definition extends (Γ Δ:pred) : Prop := forall a, Γ a -> Δ a.
Definition maximal (Γ:pred) : Prop := True.

Axiom lindenbaum : forall Γ, consistent Γ -> exists Δ, extends Γ Δ /\ maximal Δ.

Theorem test_destruct : forall (p:A), (forall Γ, consistent Γ -> True) -> True.
Proof.
  intros a H.
  set (Γ0 := fun x => True).
  assert (consistent Γ0) as Hcons by exact I.
  destruct (lindenbaum Γ0 Hcons) as [Δ [Hext Hmax]].
  exact I.
Qed.

End Repro.
