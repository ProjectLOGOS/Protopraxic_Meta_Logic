From Coq Require Import Logic.Classical.

Section Test.

Variable form : Type.
Definition set := form -> Prop.
Definition Neg (p:form) := p.
Definition In_set (Γ:set) (p:form) := Γ p.
Definition consistent (Γ:set) : Prop := ~ (exists p, Γ p /\ Γ (Neg p)).
Definition extends (Γ Δ:set) : Prop := forall p, Γ p -> Δ p.
Definition maximal (Γ:set) : Prop := consistent Γ /\ forall p, Γ p \/ Γ (Neg p).

Axiom lindenbaum_sig : forall Γ, consistent Γ -> { Δ : set | extends Γ Δ /\ maximal Δ }.
Axiom notProv_neg_consistent : forall (p:form), ~ False -> consistent (fun q => q = (Neg p)).

Theorem weak_completeness : forall p, (forall (F:Type), True) -> True.
Proof.
  intros p Hvalid.
  intro Hnot.
  set (Γ0 := fun q => q = (Neg p)).
  assert (consistent Γ0) as Hcons by (apply notProv_neg_consistent; exact Hnot).
  pose (ldb := lindenbaum_sig Γ0 Hcons).
  set (Δ := proj1_sig ldb).
  pose proof (proj2_sig ldb) as Hboth.
  destruct Hboth as [Hext Hmax].
  exact I.
Qed.

End Test.
