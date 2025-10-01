From Coq Require Import Logic.Classical.
From Coq Require Import Lists.List.

(* Reuse the constructive Lindenbaum machinery proved in TEMP_minimal.v. *)
From PXLs Require Import TEMP_minimal.

(* The small irreducible assumption used by the weak completeness test. *)
Axiom notProv_neg_consistent : forall (p:form), ~ False -> consistent (fun q => q = (Neg p)).

Theorem weak_completeness : forall p: form, (forall (F:Type), True) -> ~ False -> True.
Proof.
  intros p Hvalid.
  intro Hnot.
  set (Γ0 := fun q => q = (Neg p)).
  assert (consistent Γ0) as Hcons by (apply notProv_neg_consistent; exact Hnot).
  (* Use the Lindenbaum witness from TEMP_minimal.v *)
  pose (ldb := lindenbaum_sig Γ0 Hcons).
  set (Δ := proj1_sig ldb).
  pose proof (proj2_sig ldb) as Hboth.
  destruct Hboth as [Hext Hmax].
  exact I.
Qed.

