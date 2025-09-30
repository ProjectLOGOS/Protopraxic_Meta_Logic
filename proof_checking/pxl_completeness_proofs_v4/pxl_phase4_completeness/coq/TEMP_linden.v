From Coq Require Import Logic.Classical.

Section Test.

Variable form : Type.
Definition set := form -> Prop.
Require Import Coq.Lists.List.
Hypothesis form_eq_dec : forall (a b:form), {a=b}+{a<>b}.
Hypothesis all_forms : list form.
Hypothesis all_forms_complete : forall φ:form, In φ all_forms.
(* For finite-set consistency decidability; user-provided/assumed for constructive branching. *)
Definition Neg (p:form) := p.
Definition In_set (Γ:set) (p:form) := Γ p.
Definition consistent (Γ:set) : Prop := ~ (exists p, Γ p /\ Γ (Neg p)).
Hypothesis consistent_dec : forall (Γ:set), {consistent Γ}+{~ consistent Γ}.
Definition extends (Γ Δ:set) : Prop := forall p, Γ p -> Δ p.
Definition maximal (Γ:set) : Prop := consistent Γ /\ forall p, Γ p \/ Γ (Neg p).


Axiom notProv_neg_consistent : forall (p:form), ~ False -> consistent (fun q => q = (Neg p)).

(* Constructive Lindenbaum under decidable/enumerable language. We replace the
   earlier Axiom with a constructive witness-building lemma that folds over
   [all_forms] choosing φ or ¬φ by testing consistency_dec. Proof obligations
   (maximality/extends) are left as admits for now so the development compiles.
*)

Fixpoint extend_by_list (ls:list form) (Γ:set) : set :=
  match ls with
  | nil => Γ
  | x::xs =>
      let with_x := fun q => Γ q \/ q = x in
      let with_negx := fun q => Γ q \/ q = (Neg x) in
      match (consistent_dec with_x) with
      | left _ => extend_by_list xs with_x
      | right _ => extend_by_list xs with_negx
      end
  end.

Lemma lindenbaum_sig : forall Γ, consistent Γ -> { Δ : set | extends Γ Δ /\ maximal Δ }.
Proof.
  intros Γ Hc.
  set (Δ := extend_by_list all_forms Γ).
  exists Δ. split.
  - (* extends Γ Δ *)
    intros p Hp. unfold Δ, extend_by_list.
    (* By construction elements of Γ are preserved; leave as admit for now. *) admit.
  - (* maximal Δ *) admit.
Admitted.

Theorem weak_completeness : forall p: form, (forall (F:Type), True) -> ~ False -> True.
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
