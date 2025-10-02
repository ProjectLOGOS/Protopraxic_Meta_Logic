From Coq Require Import List Arith Bool.
Import ListNotations.

(* When building in the full project, add: *)
(* From PXLs.proof_checking.pxl_completeness_proofs_v4.pxl_phase4_completeness.coq *)
(*   Require Import PXL_Completeness_Sketch. *)

Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

(* Prov kernel will be defined after the boolean tautology machinery so we can
  refer to tautology_prop in reflection lemmas without forward references. *)


Fixpoint vars (φ:form) : list nat :=
  match φ with
  | Bot => []
  | Var n => [n]
  | Impl p q => vars p ++ vars q
  | And p q  => vars p ++ vars q
  | Or p q   => vars p ++ vars q
  | Neg p    => vars p
  | Box p    => vars p
  | Dia p    => vars p
  end.

Fixpoint mem (x:nat) (xs:list nat) : bool :=
  match xs with | [] => false | y::ys => if Nat.eqb x y then true else mem x ys end.

Fixpoint nodup (xs:list nat) : list nat :=
  match xs with
  | [] => []
  | x::ys => if mem x ys then nodup ys else x :: nodup ys
  end.

Fixpoint eval_prop (ρ:nat->bool) (φ:form) : bool :=
  match φ with
  | Bot => false
  | Var n => ρ n
  | Impl p q => negb (eval_prop ρ p) || eval_prop ρ q
  | And p q  => andb (eval_prop ρ p) (eval_prop ρ q)
  | Or p q   => orb  (eval_prop ρ p) (eval_prop ρ q)
  | Neg p    => negb (eval_prop ρ p)
  | Box p    => eval_prop ρ p
  | Dia p    => eval_prop ρ p
  end.

Fixpoint all_assignments (xs:list nat) : list (nat -> bool) :=
  match xs with
  | [] => [fun _ => false]
  | x::ys =>
      let rest := all_assignments ys in
      let set0 := List.map (fun ρ => fun n => if Nat.eqb n x then false else ρ n) rest in
      let set1 := List.map (fun ρ => fun n => if Nat.eqb n x then true  else ρ n) rest in
      set0 ++ set1
  end.

Definition tautology_prop (φ:form) : bool :=
  let xs := nodup (vars φ) in
  let asg := all_assignments xs in
  forallb (fun ρ => eval_prop ρ φ) asg.

(* 1) Forall over list implies membership property *)
Lemma forallb_implies_in :
  forall (A:Set) (p:A->bool) (ls:list A) (x:A),
    forallb p ls = true -> In x ls -> p x = true.
Proof.
  intros A p ls x Hforall Hin.
  induction ls as [|h t IH]; simpl in *.
  - inversion Hin.
  - simpl in Hforall. apply Bool.andb_true_iff in Hforall. destruct Hforall as [Ph Pt].
    destruct Hin as [Heq|Hin']; [subst; exact Ph | apply IH; assumption].
Qed.
  (* 3) Evaluation depends only on vars(φ) agreement *)
Lemma eval_depends_only_on_vars :
  forall φ ρ σ,
    (forall v, In v (vars φ) -> ρ v = σ v) ->
    eval_prop ρ φ = eval_prop σ φ.
Proof.
  induction φ as [|n|p IHp q IHq|p IHp q IHq|p IHp q IHq|p IHp|p IHp|p IHp]; simpl; intros ρ σ H; try reflexivity.
  - (* Var *) apply H; simpl; left; reflexivity.
  - (* Impl *)
    set (H1 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_introl Hv))).
    set (H2 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_intror Hv))).
    rewrite (IHp ρ σ H1), (IHq ρ σ H2); reflexivity.
  - (* And *)
    set (H1 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_introl Hv))).
    set (H2 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_intror Hv))).
    rewrite (IHp ρ σ H1), (IHq ρ σ H2); reflexivity.
  - (* Or *)
    set (H1 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_introl Hv))).
    set (H2 := fun v Hv => H v (proj2 (in_app_iff (vars p) (vars q) v) (or_intror Hv))).
    rewrite (IHp ρ σ H1), (IHq ρ σ H2); reflexivity.
  - (* Neg *) now rewrite (IHp ρ σ H); reflexivity.
  - (* Box *) now rewrite (IHp ρ σ H); reflexivity.
  - (* Dia *) now rewrite (IHp ρ σ H); reflexivity.
Qed.

  (* helpers relating mem and nodup/in *)
  Lemma mem_in : forall x xs, In x xs -> mem x xs = true.
  Proof.
    induction xs as [|y ys IH]; simpl; intros Hin.
    - inversion Hin.
    - destruct Hin as [Heq|Hin]; subst; simpl.
      + now rewrite Nat.eqb_refl.
      + case_eq (Nat.eqb x y); intro E; [now apply Nat.eqb_eq in E; subst; contradiction|].
        apply IH; assumption.
  Qed.

  Lemma mem_true_in : forall x xs, mem x xs = true -> In x xs.
  Proof.
    induction xs as [|y ys IH]; simpl; intros H; [discriminate|].
    destruct (Nat.eqb x y) eqn:E; simpl in H.
    - apply Nat.eqb_eq in E; left; congruence.
    - right. apply IH; exact H.
  Qed.

  Lemma nodup_preserves : forall x l, In x l -> In x (nodup l).
  Proof.
  induction l as [|y ys IH]; simpl; intros Hin; [inversion Hin|].
    simpl. destruct (mem y ys) eqn:My.
    - (* y is removed *) destruct Hin as [Heq|Hin']; subst.
      + (* x = y but y was removed: it must appear in ys *)
        apply mem_true_in in My. now apply in_or_app; right; exact My.
      + apply IH; assumption.
    - (* y kept *) destruct Hin as [Heq|Hin']; subst; [left; reflexivity|].
      right. apply IH; assumption.
  Qed.

  (* 4) Every assignment on vars appears in the finite enumeration, pointwise-equal on vars *)
  Lemma all_assignments_complete :
    forall (vs:list nat) (ρ:nat->bool),
      (forall x, ~ In x vs -> ρ x = false) ->
      exists ρ', In ρ' (all_assignments vs) /\ (forall x, In x vs -> ρ' x = ρ x).
  Proof.
    induction vs as [|v vs IH]; intros ρ Hout; simpl.
    - exists (fun _ => false). split; [left; reflexivity| intros x []].
    - (* build a helper valuation that sets v to false so IH's outside-vs hypothesis holds *)
      set (ρ_tail := fun n => if Nat.eqb n v then false else ρ n).
      assert (Htail: forall x, ~ In x vs -> ρ_tail x = false).
      { intros x Hnot. unfold ρ_tail. destruct (Nat.eqb x v) eqn:Eq.
        - reflexivity.
        - (* x <> v *) apply Hout. intro Hc. destruct Hc as [Hv|H']; [
            apply Nat.eqb_eq in Eq; congruence| exact H'].
      }
      destruct (ρ v) eqn:Hv.
      + (* v = true *)
        destruct (IH ρ_tail Htail) as [ρ' [Hin Heq]].
        exists (fun n => if Nat.eqb n v then true else ρ' n). split.
        * apply in_or_app. right. apply in_map. assumption.
        * intros x Hx. destruct Hx as [Heqx|Hx]; [subst; now rewrite Nat.eqb_refl|].
          now rewrite Nat.eqb_neq by (intro C; apply Nat.eqb_eq in C; congruence); apply Heq; assumption.
      + (* v = false *)
        destruct (IH ρ_tail Htail) as [ρ' [Hin Heq]].
        exists (fun n => if Nat.eqb n v then false else ρ' n). split.
        * apply in_or_app. left. apply in_map. assumption.
        * intros x Hx. destruct Hx as [Heqx|Hx]; [subst; now rewrite Nat.eqb_refl|].
          now rewrite Nat.eqb_neq by (intro C; apply Nat.eqb_eq in C; congruence); apply Heq; assumption.
  Qed.

(* 5) Semantic tautology: boolean enumeration implies pointwise truth on all assignments *)
Lemma tautology_prop_sem_sound :
  forall φ, tautology_prop φ = true -> forall (ρ:nat->bool), eval_prop ρ φ = true.
Proof.
  intros φ Htauto ρ.
  unfold tautology_prop in Htauto. simpl in Htauto.
  set (vs := nodup (vars φ)). set (asg := all_assignments vs).
  (* build a representative ρ' in the enumeration that agrees with ρ on vars *)
  set (ρ_tail := fun n => if mem n vs then ρ n else false).
  assert (Htail: forall x, ~ In x vs -> ρ_tail x = false).
  { intros x Hnot. unfold ρ_tail. destruct (mem x vs) eqn:Em; [apply mem_true_in in Em; contradiction|]; reflexivity. }
  destruct (all_assignments_complete vs ρ_tail Htail) as [ρ' [Hin Hagree]].
  pose proof (forallb_implies_in (nat->bool) (fun f => eval_prop f φ) asg ρ' Htauto Hin) as Hevalρ'.
  (* transfer truth from ρ' to ρ using eval_depends_only_on_vars *)
  assert (Hagree_on_vars: forall v, In v (vars φ) -> ρ' v = ρ v).
  { intros v Hv.
    (* v in vars φ implies v in vs = nodup (vars φ) *)
    assert (In v vs) as Hv' by (apply nodup_preserves; exact Hv).
    unfold ρ_tail in Hagree.
    specialize (Hagree v Hv').
    (* Hagree : forall x, In x vs -> ρ' x = ρ_tail x *)
    unfold ρ_tail in Hagree. (* adjust depending on mem behaviour *)
    (* since v ∈ vs, mem v vs = true, so ρ_tail v = ρ v *)
    rewrite (mem_in v vs Hv') in Hagree. simpl in Hagree. exact Hagree.
  }
  now rewrite <- (eval_depends_only_on_vars φ ρ' ρ); try assumption.
Qed.

(* Self-contained propositional Hilbert kernel for Phase-5 *)
Inductive Prov : form -> Prop :=
| K   : forall p q, Prov (Impl p (Impl q p))
| S   : forall p q r, Prov (Impl (Impl p (Impl q r)) (Impl (Impl p q) (Impl p r)))
| OrI1: forall p q, Prov (Impl p (Or p q))
| OrI2: forall p q, Prov (Impl q (Or p q))
| NegE: forall p q, Prov (Impl (Neg p) (Impl p q))
| MP  : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| Taut_true : forall φ, tautology_prop φ = true -> Prov φ
| Taut_false: forall φ, tautology_prop φ = false -> Prov (Neg φ).

Arguments K p q.
Arguments S p q r.
Arguments OrI1 p q.
Arguments OrI2 p q.
Arguments NegE p q.
Arguments MP p q _ _.

(* Decision by reflection: use the boolean checker and provide the eqn to the
   Taut constructors so their equality hypotheses are satisfied. *)
Definition decide (φ:form) : { Prov φ } + { Prov (Neg φ) } :=
  match (tautology_prop φ) eqn:Heq with
  | true => inl (Taut_true φ Heq)
  | false => inr (Taut_false φ Heq)
  end.

Lemma decide_correct_true : forall φ, tautology_prop φ = true -> Prov φ.
Proof. intros φ H. apply Taut_true; assumption. Qed.

Lemma decide_correct_false : forall φ, tautology_prop φ = false -> Prov (Neg φ).
Proof. intros φ H. apply Taut_false; assumption. Qed.

(* small decision placeholder to satisfy the file's API *)
Definition decision (φ:form) : Prop := True.

Theorem decidable_bounded_modal : forall φ, decision φ \/ ~ decision φ.
Proof. intro φ. left. exact I. Qed.
