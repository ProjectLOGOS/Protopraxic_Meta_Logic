This file collects the full Coq statements (source snippets) for the main Phase-3 files so you can copy/paste them into an editor.

-- S5_Kripke.v (key declarations)
(* ...existing code... *)

Record frame := { W : Type; R : W -> W -> Prop }.

Definition box {W} (R : W -> W -> Prop) (p : W -> Prop) : W -> Prop :=
  fun w => forall v, R w v -> p v.

Definition dia {W} (R : W -> W -> Prop) (p : W -> Prop) : W -> Prop :=
  fun w => exists v, R w v /\n+    p v.

Lemma K_sem : (* K semantic statement *)
  forall W (R : W->W->Prop) p q, (* ... *) True.

(* ...existing code... *)

-- PXL_Deep_Soundness.v (key declarations)
(* ...existing code... *)

Inductive form :=
  | Atom : nat -> form
  | Bot : form
  | Imp : form -> form -> form
  | Box : form -> form.

Fixpoint eval {W} (v : nat -> W -> Prop) (w : W) (φ : form) {struct φ} : Prop :=
  match φ with
  | Atom n => v n w
  | Bot => False
  | Imp φ ψ => eval v w φ -> eval v w ψ
  | Box φ => forall u, (* R w u -> *) eval v u φ
  end.

Inductive Prov : form -> Type :=
  | Ax : (* axioms *) Prov (* ... *)
  | MP : forall φ ψ, Prov (Imp φ ψ) -> Prov φ -> Prov ψ
  | Nec : forall φ, Prov φ -> Prov (Box φ).

Fixpoint soundness (p : Prov φ) : (* ... *) True :=
  (* proof by recursion over p *)
  True.

(* ...existing code... *)

-- S5_Independence_Barcan.v (key declarations)
(* ...existing code... *)

From PXLs Require Import S5_CounterModels.

Lemma Four_fails : (* there exists a model where Box φ -> Box Box φ fails *)
  True.

Lemma Five_fails : (* there exists a model where Dia Box φ -> Box Dia φ fails *)
  True.

Section Barcan_Constant.
  Variable dom : Type.
  Hypothesis const_dom : True.

  Lemma Barcan_constant : (* ... *) True.
  Lemma Converse_Barcan_constant : (* ... *) True.
End Barcan_Constant.

(* ...existing code... *)
PHASE 3 — Full Coq statements (selected files)

This file contains the full Coq source excerpts (lemmas and proofs) for the Phase‑3 artifacts so you can copy/paste or inspect them in one place.

---

File: PXL_Deep_Soundness.v

```coq
From Coq Require Import Logic.Classical.

(*
  PXL_Deep_Soundness.v
  Deep embedding of a propositional modal language with S5 rules.
  Proves: If Prov φ then φ is valid on any frame with equivalence R.
  Explicit proofs only.
*)

Section Deep.

(* Syntax *)
Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

(* Frames and semantics *)
Record frame := {
  W : Type;
  R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

Fixpoint eval (F:frame) (v:valuation F) (w:W F) (φ:form) {struct φ} : Prop :=
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

Definition valid_on (F:frame) (φ:form) : Prop :=
  forall (v:valuation F) (w:W F), eval F v w φ.

(* Proof system *)
Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r,
    Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

(* Soundness of axioms and rules *)
Lemma sound_K : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (Box (Impl p q)) (Impl (Box p) (Box q))).
Proof.
  intros F v w p q Hb Hp u Hwu.
  exact ((Hb u Hwu) (Hp u Hwu)).
Qed.

Lemma sound_T : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Box p) p).
Proof.
  intros F v w p Hb. apply Hb. apply (R_refl F).
Qed.

Lemma sound_4 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Box p) (Box (Box p))).
Proof.
  intros F v w p Hb u Hwu t Hut. apply Hb. eapply (R_trans F); eauto.
Qed.

Lemma sound_5 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Dia p) (Box (Dia p))).
Proof.
  intros F v w p [u [Hwu Hpu]] t Hwt. exists u. split.
  - eapply (R_trans F). apply (R_symm F). exact Hwt. exact Hwu.
  - exact Hpu.
Qed.

Lemma sound_PL_imp : forall (F:frame) (v:valuation F) (w:W F) (p q r:form),
  eval F v w (Impl (Impl p q) (Impl (Impl q r) (Impl p r))).
Proof.
  intros F v w p q r Hpqr Hqr Hp. apply Hqr. apply Hpqr. exact Hp.
Qed.

Lemma sound_PL_and1 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (And p q) p).
Proof.
  intros F v w p q [Hp _]. exact Hp.
Qed.

Lemma sound_PL_and2 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (And p q) q).
Proof.
  intros F v w p q [_ Hq]. exact Hq.
Qed.

Lemma sound_mp : forall (F:frame) (p q:form),
  valid_on F (Impl p q) -> valid_on F p -> valid_on F q.
Proof.
  intros F p q Hpq Hp v w. exact ((Hpq v w) (Hp v w)).
Qed.

Lemma sound_nec : forall (F:frame) (p:form),
  valid_on F p -> valid_on F (Box p).
Proof.
  intros F p H v w u Hwu. apply (H v u).
Qed.

Fixpoint soundness (F:frame) (φ:form) (H:Prov φ) : valid_on F φ :=
  match H in Prov φ return valid_on F φ with
  | ax_K p q => fun v w => sound_K F v w p q
  | ax_T p => fun v w => sound_T F v w p
  | ax_4 p => fun v w => sound_4 F v w p
  | ax_5 p => fun v w => sound_5 F v w p
  | ax_PL_imp p q r => fun v w => sound_PL_imp F v w p q r
  | ax_PL_and1 p q => fun v w => sound_PL_and1 F v w p q
  | ax_PL_and2 p q => fun v w => sound_PL_and2 F v w p q
  | mp p q H1 H2 => fun v w => sound_mp F p q (soundness F (Impl p q) H1) (soundness F p H2) v w
  | nec p H1 => fun v w => sound_nec F p (soundness F p H1) v w
  end.

End Deep.
```

---

File: S5_Kripke.v

```coq
From Coq Require Import Logic.Classical.

(*
  S5_Kripke.v
  Semantic S5 on Kripke frames with an equivalence accessibility.
  Modal propositions are predicates over worlds (W -> Prop).
  Box p w := forall w', R w w' -> p w'
  Dia p w := exists w', R w w' /\ p w'
  Explicit proofs only. UTF-8, no markdown fences.
*)

Section S5_Semantics.

Variable W : Type.
Variable R : W -> W -> Prop.

Hypothesis R_refl  : forall w, R w w.
Hypothesis R_symm  : forall w u, R w u -> R u w.
Hypothesis R_trans : forall w u v, R w u -> R u v -> R w v.

Definition box (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.
Definition dia (p:W->Prop) : W->Prop := fun w => exists u, R w u /\ p u.

Lemma K_sem : forall p q, (forall w, box (fun x => p x -> q x) w -> (box p w -> box q w)).
Proof.
  intros p q w Himp Hbp u Hwu.
  apply (Himp u Hwu).
  apply (Hbp u Hwu).
Qed.

Lemma T_sem : forall p, forall w, box p w -> p w.
Proof.
  intros p w Hb. apply Hb. apply R_refl.
Qed.

Lemma Four_sem : forall p, forall w, box p w -> box (box p) w.
Proof.
  intros p w Hb u Hwu v Huv.
  apply Hb. eapply R_trans; eauto.
Qed.

Lemma Five_sem : forall p, forall w, dia p w -> box (dia p) w.
Proof.
  intros p w [u [Hwu Hpu]] v Hwv.
  exists u. split; [ | exact Hpu].
  (* In equivalence relations: from R w v and R w u derive R v u via symmetry+transitivity. *)
  apply R_trans with (u:=w).
  - apply R_symm. exact Hwv.
  - exact Hwu.
Qed.

Lemma dual_box_dia : forall p w, box p w <-> ~ dia (fun x => ~ p x) w.
Proof.
  intros p w. split.
  - intros Hb [u [Hwu Hnp]]. apply Hnp. apply Hb; assumption.
  - intros Hnot u Hwu. destruct (classic (p u)) as [Hp|Hn].
    + exact Hp.
    + exfalso. apply Hnot. exists u. split; [assumption| exact Hn].
Qed.

Lemma dual_dia_box : forall p w, dia p w <-> ~ box (fun x => ~ p x) w.
Proof.
  intros p w. split.
  - intros [u [Hwu Hpu]] Hb. apply (Hb u Hwu). exact Hpu.
  - intros Hnot. destruct (classic (exists u, R w u /\ p u)) as [Hex|Hno].
    + exact Hex.
    + exfalso. apply Hnot. intros u Hwu Hu.
      apply Hno. exists u. split; [assumption| exact Hu].
Qed.

Lemma mono_box : forall p q w, (forall x, p x -> q x) -> box p w -> box q w.
Proof.
  intros p q w Himp Hb u Hwu. apply Himp, Hb; assumption.
Qed.

Lemma mono_dia : forall p q w, (forall x, p x -> q x) -> dia p w -> dia q w.
Proof.
  intros p q w Himp [u [Hwu Hpu]]. exists u. split; [assumption| apply Himp; assumption].
Qed.

Lemma dist_box_and : forall p q w, box (fun x => p x /\ q x) w <-> (box p w /\ box q w).
Proof.
  intros p q w. split.
  - intros Hb. split; intros u Hwu.
    + destruct (Hb u Hwu) as [H1 H2]. apply H1.
    + destruct (Hb u Hwu) as [H1 H2]. apply H2.
  - intros [Hp Hq] u Hwu. split; [apply Hp | apply Hq]; assumption.
Qed.

Lemma dist_dia_or : forall p q w, dia (fun x => p x \/ q x) w <-> (dia p w \/ dia q w).
Proof.
  intros p q w. split.
  - intros [u [Hwu [Hp|Hq]]]; [left; exists u; split; assumption | right; exists u; split; assumption].
  - intros [[u [Hwu Hp]] | [u [Hwu Hq]]];
    [ exists u; split; [assumption | left; assumption ]
    | exists u; split; [assumption | right; assumption ] ].
Qed.

Lemma collapse_box : forall p w, box p w <-> box (box p) w.
Proof.
  intros p w. split.
  - intros Hb u Hwu v Huv. apply Hb. eapply R_trans; eauto.
  - intros Hbb. apply (Hbb w). apply R_refl.
Qed.

Lemma collapse_dia_box : forall p w, dia p w <-> box (dia p) w.
Proof.
  intros p w. split.
  - apply Five_sem.
  - intros Hbd. destruct (Hbd w (R_refl w)) as [u [Hwu Hpu]].
    exists u. split; assumption.
Qed.

Lemma collapse_box_dia : forall p w, box p w <-> dia (box p) w.
Proof.
  intros p w. split.
  - intros Hb. exists w. split; [apply R_refl|]. intros u Hwu. apply Hb. exact Hwu.
  - intros [u [Hwu Hbp]] v Hwv.
    (* From R w u and R w v derive R u v using symmetry on Hwu then transitivity, then apply Hbp at u *)
    pose proof (R_symm _ _ Hwu) as Huw.
    pose proof (R_trans _ _ _ Huw Hwv) as Huv.
    apply Hbp. exact Huv.
Qed.

End S5_Semantics.
```

---

File: S5_Independence_Barcan.v

```coq
From Coq Require Import Logic.Classical.

(*
  S5_Independence_Barcan.v
  Independence tests for T, 4, 5 via counter-frames, and Barcan/Converse-Barcan
  under constant domains.
  Explicit proofs only.
*)

Record frame := { W : Type; R : W -> W -> Prop }.

Definition box {F:frame} (p:W F -> Prop) : W F -> Prop := fun w => forall u, R F w u -> p u.
Definition dia {F:frame} (p:W F -> Prop) : W F -> Prop := fun w => exists u, R F w u /\ p u.

Module NonReflexive_T.
  Inductive Wt := w0 | w1.
  Definition Rt (x y:Wt) : Prop := match x, y with | w0, w1 => True | w1, w1 => True | _, _ => False end.
  Definition Ft : frame := {| W := Wt; R := Rt |}.

  Definition p (w:Wt) : Prop := match w with | w0 => False | w1 => True end.

  Lemma T_fails : exists w, box (F:=Ft) p w /\ ~ p w.
  Proof.
    exists w0. split.
    - intros u Hu. destruct u; simpl in *.
      + inversion Hu.
      + exact I.
    - simpl. intro H. inversion H.
  Qed.
End NonReflexive_T.

From PXLs Require Import S5_CounterModels.

(* See `S5_CounterModels.v` for a self-contained proof of Five_fails. *)

Section Barcan_Constant.

Variable W : Type.
Variable R : W -> W -> Prop.

Definition box_const (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.

Variable D : Type.
Variable P : W -> D -> Prop.

Lemma Barcan_constant : forall w,
  (forall x:D, box_const (fun w => P w x) w) ->
  box_const (fun w => forall x:D, P w x) w.
Proof.
  intros w H u Hwu x. apply (H x u Hwu).
Qed.

Lemma Converse_Barcan_constant : forall w,
  box_const (fun w => forall x:D, P w x) w ->
  forall x:D, box_const (fun w => P w x) w.
Proof.
  intros w H x u Hwu. apply (H u Hwu).
Qed.

End Barcan_Constant.
```

---

File: S5_CounterModels.v

```coq
From Coq Require Import Logic.Classical.

(* Small, self-contained countermodel file showing failures of 4 and 5.
   Uses a tiny deep embedding of propositional modal formulas with
   local `model` and `satisfies` semantics so it doesn't depend on
   the rest of the packet. *)

Inductive form := atom (n: nat) | box (φ: form) | dia (φ: form).

Record model := {
  world : Type;
  R : world -> world -> Prop;
  D : world -> Type; (* constant domain allowed *)
  V : world -> nat -> Prop
}.

Fixpoint satisfies (M: model) (w: world M) (φ: form) : Prop :=
  match φ with
  | atom n => V M w n
  | box ψ => forall u, R M w u -> satisfies M u ψ
  | dia ψ => exists u, R M w u /\ satisfies M u ψ
  end.

Section CounterModels.

(* Three-worlds used by both countermodels *)
Inductive W := w0 | w1 | w2.

(* ---------- Four_fails model ---------- *)
Definition R4 (x y: W) : Prop :=
  match x, y with
  | w0, w1 => True
  | w1, w2 => True
  | _, _   => False
  end.

Definition Dconst (w:W) : Type := unit.

(* We'll use atom 0 as the propositional p *)
Definition V4 (w: W) (n: nat) : Prop :=
  match n, w with
  | 0, w1 => True
  | 0, w2 => False
  | 0, w0 => True
  | _, _ => False
  end.

Definition M4 : model := {| world := W; R := R4; D := Dconst; V := V4 |}.

Lemma Four_fails : exists w: W, satisfies M4 w (box (atom 0)) /\ ~ satisfies M4 w (box (box (atom 0))).
Proof.
  exists w0. split.
  - unfold satisfies. intros u Hru. destruct u; simpl in Hru; try inversion Hru; simpl; auto.
  - unfold not. intro H.
    assert (H01: R4 w0 w1) by (simpl; auto).
    specialize (H w1 H01).
    assert (H12: R4 w1 w2) by (simpl; auto).
    specialize (H w2 H12). simpl in H. exact H.
Qed.

(* ---------- Five_fails model ---------- *)
Definition R5 (x y: W) : Prop :=
  match x, y with
  | w0, w1 => True
  | w0, w2 => True
  | _, _   => False
  end.

Definition V5 (w: W) (n: nat) : Prop :=
  match n, w with
  | 0, w1 => True
  | 0, w2 => False
  | 0, w0 => False
  | _, _ => False
  end.

Definition M5 : model := {| world := W; R := R5; D := Dconst; V := V5 |}.

Lemma Five_fails : exists w:W, satisfies M5 w (dia (atom 0)) /\ ~ satisfies M5 w (box (dia (atom 0))).
Proof.
  exists w0. split.
  - unfold satisfies. exists w1. split; [simpl; auto | simpl; auto].
  - unfold not. intro H.
    assert (H02: R5 w0 w2) by (simpl; auto).
    specialize (H w2 H02). simpl in H.
    destruct H as [u [Hru Hsat]]. destruct u; simpl in Hru; inversion Hru.
Qed.

End CounterModels.
```
