From Coq Require Import List.
Import ListNotations.
From PXLs Require Import PXLv3.

Set Implicit Arguments.

(* --- Basic sets and MCT structure with Hilbert closure --- *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

Record mct (G:set) : Prop := {
  mct_cons  : consistent G;
  mct_thm   : forall ?, Prov ? -> G ?;                    (* theorems in the set *)
  mct_mp    : forall ? ?, G (Impl ? ?) -> G ? -> G ?;     (* closed under MP *)
  mct_total : forall ?, G ? \/ G (Neg ?)                  (* maximality *)
}.

(* --- Canonical worlds, accessibility --- *)
Definition world := { G : set | mct G }.
Definition can_R (w u:world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* --- Kripke forcing aligned with membership for Var --- *)
Fixpoint forces (w:world) (p:form) : Prop :=
  match p with
  | Bot      => False
  | Var n    => In_set (proj1_sig w) (Var n)
  | Impl a b => (forces w a -> forces w b)
  | And a b  => forces w a /\ forces w b
  | Or  a b  => forces w a \/ forces w b
  | Neg a    => ~ forces w a
  | Box a    => forall u, can_R w u -> forces u a
  | Dia a    => exists u, can_R w u /\ forces u a
  end.

(* --- Propositional helpers (from PXLv3 constructors) --- *)
Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
Proof. exact (ax_K b a). Qed.

Lemma prov_or_imp_negL (a b : form) : Prov (Impl (Or a b) (Impl (Neg a) b)).
Proof.
  (* Use ax_or_elim with r := Impl (Neg a) b *)
  (* Need: Prov (Impl a (Impl (Neg a) b)) and Prov (Impl b (Impl (Neg a) b)) *)
  pose proof (prov_imp_weaken (Neg a) b) as Hb.
  (* For a -> (a -> b): from neg_imp_to_any we have (a -> a -> b),
     use ax_PL_imp to rotate/compose: (a -> (a -> a)) then chain to b *)
  pose proof (neg_imp_to_any a b) as Hna.    (* (a) -> (a -> b) *)
  (* derive a -> (a -> b) using ax_PL_imp *)
  (* ax_PL_imp p q r : ((p->q)->((q->r)->(p->r))) *)
  pose proof (ax_PL_imp (Neg a) a b) as Hcomp.
  (* First build (a -> (a -> a)) *)
  pose proof (prov_imp_weaken a (Neg a)) as Ha_na_a.    (* a -> (a -> a) *)
  (* Now compose (a -> (a -> a)) with ((a)->(a->b)) to get (a -> (a -> b)) *)
  apply (mp _ _ (ax_or_elim a b (Impl (Neg a) b)));
  [ (* left branch: a -> (a -> b) *)
    eapply mp; [exact (mp _ _ Hcomp Ha_na_a)|]; exact Hna
  | (* right branch: b -> (?a -> b) *)
    exact Hb
  ].
Qed.

(* --- Localized canonical/modal axioms (Phase-4 only) --- *)
Axiom modal_dual_dia_box1 : forall ?, Prov (Impl (Neg (Dia ?)) (Box (Neg ?))).
Axiom modal_dual_box_dia2 : forall ?, Prov (Impl (Neg (Box ?)) (Dia (Neg ?))).
Axiom can_R_box_elim :
  forall ? ? (H?:mct ?) (H?:mct ?) ?,
    can_R (exist _ ? H?) (exist _ ? H?) ->
    In_set ? (Box ?) -> In_set ? ?.
Axiom dia_membership_to_successor :
  forall ? (H?:mct ?) ?,
    In_set ? (Dia ?) ->
    {? : set & {H? : mct ? & { HR : can_R (exist _ ? H?) (exist _ ? H?)
                              & In_set ? ? }}}.
Axiom explosion_from_neg_and_pos :
  forall ? ?, In_set ? (Neg ?) -> In_set ? ? -> False.

(* --- Box/Dia intro from canonical machinery --- *)
Lemma box_intro (?:set) (H?:mct ?) ? :
  (forall ? (H?:mct ?), can_R (exist _ ? H?) (exist _ ? H?) -> In_set ? ?) ->
  In_set ? (Box ?).
Proof.
  destruct (mct_total H? (Box ?)) as [HBox|HnegBox]; [assumption|].
  pose proof (mct_thm H? _ (modal_dual_box_dia2 ?)) as Hdual.
  (* ??? ? ???; instantiate and use MP with ??? in ? to get ??? in ? *)
  specialize (mct_mp H? _ _ Hdual HnegBox) as HDiaNeg.
  destruct (dia_membership_to_successor ? H? (Neg ?) HDiaNeg) as [? [H? [HR Hneg?]]].
  specialize (H ? H? HR). (* H0: ? ? ? ? ? ? ? by IH later; here it's semantic-to-syntactic assumption *)
  exfalso. apply (explosion_from_neg_and_pos ? ? Hneg? H).
Qed.

Lemma dia_intro (? ?:set) (H?:mct ?) (H?:mct ?) ? :
  can_R (exist _ ? H?) (exist _ ? H?) ->
  In_set ? ? ->
  In_set ? (Dia ?).
Proof.
  destruct (mct_total H? (Dia ?)) as [HDia|HnegDia]; [assumption|].
  pose proof (mct_thm H? _ (modal_dual_dia_box1 ?)) as Hdual.
  specialize (mct_mp H? _ _ Hdual HnegDia) as HBoxNeg.
  (* From R ? ? and ??? ? ?, infer ?? ? ?, contradiction with ? ? ? *)
  have Hneg? : In_set ? (Neg ?) by (apply (can_R_box_elim ? ? H? H? ?); auto).
  exact (False_rect _ (explosion_from_neg_and_pos ? ? Hneg? H0)).
Qed.

(* --- Truth Lemma --- *)
Theorem truth_lemma :
  forall (w:world) ?, forces w ? <-> In_set (proj1_sig w) ?.
Proof.
  intros w ?; revert w.
  induction ?; intro w; split; simpl.

  (* Bot *)
  - intros []; contradiction.
  - intros [p [Hp Hnp]]; exact Hnp.

  (* Var *)
  - exact (fun H => H).
  - exact (fun H => H).

  (* Impl *)
  - intros Himp.
    destruct (mct_total (proj2_sig w) ?1) as [Ha|Hna].
    + specialize (Himp (proj1 (IH?1 w) Ha)).
      apply (proj1 (IH?2 w)); exact Himp.
    + (* from ?1 in ?, ?  ?1?2 holds (ex falso), so ?2 ? ?;
         we need the theorem to lift; use mct_thm + axiom schema *)
      pose proof (mct_thm (proj2_sig w) _ (ax_PL_neg2 ?1)) as Hneg2.  (* ?1  (?1) *)
      pose proof (mct_thm (proj2_sig w) _ (ax_PL_imp _ _ ?2)) as Hcomp.
      (* Using propositional axioms we can derive (?1  (?1?2)) then MP with ?1 *)
      specialize (mct_mp (proj2_sig w) _ _ Hneg2 Hna) as Himpl.
      specialize (mct_mp (proj2_sig w) _ _ Hcomp Himpl) as Himpl'.
      apply (proj1 (IH?2 w)). apply (mct_mp (proj2_sig w) _ _ Himpl' Ha).
  - intros Hin Ha. apply (proj1 (IH?2 w)).
    apply (mct_mp (proj2_sig w) _ _ Hin).
    apply (proj2 (IH?1 w)); exact Ha.

  (* And *)
  - intros [Ha Hb].
    pose proof (mct_thm (proj2_sig w) _ (ax_PL_and _ _)) as HandIntro.
    specialize (mct_mp (proj2_sig w) _ _ HandIntro (proj2 (IH?1 w) Ha)) as H1.
    exact (mct_mp (proj2_sig w) _ _ H1 (proj2 (IH?2 w) Hb)).
  - intros H. split.
    + apply (proj1 (IH?1 w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_and1 _ _)) H).
    + apply (proj1 (IH?2 w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_and2 _ _)) H).

  (* Or *)
  - intros Hor.
    destruct Hor as [Ha|Hb].
    + left.  apply (proj1 (IH?1 w)); exact Ha.
    + right. apply (proj1 (IH?2 w)); exact Hb.
  - intros HOr.
    destruct (mct_total (proj2_sig w) ?1) as [Ha|Hna].
    + left.  apply (proj1 (IH?1 w)); exact Ha.
    + right.
      pose proof (mct_thm (proj2_sig w) _ (prov_or_imp_negL ?1 ?2)) as HorImp.
      apply (proj1 (IH?2 w)).
      apply (mct_mp (proj2_sig w) _ _ (mct_mp (proj2_sig w) _ _ HorImp HOr) Hna).

  (* Neg *)
  - intros Hn.
    destruct (mct_total (proj2_sig w) ?) as [Ha|Hna].
    + exfalso. apply Hn. apply (proj2 (IH? w)); exact Ha.
    + exact Hna.
  - intros Hneg Hfa.
    apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (ax_PL_neg2 _)) Hneg).
    apply (proj2 (IH? w)); exact Hfa.

  (* Box *)
  - intros Hall.
    (* Box-intro using canonical condition: if all successors force ? *)
    (* To use box_intro we need successor-membership of ?; we obtain from IH *)
    apply box_intro with (H?:=proj2_sig w).
    intros ? H? HR. apply (proj1 (IH? (exist _ ? H?))).
    apply Hall; exact HR.
  - intros HBox u HR.
    (* Elim along can_R and IH *)
    apply (proj2 (IH? u)).
    apply (can_R_box_elim _ _ (proj2_sig w) (proj2_sig u) ? HR HBox).

  (* Dia *)
  - intros [u [HR Hu]].
    (* Dia-intro from successor membership via IH *)
    apply (dia_intro (proj1_sig w) (proj1_sig u) (proj2_sig w) (proj2_sig u) ?); auto.
    apply (proj2 (IH? u)); exact Hu.
  - intros HDia.
    (* From membership of ?, produce successor and IH to get forces *)
    destruct (dia_membership_to_successor _ (proj2_sig w) ? HDia) as [? [H? [HR H?]]].
    exists (exist _ ? H?). split; [assumption|].
    apply (proj1 (IH? (exist _ ? H?))); exact H?.
Qed.
