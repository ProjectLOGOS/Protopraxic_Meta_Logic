From Coq Require Import Logic.Classical.

(*
  S5_Independence_Barcan.v
  Independence tests for T, 4, 5 via counter-frames, and Barcan/Converse-Barcan
  under constant domains.
  Explicit proofs only.
*)

Section Frames.

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
    - simpl. exact I.
  Qed.
End NonReflexive_T.

Module NonTransitive_4.
  Inductive Wt := a | b | c.
  Definition Rt (x y:Wt) : Prop :=
    match x,y with
    | a,b => True
    | b,c => True
    | x,y => x = y
    end.
  Definition Ft : frame := {| W := Wt; R := Rt |}.

  Definition p (w:Wt) : Prop := match w with | a => False | b => True | c => False end.

  Lemma Four_fails : exists w, box (F:=Ft) p w /\ ~ box (F:=Ft) (box (F:=Ft) p) w.
  Proof.
    exists a. split.
    - intros u Hu. destruct u; simpl in *.
      + reflexivity.
      + exact I.
      + inversion Hu.
    - intro Hb.
      specialize (Hb b). simpl in Hb.
      assert (Hab: Rt a b) by auto.
      specialize (Hb Hab).
      specialize (Hb c). simpl in Hb.
      assert (Hbc: Rt b c) by auto.
      specialize (Hb Hbc). simpl in Hb. exact Hb.
  Qed.
End NonTransitive_4.

Module NonEuclidean_5.
  Inductive Wt := a | b | c.
  Definition Rt (x y:Wt) : Prop :=
    match x,y with
    | a,b => True
    | a,c => True
    | x,y => x = y
    end.
  Definition Ft : frame := {| W := Wt; R := Rt |}.

  Definition p (w:Wt) : Prop := match w with | c => True | _ => False end.

  Lemma Five_fails : exists w, dia (F:=Ft) p w /\ ~ box (F:=Ft) (dia (F:=Ft) p) w.
  Proof.
    exists a. split.
    - exists c. split; auto. simpl. exact I.
    - intro Hb. specialize (Hb b). simpl in Hb.
      assert (Hab: Rt a b) by auto.
      specialize (Hb Hab). destruct Hb as [u [Hbu Hpu]].
      destruct u; simpl in *.
      + inversion Hbu.
      + inversion Hbu.
      + exact Hpu.
  Qed.
End NonEuclidean_5.

End Frames.

Section Barcan_Constant.

Variable W : Type.
Variable R : W -> W -> Prop.

Definition box (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.

Variable D : Type.
Variable P : W -> D -> Prop.

Lemma Barcan_constant : forall w,
  (forall x:D, box (fun w => P w x) w) ->
  box (fun w => forall x:D, P w x) w.
Proof.
  intros w H u Hwu x. apply (H x u Hwu).
Qed.

Lemma Converse_Barcan_constant : forall w,
  box (fun w => forall x:D, P w x) w ->
  forall x:D, box (fun w => P w x) w.
Proof.
  intros w H x u Hwu. apply (H u Hwu).
Qed.

End Barcan_Constant.
