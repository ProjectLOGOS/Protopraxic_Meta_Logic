From Coq Require Import Logic.Classical.

Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

Record frame := {
  W : Type; R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

Fixpoint eval (F:frame) (v:valuation F) (w:(W F)) (φ:form) : Prop :=
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

Fixpoint nnf (φ:form) : form :=
  match φ with
  | Bot => Bot
  | Var n => Var n
  | Impl p q => Or (Neg (nnf p)) (nnf q)
  | And p q  => And (nnf p) (nnf q)
  | Or p q   => Or  (nnf p) (nnf q)
  | Neg p =>
      match p with
      | Bot => Or (Var 0) (Neg (Var 0))
      | Var n => Neg (Var n)
      | Impl a b => And (nnf a) (Neg (nnf b))
      | And a b  => Or (Neg (nnf a)) (Neg (nnf b))
      | Or a b   => And (Neg (nnf a)) (Neg (nnf b))
      | Neg a    => nnf a
      | Box a    => Dia (Neg (nnf a))
      | Dia a    => Box (Neg (nnf a))
      end
  | Box p => Box (nnf p)
  | Dia p => Dia (nnf p)
  end.

Lemma eval_true_placeholder : forall (F:frame) v w,
  eval F v w (Or (Var 0) (Neg (Var 0))).
Proof.
  intros F v w. destruct (classic (v 0 w)) as [H|H]; [left|right]; exact H.
Qed.

Lemma nnf_correct :
  forall (F:frame) v w φ, eval F v w (nnf φ) <-> eval F v w φ.
Proof.
  intros F v w φ. induction φ; simpl.
  - split; intro H; exact H.
  - split; intro H; exact H.
  - split.
    + intro H. intros Hp.
      destruct H as [Hn|Hq].
      * exfalso. apply Hn. apply (proj1 (IHφ1)). exact Hp.
      * apply (proj2 (IHφ2)). exact Hq.
    + intro H. destruct (classic (eval F v w φ1)) as [Hp|Hnp].
      * right. apply (proj1 (IHφ2)). apply H. exact Hp.
      * left. intro Hp. apply Hnp. apply (proj2 (IHφ1)). exact Hp.
  - rewrite IHφ1, IHφ2. split; intro H; assumption.
  - rewrite IHφ1, IHφ2. split; intro H; assumption.
  - destruct φ; simpl in *.
    + split; intro _; apply eval_true_placeholder.
    + split; intro H; exact H.
    + split.
      * intro H. destruct (IHφ1) as [IH1a IH1b]. destruct (IHφ2) as [IH2a IH2b].
        intros Hp. destruct H as [Hp' Hnq]. apply Hnq. apply IH2a. apply (H Hp').
      * intro H. split.
        { apply (proj2 IHφ1). intro Hp. apply (H (proj1 IHφ1 Hp)). }
        { intro Hq. apply (H (proj1 IHφ2 Hq)). }
    + split.
      * intro H. destruct H as [Hna|Hnb].
        { left. intro Hp. apply Hna. apply (proj1 IHφ1). exact Hp. }
        { right. intro Hq. apply Hnb. apply (proj1 IHφ2). exact Hq. }
      * intro H. destruct H as [Hna Hnb].
        { left. intro Hp. apply Hna. apply (proj2 IHφ1). exact Hp. }
        { right. intro Hq. apply Hnb. apply (proj2 IHφ2). exact Hq. }
    + split.
      * intro H. destruct H as [Hna Hnb].
        { left. intro Hp. apply Hna. apply (proj1 IHφ1). exact Hp. }
        { right. intro Hq. apply Hnb. apply (proj1 IHφ2). exact Hq. }
      * intro H. destruct H as [Hna|Hnb].
        { split; intro Hp; [apply Hna | apply eval_true_placeholder]. }
        { split; [apply eval_true_placeholder | intro Hq; apply Hnb]. }
    + rewrite IHφ. split; intro H; exact H.
    + split.
      * intro H. destruct H as [u [Hwu H]]. intro Hb. apply (H (Hb u Hwu)).
      * intro H. destruct (classic (exists u, R F w u /\ ~ eval F v u φ)) as [Hex|Hno].
        { destruct Hex as [u [Hwu Hn]]. exists u. split; [assumption|]. intro Hu. apply Hn. exact Hu. }
        { exfalso. apply H. intro u Hwu.
          destruct (classic (eval F v u φ)) as [Hp|Hnp]; [exact Hp|].
          apply Hno. exists u. split; [assumption| exact Hnp]. }
    + split.
      * intro H. intro u Hwu Hu. apply H. exists u. split; [assumption| exact Hu].
      * intro H. destruct (classic (exists u, R F w u /\ eval F v u φ)) as [Hex|Hno].
        { exfalso. destruct Hex as [u [Hwu Hu]]. apply (H u Hwu Hu). }
        { intro Hd. destruct Hd as [u [Hwu Hu]]. apply Hno. exists u. split; [assumption| exact Hu]. }
  - rewrite IHφ. split; intro H; exact H.
  - rewrite IHφ. split; intro H; exact H.
Qed.
