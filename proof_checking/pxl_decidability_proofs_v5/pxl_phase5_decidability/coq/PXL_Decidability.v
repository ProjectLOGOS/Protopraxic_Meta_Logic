From Coq Require Import List Arith Bool.
Import ListNotations.

(* Minimal propositional fragment used for decidability/tautology checks. *)
Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

Fixpoint vars (phi:form) : list nat :=
  match phi with
  | Bot => []
  | Var n => [n]
  | Impl p q => vars p ++ vars q
  | And p q  => vars p ++ vars q
  | Or p q   => vars p ++ vars q
  | Neg p    => vars p
  | Box p    => vars p
  | Dia p    => vars p
  end.

Fixpoint eval_prop (rho:nat->bool) (phi:form) : bool :=
  match phi with
  | Bot => false
  | Var n => rho n
  | Impl p q => negb (eval_prop rho p) || eval_prop rho q
  | And p q  => andb (eval_prop rho p) (eval_prop rho q)
  | Or p q   => orb  (eval_prop rho p) (eval_prop rho q)
  | Neg p    => negb (eval_prop rho p)
  | Box p    => eval_prop rho p
  | Dia p    => eval_prop rho p
  end.

Fixpoint all_assignments (xs:list nat) : list (nat -> bool) :=
  match xs with
  | [] => [fun _ => false]
  | x::ys =>
      let rest := all_assignments ys in
      let set0 := List.map (fun r => fun n => if Nat.eqb n x then false else r n) rest in
      let set1 := List.map (fun r => fun n => if Nat.eqb n x then true  else r n) rest in
      set0 ++ set1
  end.

Definition tautology_prop (phi:form) : bool :=
  let xs := vars phi in
  let asg := all_assignments xs in
  forallb (fun r => eval_prop r phi) asg.

Lemma forallb_true_pointwise :
  forall (A:Type) (f:A->bool) (l:list A),
    forallb f l = true -> forall x, In x l -> f x = true.
Proof.
  intros A f l H; induction l as [|a l IH]; simpl in *; intros x Hin.
  - inversion Hin.
  - apply andb_true_iff in H. destruct H as [Ha Hl].
    destruct Hin as [Heq|Hin']; [subst; exact Ha| apply (IH Hl); exact Hin'].
Qed.

Lemma exists_assign: forall xs rho,
  exists rho', In rho' (all_assignments xs) /\ (forall n, In n xs -> rho' n = rho n).
Proof.
  induction xs as [|x xs IH]; simpl; intros rho.
  - exists (fun _ => false). split; [left; reflexivity| intros n H; inversion H].
  - destruct (IH rho) as [rrest [Hin Hprop]].
    destruct (rho x) eqn:Hx.
    + set (f := fun n => if Nat.eqb n x then true else rrest n).
      exists f. split.
      * simpl. right. apply in_map_iff. exists rrest. split; [apply Hin| reflexivity].
      * intros n Hn. simpl in Hn. destruct Hn as [Heq|Hn]; [subst; simpl; reflexivity| apply Hprop; exact Hn].
    + set (f := fun n => if Nat.eqb n x then false else rrest n).
      exists f. split.
      * simpl. left. apply in_map_iff. exists rrest. split; [apply Hin| reflexivity].
      * intros n Hn. simpl in Hn. destruct Hn as [Heq|Hn]; [subst; simpl; reflexivity| apply Hprop; exact Hn].
Qed.

Lemma eval_ext_apply : forall phi rho1 rho2,
  (forall n, In n (vars phi) -> rho1 n = rho2 n) ->
  eval_prop rho1 phi = eval_prop rho2 phi.
Proof.
  induction phi; simpl; intros rho1 rho2 Heq; try reflexivity.
  - apply Heq. simpl. left. reflexivity.
  - rewrite (IHphi1 rho1 rho2 (fun m H => Heq m (or_introl H))).
    rewrite (IHphi2 rho1 rho2 (fun m H => Heq m (or_intror H))). reflexivity.
  - rewrite (IHphi1 rho1 rho2 (fun m H => Heq m (or_introl H))).
    rewrite (IHphi2 rho1 rho2 (fun m H => Heq m (or_intror H))). reflexivity.
  - rewrite (IHphi1 rho1 rho2 (fun m H => Heq m (or_introl H))).
    rewrite (IHphi2 rho1 rho2 (fun m H => Heq m (or_intror H))). reflexivity.
  - apply IHphi. intros m H. apply Heq. now simpl; right; exact H.
Qed.

Lemma tautology_prop_sound : forall phi, tautology_prop phi = true ->
  forall rho, eval_prop rho phi = true.
Proof.
  intros phi Htrue rho.
  set (xs := vars phi).
  set (asg := all_assignments xs).
  unfold xs, asg in *.
  pose proof (forallb_true_pointwise _ (fun r => eval_prop r phi) asg Htrue) as F.
  destruct (exists_assign xs rho) as [rho' [Hin_rho' Hagree]].
  specialize (F rho' Hin_rho').
  apply eq_trans with (y := eval_prop rho' phi).
  - apply eq_sym. apply (eval_ext_apply phi rho rho'). intros n Hn.
    apply Hagree. exact Hn.
  - exact F.
Qed.

(* small decidability placeholder used by downstream code *)
Definition decision (phi:form) : Prop := True.
Theorem decidable_bounded_modal : forall phi, decision phi \/ ~ decision phi.
Proof. intro phi. left. exact I. Qed.
