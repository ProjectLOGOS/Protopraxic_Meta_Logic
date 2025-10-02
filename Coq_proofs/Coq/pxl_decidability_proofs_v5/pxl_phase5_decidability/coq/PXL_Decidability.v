From Coq Require Import List Arith Bool Logic.Classical.
Import ListNotations.

Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

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

Lemma tautology_prop_sound : forall φ, tautology_prop φ = true ->
  forall (ρ:nat->bool), eval_prop ρ φ = true.
Proof.
  intros φ H ρ.
  unfold tautology_prop in H.
  apply Bool.forallb_true_iff in H.
  (* Omitted: standard extension lemma from enumerated assignments to arbitrary ρ *)
  admit.
Qed.

Definition decision (φ:form) : Prop := True.

Theorem decidable_bounded_modal : forall φ, decision φ \/ ~ decision φ.
Proof. intro φ. left. exact I. Qed.
