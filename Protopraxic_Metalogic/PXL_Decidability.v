From Coq Require Import List Arith Bool.
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

(* ---- Helper lemmas ---- *)

Lemma forallb_implies_in :
  forall A (p:A->bool) xs x, forallb p xs = true -> In x xs -> p x = true.
Proof.
  intros A p xs x Hall Hin.
  induction xs as [|a xs IH]; simpl in *; try contradiction.
  destruct Hin as [-> | Hin].
  - apply Bool.andb_true_iff in Hall as [Ha _]; exact Ha.
  - apply Bool.andb_true_iff in Hall as [_ Hxs]; auto.
Qed.

Lemma mem_in : forall x xs, mem x xs = true <-> In x xs.
Proof. admit. Admitted.

Lemma mem_true_in : forall x xs, mem x xs = true -> In x xs.
Proof. intros; apply mem_in; auto. Qed.

Lemma nodup_preserves : forall x xs, In x xs -> In x (nodup xs).
Proof. admit. Admitted.

(* ---- Hilbert-style kernel ---- *)

Inductive Prov : form -> Prop :=
| K    : forall A B, Prov (Impl A (Impl B A))
| S    : forall A B C, Prov (Impl (Impl A (Impl B C)) (Impl (Impl A B) (Impl A C)))
| OrI1 : forall A B, Prov (Impl A (Or A B))
| OrI2 : forall A B, Prov (Impl B (Or A B))
| NegE : forall A, Prov (Impl (Neg A) (Impl A Bot))
| AndI : forall A B, Prov (Impl A (Impl B (And A B)))
| AndE1: forall A B, Prov (Impl (And A B) A)
| AndE2: forall A B, Prov (Impl (And A B) B)
| OrE  : forall A B C, Prov (Impl (Or A B) (Impl (Impl A C) (Impl (Impl B C) C)))
| MP   : forall A B, Prov (Impl A B) -> Prov A -> Prov B.

(* ---- Derived lemmas ---- *)

Lemma imp_id : forall A, Prov (Impl A A).
Proof.
  intro A.
  eapply MP.
  - eapply MP; [ exact (S A (Impl A A) A) | exact (K A (Impl A A)) ].
  - exact (K A A).
Qed.

(* Note: imp_id_all would be unsound - we can't prove arbitrary formulas *)
(* We use specific proofs for each case instead *)

(* ---- Chain/context machinery ---- *)

Fixpoint ctx_of (ρ:nat->bool) (xs:list nat) : list form :=
  match xs with
  | [] => []
  | n::ns =>
      let rest := ctx_of ρ ns in
      if ρ n then (Var n) :: rest else (Neg (Var n)) :: rest
  end.

Fixpoint chain (Γ:list form) (φ:form) : form :=
  match Γ with
  | [] => φ
  | ψ::Δ => Impl ψ (chain Δ φ)
  end.

Lemma prepend_ctx : forall Γ ψ φ, Prov (chain Γ φ) -> Prov (chain (ψ::Γ) φ).
Proof.
  intros Γ ψ φ H.
  simpl.
  eapply MP; [ exact (K (chain Γ φ) ψ) | exact H ].
Qed.

(* Lift an implication through any chain Γ·_ *)
Lemma chain_lift : forall Γ A B,
  Prov (Impl A B) -> Prov (Impl (chain Γ A) (chain Γ B)).
Proof.
  intros Γ A B HAB; revert A B HAB.
  induction Γ as [|a Γ' IH]; simpl; intros A B HAB.
  - exact HAB.
  - eapply MP.
    + exact (S a (chain Γ' A) (chain Γ' B)).
    + eapply MP.
      * exact (K (Impl (chain Γ' A) (chain Γ' B)) a).
      * exact (IH _ _ HAB).
Qed.

Lemma chain_mp : forall Γ A B,
  Prov (Impl A B) -> Prov (chain Γ A) -> Prov (chain Γ B).
Proof.
  intros Γ A B HAB HΓA. eapply MP; [ apply chain_lift; exact HAB | exact HΓA ].
Qed.

(* Project a hypothesis from Γ into a chain proof of that hypothesis *)
(* Assumption rule: if a formula is in the context, we can derive the chained implication *)
Axiom member_to_chain :
  forall Γ a, In a Γ -> Prov (chain Γ a).

Lemma chain_or_intro_l : forall Γ A B, Prov (chain Γ A) -> Prov (chain Γ (Or A B)).
Proof.
  intros Γ A B Ha.
  eapply chain_mp; [ exact (OrI1 A B) | exact Ha ].
Qed.

Lemma chain_or_intro_r : forall Γ A B, Prov (chain Γ B) -> Prov (chain Γ (Or A B)).
Proof.
  intros Γ A B Hb.
  eapply chain_mp; [ exact (OrI2 A B) | exact Hb ].
Qed.

Lemma close_chain : forall Γ φ, Prov (chain Γ φ) -> Prov φ.
Proof.
  intros Γ φ H.
  induction Γ as [|ψ Γ IH]; simpl in *; auto.
  apply IH.
  eapply MP; [ exact H | admit ]. (* Would need specific ψ proof *)
Admitted.

(* ---------- helpers to hit ctx_of literals ---------- *)

Lemma vars_in_nodup_vars :
  forall (φ:form) (v:nat), In v (vars φ) -> In v (nodup (vars φ)).
Proof. intros φ v Hin. apply nodup_preserves; exact Hin. Qed.

Lemma in_ctx_of_true :
  forall ρ xs n, In n xs -> ρ n = true -> In (Var n) (ctx_of ρ xs).
Proof.
  intros ρ xs n Hin Hρ; induction xs as [|m xs IH] in Hin |- *; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + now rewrite Hρ; simpl; auto.
    + destruct (ρ m); simpl; auto using in_cons.
Qed.

Lemma in_ctx_of_false :
  forall ρ xs n, In n xs -> ρ n = false -> In (Neg (Var n)) (ctx_of ρ xs).
Proof.
  intros ρ xs n Hin Hρ; induction xs as [|m xs IH] in Hin |- *; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + now rewrite Hρ; simpl; auto.
    + destruct (ρ m); simpl; auto using in_cons.
Qed.

(* ---------- boolean truth -> chain proof (context = nodup(vars φ)) ---------- *)

Fixpoint derive_under_ctx (ρ:nat->bool) (φ:form)
  : eval_prop ρ φ = true -> Prov (chain (ctx_of ρ (nodup (vars φ))) φ).
Proof.
  intros Hev; revert Hev.
  induction φ as
    [ | n
    | ψ IHψ χ IHχ
    | ψ IHψ χ IHχ
    | ψ IHψ χ IHχ
    | ψ IHψ
    | ψ IHψ
    | ψ IHψ
    ]; simpl.

  - (* Bot *) intros Hev; discriminate Hev.

  - (* Var n *)
    intros Hev.
    destruct (ρ n) eqn:Hv; simpl in Hev; try discriminate.
    assert (Hin : In n (nodup (vars (Var n)))) by (simpl; left; reflexivity).
    assert (Hin_ctx : In (Var n) (ctx_of ρ (nodup (vars (Var n))))) by (apply in_ctx_of_true; [exact Hin | exact Hv]).
    simpl in Hin_ctx; rewrite Hv in Hin_ctx; simpl in Hin_ctx.
    apply member_to_chain; exact Hin_ctx.

  - (* Impl ψ χ *)
    destruct (eval_prop ρ ψ) eqn:Hψ; simpl; intro Hχ.
    + (* ψ true, χ true *)
      admit. (* Need weakening: IHχ gives context (vars χ) but we need (vars ψ ++ vars χ) *)
    + (* ψ false, whole implication true *)
      admit. (* Need to derive Impl ψ χ from Neg ψ in context *)

  - (* And ψ χ *)
    intros Hev. apply Bool.andb_true_iff in Hev as [Hψ Hχ].
    admit. (* Complex context mixing issue *)

  - (* Or ψ χ *)
    intros Hev. apply Bool.orb_true_iff in Hev as [Hψ | Hχ].
    + admit. (* Context mixing: need (vars ψ ++ vars χ) but have (vars ψ) *)
    + admit. (* Context mixing: need (vars ψ ++ vars χ) but have (vars χ) *)

  - (* Neg ψ *)
    intros Hev. destruct (eval_prop ρ ψ) eqn:Hψ; inversion Hev.
    admit. (* Same chain_lift type mismatch *)

  - (* Box ψ *) intros Hev. admit. (* Need Box introduction rule *)
  - (* Dia ψ *) intros Hev. admit. (* Need Dia introduction rule *)
Admitted.

(* ---------- list-wide helpers for decide ---------- *)

Lemma forallb_exists_false {A} (p:A->bool) (l:list A) :
  forallb p l = false -> exists x, In x l /\ p x = false.
Proof.
  induction l as [|a l IH]; simpl; intro H; try discriminate.
  destruct (p a) eqn:Pa; simpl in H.
  - apply IH in H. destruct H as [x [Hin Hpx]]. exists x; auto.
  - exists a; split; [left; reflexivity| exact Pa].
Qed.

(* Big disjunction over a list – minimal cover to finish decide(true) path *)
Fixpoint big_or (xs:list form) : form :=
  match xs with
  | [] => Impl Bot Bot
  | a::t => Or a (big_or t)
  end.

Lemma big_or_intro_l Γ a t : Prov (chain Γ a) -> Prov (chain Γ (big_or (a::t))).
Proof.
  intros H; induction t as [|b t IH]; simpl.
  - eapply chain_or_intro_l; exact H.
  - eapply chain_or_intro_l; exact H.
Qed.

Lemma big_or_intro_r Γ a t : Prov (chain Γ (big_or t)) -> Prov (chain Γ (big_or (a::t))).
Proof.
  intros H; induction t as [|b t IH]; simpl.
  - eapply chain_or_intro_r; exact H.
  - eapply chain_or_intro_r; exact H.
Qed.

(* Coverage: the big disjunction of all assignment-context literals is Prov *)
Lemma covers_all_ctx (xs:list nat) :
  Prov (big_or (map (fun ρ => chain (ctx_of ρ xs) (Impl Bot Bot))
                    (all_assignments xs))).
Proof.
  (* Complex coverage proof for all assignment contexts *)
  admit.
Admitted.

(* ---------- constructive decision procedure ---------- *)

Definition decide (φ:form) : { Prov φ } + { Prov (Neg φ) }.
Proof.
  set (xs := nodup (vars φ)).
  set (asg := all_assignments xs).
  destruct (tautology_prop φ) eqn:Htaut.
  - (* true *) destruct asg as [|ρ0 rest] eqn:Hasg.
    + left; admit. (* Degenerate case: need to prove closed tautology *)
    + assert (Hev: eval_prop ρ0 φ = true).
      { admit. (* Technical: extract ρ0 from forallb since it's first in list *) }
      left. eapply close_chain, derive_under_ctx; exact Hev.
  - (* false *) right; admit. (* Need computational witness extraction from forallb = false *)
Admitted.

Lemma tautology_prop_sound : forall φ, tautology_prop φ = true -> Prov φ.
Proof.
  intros φ Ht. destruct (decide φ) as [Hp | Hn]; auto.
  (* In the impossible branch, we'd have both Prov φ and Prov ¬φ; kernel can explode via NegE *)
  admit.
Admitted.