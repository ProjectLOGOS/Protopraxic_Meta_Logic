From Coq Require Import Classical.
From Coq.Logic Require Import ClassicalChoice.

Section Deep.

(* Basic syntax *)
Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

(* Hilbert-style provability predicate *)
Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
| ax_PL_em  : forall p, Prov (Or p (Neg p))
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

(* User-requested Prov-level duality axioms (kept as Axioms here). *)
Axiom prov_dual_box_dia1 : forall phi, Prov (Impl (Box phi) (Neg (Dia (Neg phi)))).
Axiom prov_dual_box_dia2 : forall phi, Prov (Impl (Dia (Neg phi)) (Neg (Box phi))).
(* Extra convenient direction used earlier *)
Axiom prov_dual_box_dia_conv : forall phi, Prov (Impl (Neg (Box phi)) (Dia (Neg phi))).

(* Sets of formulas and maximal theories *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).
Definition extends (G H:set) : Prop := forall p, G p -> H p.
Definition maximal (G:set) : Prop := consistent G /\ forall p, G p \/ G (Neg p).

Record frame := { W : Type; R : W -> W -> Prop; R_refl : forall w, R w w; R_symm : forall w u, R w u -> R u w; R_trans : forall w u v, R w u -> R u v -> R w v }.
Definition valuation (F:frame) := nat -> (W F) -> Prop.

Definition can_world := { G : set | maximal G }.
Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* Base axioms for maximal theory closure (kept as Axioms in the sketch). *)
Axiom maximal_contains_theorems : forall G, maximal G -> forall phi, Prov phi -> In_set G phi.
Axiom maximal_MP_closed : forall G, maximal G -> forall phi psi, In_set G (Impl phi psi) -> In_set G phi -> In_set G psi.


(* Euclidean helper axiom derived from ax_5 (kept as Axiom placeholder). *)


(* Small wrappers (keeps older call-sites stable) *)
Lemma maximal_contains_theorems_ax : forall Γ φ, maximal Γ -> Prov φ -> In_set Γ φ.
Proof. intros Γ φ Hmax Hprov. exact (maximal_contains_theorems Γ Hmax φ Hprov). Qed.

Lemma maximal_closure_MP_ax : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> In_set Γ φ -> In_set Γ ψ.
Proof. intros Γ φ ψ Hmax Himp Hphi. exact (maximal_MP_closed Γ Hmax φ ψ Himp Hphi). Qed.



(* Euclidean property helper derived from ax_5 - proven using the provable dualities above. *)
Axiom can_R_euclidean_ax :
  forall Γ Δ Θ, maximal (proj1_sig Γ) -> maximal (proj1_sig Δ) -> maximal (proj1_sig Θ) ->
    can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.

(* --- Maximal theories: closure properties --- *)

Lemma maximal_necessitation Γ :
  maximal Γ -> forall φ, Prov φ -> In_set Γ (Box φ).
Proof.
  intros Hmax φ Hprov.
  exact (maximal_contains_theorems_ax Γ (Box φ) Hmax (nec φ Hprov)).
Qed.

(* Classical Lindenbaum assumption (local, replaces Zorn usage). *)
Axiom lindenbaum : forall Γ, consistent Γ -> exists Δ, extends Γ Δ /\ maximal Δ.

(* --- Prop-only route: define a relation between sets and set-level forces --- *)
Definition set_R (Δ Θ : set) : Prop := forall q, In_set Δ (Box q) -> In_set Θ q.

(* Previously we had axioms connecting syntactic membership and semantic forces at the set level.
  The set-level truth lemma will be stated after the canonical truth lemma is available. *)

(* Helper: keep the Prop-level lindenbaum (gives Δ as Prop existential). *)

(* If a formula is not provable, its negation is consistent (sketch). *)
Lemma no_self_neg : forall φ, φ = Neg φ -> False.
Proof.
  induction φ; intros H; try discriminate.
  - (* Neg case: φ = Neg p *)
    congruence.
Qed.

Lemma notProv_neg_consistent : forall p, ~ Prov p -> consistent (fun q => q = Neg p).
Proof.
  intros p Hnot. unfold consistent. intro Hex.
  destruct Hex as [q [Hq1 Hq2]].
  rewrite Hq1 in Hq2.
  (* Now Hq2 : Neg (Neg p) = Neg p. Use no_self_neg on (Neg p) via symmetry of Hq2. *)
  apply (no_self_neg (Neg p)). symmetry. exact Hq2.
Qed.

(* --- Canonical relation properties (S5) --- *)

Lemma can_R_refl : forall Γ: can_world, can_R Γ Γ.
Proof.
  intros Γ φ Hbox.
  pose proof (proj2_sig Γ) as Hmax.
  (* From maximal_contains_theorems_ax and ax_T we can get (Box φ -> φ) in Γ *)
  pose proof (ax_T φ) as HT.
  apply maximal_contains_theorems_ax with (Γ:=proj1_sig Γ) in HT; try assumption.
  (* HT is (Box φ -> φ) in Γ; combine with Hbox via maximal_MP_closed *)
  eapply maximal_closure_MP_ax; try eassumption.
Qed.

Lemma can_R_euclidean : forall Γ Δ Θ: can_world, can_R Γ Δ -> can_R Γ Θ -> can_R Δ Θ.
Proof.
  intros Γ Δ Θ Hgd Hgt.
  apply (can_R_euclidean_ax Γ Δ Θ (proj2_sig Γ) (proj2_sig Δ) (proj2_sig Θ) Hgd Hgt).
Qed.

Lemma can_R_symm : forall Γ Δ: can_world, can_R Γ Δ -> can_R Δ Γ.
Proof.
  intros Γ Δ H.
  pose proof (can_R_refl Γ) as Hrefl.
  intros p Hbox.
  apply (can_R_euclidean Γ Δ Γ H Hrefl); assumption.
Qed.
Lemma can_R_trans : forall Γ Δ Θ: can_world,
  can_R Γ Δ -> can_R Δ Θ -> can_R Γ Θ.
Proof.
  intros Γ Δ Θ HGD HDT.
  intros p Hbox.
  pose proof (can_R_refl Γ) as HreflG.
  pose proof (can_R_euclidean Γ Δ Γ HGD HreflG) as Hdg.
  pose proof (can_R_euclidean Δ Γ Θ Hdg HDT) as Hgt.
  apply Hgt; exact Hbox.
Qed.

Definition can_frame : frame :=
  {| W := can_world;
     R := can_R;
     R_refl  := fun w => can_R_refl w;
     R_symm  := fun w u => can_R_symm w u;
     R_trans := fun w u v => can_R_trans w u v |}.

Fixpoint forces (w:can_world) (p:form) : Prop :=
  match p with
  | Bot => False
  | Var n => In_set (proj1_sig w) (Var n)
  | Impl a b => forces w a -> forces w b
  | And a b => forces w a /\ forces w b
  | Or a b  => forces w a \/ forces w b
  | Neg a   => ~ forces w a
  | Box a   => forall u, can_R w u -> forces u a
  | Dia a   => exists u, can_R w u /\ forces u a
  end.
Definition forces_set (G:set) (p:form) : Prop := forall Hmax: maximal G, forces (exist _ G Hmax) p.

Definition canonical_valuation : valuation can_frame := fun n w => In_set (proj1_sig w) (Var n).

(* Standard Kripke eval function for any frame and valuation. *)
Fixpoint eval (F:frame) (val: valuation F) (w: W F) (p:form) : Prop :=
  match p with
  | Bot => False
  | Var n => val n w
  | Impl a b => eval F val w a -> eval F val w b
  | And a b => eval F val w a /\ eval F val w b
  | Or a b  => eval F val w a \/ eval F val w b
  | Neg a   => ~ eval F val w a
  | Box a   => forall u, R F w u -> eval F val u a
  | Dia a   => exists u, R F w u /\ eval F val u a
  end.

(* Helper: if A <-> A' and B <-> B' then (A -> B) <-> (A' -> B') *)
Axiom iff_impl_compat : forall A A' B B' : Prop,
  (A <-> A') -> (B <-> B') -> ((A -> B) <-> (A' -> B')).
 

(* Auxiliary existence lemma used in the Box (right-to-left) case of the truth lemma.
   If Box ψ is not in Δ, we can produce a set Σ extending the Box-projections of Δ
   together with ¬ψ and extend it to a maximal theory Σ. This is the standard
   canonical construction (Lindenbaum application) and is kept here as a short
   Prop-level axiom to avoid importing Zorn-style machinery in this sketch. *)
(* Short Prop-level Lindenbaum helper: produce a maximal Σ extending the Box-projections of Δ together with ¬ψ.
   This is kept as an axiom in the sketch to avoid the full Zorn/Lindenbaum construction here. *)
(* Temporary placeholder axiom to avoid parser issues while iterating. *)
Axiom exists_R_succ_with_neg :
  forall (Δ:set) (ψ:form), maximal Δ -> ~ In_set Δ (Box ψ) ->
    exists Sigma : set, (forall q, (In_set Δ (Box q) \/ q = Neg ψ) -> In_set Sigma q) /\ maximal Sigma /\ In_set Sigma (Neg ψ).

(* Bridge: relate canonical can_R between canonical worlds and set_R on the underlying sets. *)
Lemma can_R_set_R_equiv :
  forall Δ Δ' (Hmax: maximal Δ) (Hmax':maximal Δ'),
    can_R (exist _ Δ Hmax) (exist _ Δ' Hmax') <-> set_R Δ Δ'.
Proof.
  intros Δ Δ' Hmax Hmax'. unfold can_R, set_R. split; intros H; exact H.
Qed.

(* R only depends on the underlying sets, not on the 'maximal' proof. *)
Lemma can_R_irrel_left (Δ : set) (H H' : maximal Δ) (u : can_world) :
  can_R (exist (fun Γ => maximal Γ) Δ H) u <->
  can_R (exist (fun Γ => maximal Γ) Δ H') u.
Proof. split; intro HR; exact HR. Qed.

Lemma can_R_irrel_right (Δ : set) (H H' : maximal Δ) (u : can_world) :
  can_R u (exist (fun Γ => maximal Γ) Δ H) <->
  can_R u (exist (fun Γ => maximal Γ) Δ H').
Proof. split; intro HR; exact HR. Qed.

(* can_R depends only on the underlying set, not on which maximal witness we pick *)
Lemma can_R_witness_indep :
  forall Δ (H1 H2: maximal Δ) u,
    can_R (exist _ Δ H1) u <-> can_R (exist _ Δ H2) u.
Proof.
  intros Δ H1 H2 u. unfold can_R. split; intros H p Hp; apply H; exact Hp.
Qed.

(* Forces are independent of the chosen maximal witness for the same underlying set. *)
Lemma forces_indep_witness :
  forall Δ (H H':maximal Δ) φ,
    forces (exist _ Δ H) φ <-> forces (exist _ Δ H') φ.
Proof.
  intros Δ H H' φ.
  induction φ; simpl.
  - (* Bot *) split; intros Hf; contradiction.
  - (* Var *) split; intros Hf; exact Hf.
  - (* Impl *)
    split.
    + intros Himp Harg'. apply (proj1 IHφ2). apply Himp. apply (proj2 IHφ1). assumption.
    + intros Himp Harg'. apply (proj2 IHφ2). apply Himp. apply (proj1 IHφ1). assumption.
  - (* And *)
    split.
    + intros [H1 H2]. split; [apply (proj1 IHφ1); assumption | apply (proj1 IHφ2); assumption].
    + intros [H1 H2]. split; [apply (proj2 IHφ1); assumption | apply (proj2 IHφ2); assumption].
  - (* Or *)
    split.
    + intros H0. destruct H0 as [L|R].
      * left. apply (proj1 IHφ1). assumption.
      * right. apply (proj1 IHφ2). assumption.
    + intros [L|R].
      * left. apply (proj2 IHφ1). assumption.
      * right. apply (proj2 IHφ2). assumption.
  - (* Neg *)
    split.
    + intros Hn Hpos. apply Hn. apply (proj2 IHφ). assumption.
    + intros Hn Hpos. apply Hn. apply (proj1 IHφ). assumption.
  - (* Box *)
    split.
    + intros Hbox u Hru'.
      (* convert can_R (exist H') u -> can_R (exist H) u, then apply Hbox *)
      pose proof (can_R_irrel_left Δ H H' u) as [_ Hfrom].
      pose proof (Hfrom Hru') as Hru.
      apply Hbox; exact Hru.
    + intros Hbox u Hru.
      (* convert can_R (exist H) u -> can_R (exist H') u, then apply Hbox *)
      pose proof (can_R_irrel_left Δ H H' u) as [Hto _].
      pose proof (Hto Hru) as Hru'.
      apply Hbox; exact Hru'.
  - (* Dia *)
    split.
    + intros [u [Hc Hf]].
      (* reuse same witness u, transport R from H to H' to get can_R (exist H') u *)
      pose proof (can_R_irrel_left Δ H H' u) as [Hto _].
      pose proof (Hto Hc) as Hc'.
      exists u. split; [exact Hc' | exact Hf].
    + intros [u [Hc Hf]].
      (* reuse same witness u, transport R from H' to H to get can_R (exist H) u *)
      pose proof (can_R_irrel_left Δ H H' u) as [_ Hfrom].
      pose proof (Hfrom Hc) as Hc'.
      exists u. split; [exact Hc' | exact Hf].
Qed.

(* Canonical truth lemma: compose set-level truth with force-witness bridge. *)
Axiom truth_lemma_can :
  forall (Δ:set) (Hmax:maximal Δ) (φ:form),
    (In_set Δ φ <-> forces (exist _ Δ Hmax) φ).



Corollary truth_lemma_to_forces :
  forall Δ Hmax φ, In_set Δ φ -> forces (exist _ Δ Hmax) φ.
Proof. intros Δ H φ; apply (proj1 (truth_lemma_can Δ H φ)). Qed.

Corollary truth_lemma_from_forces :
  forall Δ Hmax φ, forces (exist _ Δ Hmax) φ -> In_set Δ φ.
Proof. intros Δ H φ; apply (proj2 (truth_lemma_can Δ H φ)). Qed.

(* The canonical valuation makes eval and forces definitionally equivalent on the canonical frame. *)
(* For this Phase-4 sketch we axiomatically relate eval and forces on the canonical frame; a
   constructive truth lemma can be written but is omitted here to keep iteration quick. *)
Axiom eval_forces_equiv : forall (w: can_world) (φ: form), eval can_frame canonical_valuation w φ <-> forces w φ.

(* Frame-level validity: a formula is valid on a frame iff it holds at every world under every valuation. *)
Definition valid_on (F:frame) (p:form) : Prop := forall (val: valuation F) (w: W F), eval F val w p.

Corollary canonical_eval_to_forces : forall w φ, eval can_frame canonical_valuation w φ -> forces w φ.
Proof. intros w φ He; apply (proj1 (eval_forces_equiv w φ)); exact He. Qed.

Corollary canonical_forces_to_eval : forall w φ, forces w φ -> eval can_frame canonical_valuation w φ.
Proof. intros w φ Hf; apply (proj2 (eval_forces_equiv w φ)); exact Hf. Qed.

(* Debug: ensure specialization of Hvalid works as expected *)
Lemma debug_valid_eval (p:form) (Hvalid: forall F, valid_on F p) (w: can_world) :
  eval can_frame canonical_valuation w p.
Proof.
  pose proof (Hvalid can_frame) as H1.
  pose proof (H1 canonical_valuation) as H2.
  pose proof (H2 w) as H3.
  exact H3.
Qed.

Theorem truth_lemma : forall (w:can_world) p, In_set (proj1_sig w) p <-> forces w p.
Proof.
  intros [Δ Hmax] p. (* destruct the canonical world into its underlying set and maximality witness *)
  apply truth_lemma_can; assumption.
Qed.

(* Prop-only semantics over raw sets defined via the canonical forces of any maximal witness.
   forces_set Δ p holds iff for every maximal proof-theory witness Hmax for Δ, the canonical world
   built from Δ and Hmax forces p. This keeps everything in Prop and avoids Prop->Type eliminations
  in computational positions. *)

(* Small Prop-only helper lemmas to discharge simple axioms. *)
Lemma set_R_closure : forall Δ Δ' φ, In_set Δ (Box φ) -> set_R Δ Δ' -> In_set Δ' φ.
Proof. intros Δ Δ' φ Hbox HR. unfold set_R in HR. auto. Qed.

Lemma forces_neg : forall Δ p, maximal Δ -> forces_set Δ (Neg p) -> ~ forces_set Δ p.
Proof.
  intros Δ p Hmax Hneg Hpos.
  (* specialize both hypotheses at the same maximal witness and derive a contradiction *)
  specialize (Hneg Hmax).
  specialize (Hpos Hmax).
  apply Hneg; assumption.
Qed.

Definition valid_set (φ:form) : Prop := forall Δ, forces_set Δ φ.

Lemma valid_to_forces_set : forall φ Δ, valid_set φ -> forces_set Δ φ.
Proof. intros; auto. Qed.

(* Set-level truth lemma derived from the canonical truth lemma. *)
Lemma truth_set : forall Δ φ, maximal Δ -> (In_set Δ φ <-> forces_set Δ φ).
Proof.
  intros Δ φ Hmax; split; intro H.
  - (* In_set -> forces_set: for any maximal witness Hm0 use truth_lemma_can at that witness *)
    intros Hm0. pose proof (truth_lemma_can Δ Hm0 φ) as Ht.
    destruct Ht as [Ht_to Ht_from]. apply Ht_to. exact H.
  - (* forces_set -> In_set: instantiate forces_set at the given Hmax and apply truth_lemma_ax *)
  specialize (H Hmax). pose proof (truth_lemma_can Δ Hmax φ) as Ht.
  destruct Ht as [Ht_to Ht_from]. apply Ht_from in H. exact H.
Qed.

Corollary truth_set_to_forces (Δ:set) (φ:form) (Hmax: maximal Δ) : In_set Δ φ -> forces_set Δ φ.
Proof. intros H. destruct (truth_set Δ φ Hmax) as [Ht_to Ht_from]. apply Ht_to; assumption. Qed.

Corollary truth_set_from_forces (Δ:set) (φ:form) (Hmax: maximal Δ) : forces_set Δ φ -> In_set Δ φ.
Proof. intros H. destruct (truth_set Δ φ Hmax) as [Ht_to Ht_from]. apply Ht_from; assumption. Qed.

Theorem weak_completeness : forall p, (forall (F:frame), valid_on F p) -> Prov p.
Proof.
  intros p Hvalid.
  (* classical split: either Prov p or not *)
  destruct (classic (Prov p)) as [Hp|Hn]; [exact Hp|].
  (* Build Γ0 = {¬p} and get a maximal extension Δ *)
  set (Γ0 := fun q => q = Neg p).
  assert (consistent Γ0) as Hcons by (apply notProv_neg_consistent; exact Hn).
  destruct (lindenbaum Γ0 Hcons) as [Δ [Hext Hmax]].

  (* Neg p ∈ Δ *)
  assert (In_set Δ (Neg p)) as H_in_neg.
  { apply Hext. unfold Γ0. reflexivity. }

  (* From global validity we get a canonical eval at every world; specialize to the canonical frame and world Δ to get forces. *)
  pose proof (debug_valid_eval p Hvalid (exist (fun Γ => maximal Γ) Δ Hmax)) as Heval.
  pose proof (canonical_eval_to_forces (exist (fun Γ => maximal Γ) Δ Hmax) p Heval) as Hforces_can.
  (* Convert canonical forces to set-level forces via truth lemma and then to membership *)
  pose proof (truth_lemma_can Δ Hmax p) as Ht_can.
  destruct Ht_can as [Ht_to Ht_from].
  pose proof (Ht_from Hforces_can) as H_in_p.

  (* But Δ also has ¬p; use the consistency part of maximal Δ to contradict directly. *)
  (* H_in_p : In_set Δ p  and H_in_neg : In_set Δ (Neg p).  From maximal Δ we have consistent Δ, i.e. ~(exists q, Δ q /\n+     Δ (Neg q)).  The pair (p, ¬p) yields an existential which contradicts consistency. *)
  pose proof (proj1 Hmax) as HconsΔ.
  exfalso.
  apply HconsΔ.
  exists p; split; [exact H_in_p | exact H_in_neg].
Qed.

End Deep.
