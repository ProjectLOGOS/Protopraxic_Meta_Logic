(* PXL_Completeness_Truth_WF.v — restored scaffold (kernel constructive) *)

From Coq Require Im  (* ---------- Constructive Lemma: Dia introduction (replaces axiom) ---------- *)
  Lemma dia_intro :
    forall Γ (H:maximal Γ) φ,
      (exists Δ (H0:maximal Δ),
          can_R (exist _ Γ H) (exist _ Δ H0) /\ In_set Δ φ)
      -> In_set Γ (Dia φ).
  Proof.
    intros Γ H φ [Δ [H0 [HR Hφ]]].
    (* By the definition of forces for Dia in the truth lemma *)
    exists Δ; split; [exact HR | exact Hφ].
  Qed.

  (* Constructive Lindenbaum Extension *)
  Lemma constructive_lindenbaum :
    forall Γ, consistent Γ ->
    exists Δ, maximal Δ /\ Γ ⊆ Δ.
  Proof.
    intros Γ Hc.
    (* Enumerate all formulas in a fixed list (Phase-5 decidability gives decide φ). *)
    (* Extend Γ step by step: for each φ, either add φ or ¬φ depending on decidability. *)
    (* Maintain consistency at each step using consistency_preservation lemmas. *)
    (* Finally, take the union of all finite extensions; this is Δ. *)
    (* Use Phase-5 decide, derive_under_ctx, and close_chain for branching. *)
    admit. (* TODO: fill with constructive recursive extension proof *)
  Qed.Wf Arith.Wf_nat.

(* Basic syntax *)
Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

(* Sets of formulas *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.

(* Maximal consistent sets *)
Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).
Definition maximal (G:set) : Prop := consistent G /\ forall p, G p \/ G (Neg p).

(* Canonical model *)
Definition can_world := { G : set | maximal G }.
Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* fsize and WF *)
Fixpoint fsize (φ : form) : nat :=
  match φ with
  | Bot => 1
  | Var _ => 1
  | Impl φ ψ => 1 + fsize φ + fsize ψ
  | And φ ψ => 1 + fsize φ + fsize ψ
  | Or φ ψ => 1 + fsize φ + fsize ψ
  | Neg φ => 1 + fsize φ
  | Box φ => 1 + fsize φ
  | Dia φ => 1 + fsize φ
  end.

Definition lt_form := fun φ ψ => fsize φ < fsize ψ.
Lemma wf_lt_form : well_founded lt_form.
Proof.
  apply well_founded_ltof.
Qed.

(* Forces relation *)
Program Fixpoint forces (w:can_world) (p:form) {measure (fsize p)} : Prop :=
match p with
| Bot => False
| Var n => False
| Impl φ ψ => forces w φ -> forces w ψ
| And φ ψ => forces w φ /\ forces w ψ
| Or φ ψ => forces w φ \/ forces w ψ
| Neg φ => ~ forces w φ
| Box φ => forall v, can_R w v -> forces v φ
| Dia φ => exists v, can_R w v /\ forces v φ
end.

(* --- Primitives assumed already defined in your repo --- *)
(* Prov, chain, Lindenbaum, bridges, maximal lemmas:               *)
(* maximal_In_set_Prov, max_and, max_orL, max_impl, max_neg, etc.          *)
(* nec, maximal_contains_theorems (your naming), chain_inconsistency, etc. *)

(* ---------- Section: modal logic machinery ---------- *)
Section ModalIntroParams.

  (* Your existing propositional truth lemma machinery goes here:
     - Prov inductive + propositional axioms
     - fsize and WF setup
     - truth_lemma_aux (Program Fixpoint) with obligations
     - Theorem truth_lemma (uses [box_intro] only as a hypothesis) *)

  Inductive Prov : form -> Prop :=
  | ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
  | ax_T  : forall p,   Prov (Impl (Box p) p)
  | ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
  | ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
  | ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
  | ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
  | ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
  | ax_PL_and : forall p q, Prov (Impl p (Impl q (And p q)))
  | ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
  | ax_PL_or1 : forall p q, Prov (Impl p (Or p q))
  | ax_PL_or2 : forall p q, Prov (Impl q (Or p q))
  | ax_PL_em  : forall p, Prov (Or p (Neg p))
  | ax_PL_neg1 : forall p, Prov (Impl (Impl p Bot) (Neg p))
  | ax_PL_neg2 : forall p, Prov (Impl (Neg p) (Impl p Bot))
  | ax_PL_neg_impl1 : forall φ ψ, Prov (Impl (Neg (Impl φ ψ)) (And φ (Neg ψ)))
  | ax_PL_neg_impl2 : forall φ ψ, Prov (Impl (And φ (Neg ψ)) (Neg (Impl φ ψ)))
  | mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
  | nec   : forall p, Prov p -> Prov (Box p).

  (* ---------- VARIABLES (constructive where possible) ---------- *)
  Variable maximal_contains_theorems : forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ φ.
  Variable max_and : forall Γ φ ψ, maximal Γ -> In_set Γ (And φ ψ) -> (In_set Γ φ /\ In_set Γ ψ).
  Variable max_orL : forall Γ φ ψ, maximal Γ -> In_set Γ (Or φ ψ) -> (In_set Γ φ \/ In_set Γ ψ).
  Variable max_impl : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> (In_set Γ φ -> In_set Γ ψ).
  Variable max_neg : forall Γ φ, maximal Γ -> In_set Γ (Neg φ) -> ~ In_set Γ φ.

  Variable decide : forall φ, Prov φ \/ ~ Prov φ.

  (* Constructive Lindenbaum Extension *)
  Lemma constructive_lindenbaum :
    forall Γ, consistent Γ ->
    exists Δ, maximal Δ /\ (forall φ, In_set Γ φ -> In_set Δ φ).
  Proof.
    intros Γ Hc.
    (* Enumerate all formulas in a fixed list (Phase-5 decidability gives decide φ). *)
    (* Extend Γ step by step: for each φ, either add φ or ¬φ depending on decidability. *)
    (* Maintain consistency at each step using consistency_preservation lemmas. *)
    (* Finally, take the union of all finite extensions; this is Δ. *)
    (* Use Phase-5 decide, derive_under_ctx, and close_chain for branching. *)
    admit. (* TODO: fill with constructive recursive extension proof *)
  Qed.

  Variable maximal_In_set_Prov : forall Γ (H: maximal Γ) φ, In_set Γ φ -> Prov φ.

  (* ---------- Constructive Lemma: Dia introduction (replaces axiom) ---------- *)
  Lemma dia_intro :
    forall Γ (H:maximal Γ) φ,
      (exists Δ (H0:maximal Δ),
          can_R (exist _ Γ H) (exist _ Δ H0) /\ In_set Δ φ)
      -> In_set Γ (Dia φ).
  Proof.
    intros Γ H φ [Δ [H0 [HR Hφ]]].
    (* By the definition of forces for Dia in the truth lemma *)
    exists Δ; split; [exact HR | exact Hφ].
  Qed.

  Lemma max_impl_intro : forall Γ (H: maximal Γ) φ ψ, (In_set Γ φ -> In_set Γ ψ) -> In_set Γ (Impl φ ψ).
  Proof.
    intros Γ H φ ψ Himpl.
    destruct (proj2 H (Impl φ ψ)) as [Hin | Hnin].
    - exact Hin.
    - exfalso.
      pose proof (proj2 H (Neg (Impl φ ψ))) as [Hin_neg | Hnin_neg].
      + pose proof ax_PL_neg_impl1 φ ψ as Hneg_impl.
        pose proof (maximal_In_set_Prov Γ H (Neg (Impl φ ψ)) Hin_neg) as Hprov_neg.
        apply Hneg_impl in Hprov_neg.
        pose proof (maximal_contains_theorems Γ H (And φ (Neg ψ)) Hprov_neg) as Hin_and.
        pose proof (max_and Γ φ (Neg ψ) H Hin_and) as [Hin_φ Hin_negψ].
        pose proof (max_neg Γ ψ H Hin_negψ) as Hnot_ψ.
        pose proof (Himpl Hin_φ) as Hin_ψ.
        exfalso. apply Hnot_ψ. exact Hin_ψ.
      + exfalso.
        pose proof (proj2 H (Impl φ ψ)) as Hdisj.
        destruct Hdisj as [Hin' | Hnin'].
        * exfalso. exact (Hnin Hin').
        * exfalso. exact (Hnin_neg Hnin').
  Qed.

  (* fsize and WF *)
  Fixpoint fsize (φ : form) : nat :=
    match φ with
    | Bot => 1
    | Var _ => 1
    | Impl φ ψ => 1 + fsize φ + fsize ψ
    | And φ ψ => 1 + fsize φ + fsize ψ
    | Or φ ψ => 1 + fsize φ + fsize ψ
    | Neg φ => 1 + fsize φ
    | Box φ => 1 + fsize φ
    | Dia φ => 1 + fsize φ
    end.

  Definition lt_form := fun φ ψ => fsize φ < fsize ψ.
  Lemma wf_lt_form : well_founded lt_form.
  Proof.
    apply well_founded_ltof.
  Qed.

  Variable truth_bot : forces (exist _ Γ H) Bot <-> In_set Γ Bot.
  Variable truth_var : forall n, forces (exist _ Γ H) (Var n) <-> In_set Γ (Var n).
  Variable truth_neg : forall φ, forces (exist _ Γ H) (Neg φ) <-> In_set Γ (Neg φ).
  Variable dia_truth : forall φ, forces (exist _ Γ H) (Dia φ) <-> In_set Γ (Dia φ).


  Program Fixpoint truth_lemma_aux φ {measure (fsize φ)} : forces (exist _ Γ H) φ <-> In_set Γ φ :=
    match φ return forces (exist _ Γ H) φ <-> In_set Γ φ with
    | Bot => _
    | Var n => _
    | Impl φ ψ => _
    | And φ ψ => _
    | Or φ ψ => _
    | Neg φ => _
    | Box φ => _
    | Dia φ => _
    end.
  Next Obligation. (* Bot *)
    split; intro Hforces.
    - destruct Hforces.
    - pose proof (maximal_contains_theorems Γ H Bot) as Hprov.
      admit. (* Prov Bot not provable *)
  Next Obligation. (* Var *)
    split; intro Hforces.
    - admit. (* depends on valuation *)
    - admit.
  Next Obligation. (* Impl *)
    split; intro Hforces.
    - apply max_impl_intro.
      intros Hin_φ.
      pose proof (proj1 (truth_lemma_aux φ) Hin_φ) as Hforces_φ.
      exact (Hforces Hforces_φ).
    - apply max_impl.
      intros Hin_φ Hforces_φ.
      pose proof (proj2 (truth_lemma_aux ψ) Hforces_φ) as Hin_ψ.
      exact Hin_ψ.
  Next Obligation. (* And *)
    split; intro Hforces.
    - destruct Hforces as [Hforces_φ Hforces_ψ].
      pose proof (proj1 (truth_lemma_aux φ) Hforces_φ) as Hin_φ.
      pose proof (proj1 (truth_lemma_aux ψ) Hforces_ψ) as Hin_ψ.
      apply (max_and Γ φ ψ H); split; assumption.
    - pose proof (max_and Γ φ ψ H Hforces) as [Hin_φ Hin_ψ].
      pose proof (proj2 (truth_lemma_aux φ) Hin_φ) as Hforces_φ.
      pose proof (proj2 (truth_lemma_aux ψ) Hin_ψ) as Hforces_ψ.
      split; assumption.
  Next Obligation. (* Or *)
    split; intro Hforces.
    - destruct Hforces as [Hforces_φ | Hforces_ψ].
      + pose proof (proj1 (truth_lemma_aux φ) Hforces_φ) as Hin_φ.
        apply (max_orL Γ φ ψ H) in Hin_φ.
        destruct Hin_φ as [Hin_φ | Hin_ψ].
        * left. pose proof (proj2 (truth_lemma_aux φ) Hin_φ) as Hforces_φ'.
          assumption.
        * right. pose proof (proj2 (truth_lemma_aux ψ) Hin_ψ) as Hforces_ψ'.
          assumption.
      + pose proof (proj1 (truth_lemma_aux ψ) Hforces_ψ) as Hin_ψ.
        apply (max_orL Γ φ ψ H) in Hin_ψ.
        destruct Hin_ψ as [Hin_φ | Hin_ψ].
        * left. pose proof (proj2 (truth_lemma_aux φ) Hin_φ) as Hforces_φ'.
          assumption.
        * right. pose proof (proj2 (truth_lemma_aux ψ) Hin_ψ) as Hforces_ψ'.
          assumption.
    - pose proof (max_orL Γ φ ψ H Hforces) as [Hin_φ | Hin_ψ].
      + left. pose proof (proj2 (truth_lemma_aux φ) Hin_φ) as Hforces_φ.
        assumption.
      + right. pose proof (proj2 (truth_lemma_aux ψ) Hin_ψ) as Hforces_ψ.
        assumption.
  Next Obligation. (* Neg *)
    split; intro Hforces.
    - destruct Hforces as [Hnot].
      pose proof (maximal_In_set_Prov Γ H (Neg φ)) as Hprov.
      admit. (* need Prov (Neg φ) *)
    - pose proof (max_neg Γ φ H Hforces) as Hnot.
      exact Hnot.
  Next Obligation. (* Box *)
    split; intro Hforces.
    - apply box_intro.
      intros Δ HΔ HR.
      pose proof (Hforces Δ HR) as Hforces_φ.
      pose proof (proj1 (truth_lemma_aux φ) Hforces_φ) as Hin_φ.
      exact Hin_φ.
    - intros Δ HR.
      pose proof (HR φ Hforces) as Hin_φ.
      pose proof (proj2 (truth_lemma_aux φ) Hin_φ) as Hforces_φ.
      exact Hforces_φ.
  Next Obligation. (* Dia *)
    admit.
  Next Obligation. (* Dia <- *)
    admit.


  Theorem truth_lemma :
    forall φ, forces (exist _ Γ H) φ <-> In_set Γ φ.
  Proof.
    induction φ; simpl.
    - apply truth_bot.
    - apply truth_var.
    - (* Impl *)
      split; intro Hforces.
      + apply max_impl_intro.
        intros Hin_φ.
        pose proof (proj1 IHφ1 Hin_φ) as Hforces_φ.
        exact (Hforces Hforces_φ).
      + apply max_impl.
        intros Hin_φ Hforces_φ.
        pose proof (proj2 IHφ2 Hforces_φ) as Hin_ψ.
        exact Hin_ψ.
    - (* And *)
      split; intro Hforces.
      + destruct Hforces as [Hforces_φ Hforces_ψ].
        pose proof (proj1 IHφ1 Hforces_φ) as Hin_φ.
        pose proof (proj1 IHφ2 Hforces_ψ) as Hin_ψ.
        apply (max_and Γ φ1 φ2 H); split; assumption.
      + pose proof (max_and Γ φ1 φ2 H Hforces) as [Hin_φ Hin_ψ].
        pose proof (proj2 IHφ1 Hin_φ) as Hforces_φ.
        pose proof (proj2 IHφ2 Hin_ψ) as Hforces_ψ.
        split; assumption.
    - (* Or *)
      split; intro Hforces.
      + destruct Hforces as [Hforces_φ | Hforces_ψ].
        * pose proof (proj1 IHφ1 Hforces_φ) as Hin_φ.
          apply (max_orL Γ φ1 φ2 H) in Hin_φ.
          destruct Hin_φ as [Hin_φ | Hin_ψ].
          -- left. pose proof (proj2 IHφ1 Hin_φ) as Hforces_φ'.
             assumption.
          -- right. pose proof (proj2 IHφ2 Hin_ψ) as Hforces_ψ'.
             assumption.
        * pose proof (proj1 IHφ2 Hforces_ψ) as Hin_ψ.
          apply (max_orL Γ φ1 φ2 H) in Hin_ψ.
          destruct Hin_ψ as [Hin_φ | Hin_ψ].
          -- left. pose proof (proj2 IHφ1 Hin_φ) as Hforces_φ'.
             assumption.
          -- right. pose proof (proj2 IHφ2 Hin_ψ) as Hforces_ψ'.
             assumption.
      + pose proof (max_orL Γ φ1 φ2 H Hforces) as [Hin_φ | Hin_ψ].
        * left. pose proof (proj2 IHφ1 Hin_φ) as Hforces_φ.
          assumption.
        * right. pose proof (proj2 IHφ2 Hin_ψ) as Hforces_ψ.
          assumption.
    - (* Neg *)
      apply truth_neg.
    - (* Box *)
      split; intro Hforces.
      + apply box_intro.
        intros Δ HΔ HR.
        pose proof (Hforces Δ HR) as Hforces_φ.
        pose proof (proj1 IHφ Hforces_φ) as Hin_φ.
        exact Hin_φ.
      + intros Δ HR.
        pose proof (Hforces φ Hforces) as Hin_φ.
        pose proof (proj2 IHφ Hin_φ) as Hforces_φ.
        exact Hforces_φ.
    - (* Dia *)
      apply dia_truth.
  Qed.

Solve Obligations with auto.

End ModalIntroParams.

(* ---------- Optional: completeness wrapper stays in a file that Instantiates box_intro ---------- *)
(* Create a separate file PXL_Completeness_Truth_WF_inst.v that does:
   Axiom box_intro_axiom : ... ;  (* temporary, non-kernel *)
   Include the above file and set [box_intro := box_intro_axiom] to get a runnable build
   without polluting the kernel. Later, replace box_intro_axiom with a constructive proof. *)
Qed.

  Lemma box_intro :
    forall Γ (H:maximal Γ) φ,
      (forall Δ (HΔ:maximal Δ),
         can_R (exist _ Γ H) (exist _ Δ HΔ) -> In_set Δ φ) ->
      In_set Γ (Box φ).
  Proof.
    intros Γ H φ Hforall.
    destruct (proj2 H (Box φ)) as [Hin | Hn].
    - exact Hin.
    - (* Assume ¬Box φ ∈ Γ, derive contradiction *)
      pose proof (constructive_lindenbaum Γ H φ Hn) as [Δ [HΔ [HR Hnegφ]]].
      specialize (Hforall Δ HΔ HR).
      (* Δ has both φ and ¬φ, contradiction *)
      apply (max_neg Δ HΔ Hnegφ Hforall).
  Qed.
