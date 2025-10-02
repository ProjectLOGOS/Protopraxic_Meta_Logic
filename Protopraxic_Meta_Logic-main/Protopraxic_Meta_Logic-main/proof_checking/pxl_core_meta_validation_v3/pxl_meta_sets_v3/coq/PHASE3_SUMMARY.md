Phase 3 summary — exact declarations, plain-English descriptions, and file:line links

Files considered: `PXL_Deep_Soundness.v`, `S5_Kripke.v`, `S5_Independence_Barcan.v`, `S5_CounterModels.v` (all in this folder).

Notes on navigation
- File:line links are relative to this `coq` folder. Paste the path into your editor or use the file explorer to jump to the line.
- The packet verifies via the canonical scripts (`meta-build.ps1` + `coqchk -R . PXLs`).

PXL_Deep_Soundness.v
- proof file: `PXL_Deep_Soundness.v`
	- Line 34: Fixpoint declaration
		- Fixpoint eval (F:frame) (v:valuation F) (w:W F) (φ:form) {struct φ} : Prop :=
			(semantic evaluation function for the deep embedding)
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:34

	- Line 63: Lemma sound_K
		- Lemma sound_K : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
				eval F v w (Impl (Box (Impl p q)) (Impl (Box p) (Box q))).
		- Plain English: the standard K axiom is semantically valid (box distributes over implication).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:63

	- Line 70: Lemma sound_T
		- Lemma sound_T : forall (F:frame) (v:valuation F) (w:W F) (p:form),
				eval F v w (Impl (Box p) p).
		- Plain English: T is valid on reflexive frames (if □p then p).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:70

	- Line 76: Lemma sound_4
		- Lemma sound_4 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
				eval F v w (Impl (Box p) (Box (Box p))).
		- Plain English: 4 (positive introspection □p -> □□p) is valid on transitive frames.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:76

	- Line 82: Lemma sound_5
		- Lemma sound_5 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
				eval F v w (Impl (Dia p) (Box (Dia p))).
		- Plain English: 5 (if ◇p then □◇p) holds on Euclidean frames (part of S5).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:82

	- Line 90: Lemma sound_PL_imp
		- Lemma sound_PL_imp : forall (F:frame) (v:valuation F) (w:W F) (p q r:form),
				eval F v w (Impl (Impl p q) (Impl (Impl q r) (Impl p r))).
		- Plain English: propositional implication axiom is valid under evaluation.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:90

	- Line 96: Lemma sound_PL_and1
		- Lemma sound_PL_and1 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
				eval F v w (Impl (And p q) p).
		- Plain English: projection of conjunction to first conjunct.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:96

	- Line 102: Lemma sound_PL_and2
		- Lemma sound_PL_and2 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
				eval F v w (Impl (And p q) q).
		- Plain English: projection of conjunction to second conjunct.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:102

	- Line 108: Lemma sound_mp
		- Lemma sound_mp : forall (F:frame) (p q:form),
				valid_on F (Impl p q) -> valid_on F p -> valid_on F q.
		- Plain English: modus ponens preserves validity.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:108

	- Line 114: Lemma sound_nec
		- Lemma sound_nec : forall (F:frame) (p:form),
				valid_on F p -> valid_on F (Box p).
		- Plain English: necessitation preserves validity (if p is valid then so is □p).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:114

	- Line 120: Fixpoint soundness (main deep soundness theorem)
		- Fixpoint soundness (F:frame) (φ:form) (H:Prov φ) : valid_on F φ :=
			(constructive recursive proof that each Prov rule yields a valid formula)
		- Plain English: every provable formula (Prov φ) is valid on any S5 frame (reflexive, symmetric, transitive).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/PXL_Deep_Soundness.v:120

S5_Kripke.v
- proof file: `S5_Kripke.v`
	- Line 24: Lemma K_sem
		- Lemma K_sem : forall p q, (forall w, box (fun x => p x -> q x) w -> (box p w -> box q w)).
		- Plain English: local distribution of implication under box (semantic K).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:24

	- Line 31: Lemma T_sem
		- Lemma T_sem : forall p, forall w, box p w -> p w.
		- Plain English: reflexivity yields T: □p -> p.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:31

	- Line 36: Lemma Four_sem
		- Lemma Four_sem : forall p, forall w, box p w -> box (box p) w.
		- Plain English: transitivity yields 4: □p -> □□p.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:36

	- Line 42: Lemma Five_sem
		- Lemma Five_sem : forall p, forall w, dia p w -> box (dia p) w.
		- Plain English: Euclidean property (via symmetry+trans) yields 5: ◇p -> □◇p.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:42

	- Line 52: Lemma dual_box_dia
		- Lemma dual_box_dia : forall p w, box p w <-> ~ dia (fun x => ~ p x) w.
		- Plain English: box and dia are duals under classical negation.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:52

	- Line 61: Lemma dual_dia_box
		- Lemma dual_dia_box : forall p w, dia p w <-> ~ box (fun x => ~ p x) w.
		- Plain English: dia and box duality (other direction).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:61

	- Line 71: Lemma mono_box
		- Lemma mono_box : forall p q w, (forall x, p x -> q x) -> box p w -> box q w.
		- Plain English: box is monotone in its argument.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:71

	- Line 76: Lemma mono_dia
		- Lemma mono_dia : forall p q w, (forall x, p x -> q x) -> dia p w -> dia q w.
		- Plain English: dia is monotone in its argument.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:76

	- Line 81: Lemma dist_box_and
		- Lemma dist_box_and : forall p q w, box (fun x => p x /\ q x) w <-> (box p w /\ box q w).
		- Plain English: box distributes over conjunction (and vice versa).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:81

	- Line 90: Lemma dist_dia_or
		- Lemma dist_dia_or : forall p q w, dia (fun x => p x \/ q x) w <-> (dia p w \/ dia q w).
		- Plain English: diamond distributes over disjunction.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:90

	- Line 99: Lemma collapse_box
		- Lemma collapse_box : forall p w, box p w <-> box (box p) w.
		- Plain English: in S5 frames boxes collapse (□p <-> □□p).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:99

	- Line 106: Lemma collapse_dia_box
		- Lemma collapse_dia_box : forall p w, dia p w <-> box (dia p) w.
		- Plain English: diamond and box collapse in S5 (◇p <-> □◇p).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:106

	- Line 114: Lemma collapse_box_dia
		- Lemma collapse_box_dia : forall p w, box p w <-> dia (box p) w.
		- Plain English: another form of the S5 collapse (relating □ and ◇).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Kripke.v:114

S5_Independence_Barcan.v
- proof file: `S5_Independence_Barcan.v`
	- Line 22: Lemma T_fails
		- Lemma T_fails : exists w, box (F:=Ft) p w /\ ~ p w.
		- Plain English: a concrete non-reflexive frame (`NonReflexive_T`) where □p holds at a world but p does not — shows T is independent (fails) in that frame.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Independence_Barcan.v:22

	- Line 52: Lemma Barcan_constant
		- Lemma Barcan_constant : forall w,
				(forall x:D, box_const (fun w => P w x) w) ->
				box_const (fun w => forall x:D, P w x) w.
		- Plain English: Barcan schema holds under constant domains: if each instance □P(x) holds then □(∀x P(x)).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Independence_Barcan.v:52

	- Line 59: Lemma Converse_Barcan_constant
		- Lemma Converse_Barcan_constant : forall w,
				box_const (fun w => forall x:D, P w x) w ->
				forall x:D, box_const (fun w => P w x) w.
		- Plain English: the converse Barcan schema under constant domains.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_Independence_Barcan.v:59

	- Import note: `From PXLs Require Import S5_CounterModels.` is used to access the constructive countermodels `Four_fails` and `Five_fails`.

S5_CounterModels.v
- proof file: `S5_CounterModels.v`
	- Line 17: Fixpoint satisfies
		- Fixpoint satisfies (M: model) (w: world M) (φ: form) : Prop := ...
		- Plain English: the deep-model satisfaction relation for the tiny propositional modal language used in the countermodels.
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_CounterModels.v:17

	- Line 50: Lemma Four_fails
		- Lemma Four_fails : exists w: W, satisfies M4 w (box (atom 0)) /\ ~ satisfies M4 w (box (box (atom 0))).
		- Plain English: a concrete 3-world model showing 4 (□p -> □□p) fails (so 4 is independent there).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_CounterModels.v:50

	- Line 79: Lemma Five_fails
		- Lemma Five_fails : exists w:W, satisfies M5 w (dia (atom 0)) /\ ~ satisfies M5 w (box (dia (atom 0))).
		- Plain English: a concrete 3-world model showing 5 (◇p -> □◇p) fails (so 5 is independent there).
		- File: proof_checking/pxl_core_meta_validation_v3/pxl_meta_sets_v3/coq/S5_CounterModels.v:79

Status: All listed lemmas are present in source and compile to `.vo`; packet-level verification with `meta-build.ps1 -Clean` and `coqchk -R . PXLs` returns "Modules were successfully checked".

Follow-ups (pick any):
- Add exact copy of each lemma body into this file (I can expand each entry to include the full multi-line Coq declaration and short proof sketch).
- Produce a one-page English explainer (for non-Coq readers) describing the significance of each lemma.
- Create editor/bookmark-friendly clickable links (I can generate a VS Code workspace snippet or tasks file that opens each file at the desired line).

Which of those follow-ups do you want next? (I can do all of them incrementally if you prefer.)
