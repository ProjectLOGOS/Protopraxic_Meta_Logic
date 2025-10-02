This file explains, in plain English, the main Phase-3 lemmas and their roles.

S5_Kripke.v
- Purpose: Define Kripke frames and the modal operators `box` and `dia` as predicates on worlds. Prove the semantic versions of modal axioms for S5 (K, T, 4, 5) and useful lemmas like distribution and dualities between box and dia.
- Why it matters: These lemmas tie the syntactic modal axioms to model-theoretic truth conditions. The collapse lemmas show that in S5 frames certain nested modalities reduce to simpler ones.

PXL_Deep_Soundness.v
- Purpose: Provide a deep embedding of the object logic (syntax `form`) and an evaluation function `eval` parameterized by a valuation. Define the inductive `Prov` proof object and prove `soundness` — that any provable formula is valid in all models.
- Why it matters: Soundness is crucial: it guarantees the proof system doesn't derive false statements with respect to the intended semantics.

S5_CounterModels.v
- Purpose: Construct explicit Kripke models (three-world constructive models) showing that the 4 and 5 axioms are not derivable in general frames without their frame properties. The lemmas `Four_fails` and `Five_fails` supply witness models and worlds where the axiom instances fail.
- Why it matters: Independence proofs show which axioms require which frame properties; they help justify adding axioms to a base modal logic.

S5_Independence_Barcan.v
- Purpose: Use the countermodels module to show `Four_fails` and `Five_fails` hold as independence results. Also proves the Barcan and Converse-Barcan schemas under the constant-domain assumption.
- Why it matters: These results complete Phase-3's goal to show independence and the behavior of quantifiers across modal operators under domain assumptions.

Files added for developer convenience:
- `coqc-pxl.ps1`: helper to compile a single `.v` by binding the project's `coq` directory to the logical `PXLs` path on Windows robustly.
- `PHASE3_SUMMARY.md` and `PHASE3_FULL_STATEMENTS.md`: summaries and copied statements to help navigation, review, and editor automation.
PHASE 3 — Plain-English explainer for main lemmas

This note gives short, accessible descriptions for the principal lemmas and theorems in the Phase‑3 Coq packet. It maps each statement to an intuitive claim and notes the proof strategy used in the Coq sources.

1) PXL_Deep_Soundness.v
- What it claims: Every provable formula (Prov φ) in the deep embedding is valid on any Kripke frame whose accessibility relation is an equivalence (S5 frames).
- Proof idea: We define a compositional evaluation function `eval` on frames, then prove that each axiom schema evaluates to a tautology in the semantics (sound_K, sound_T, sound_4, sound_5, etc.). For the rules (mp, nec) we prove that truth is closed under modus ponens and necessitation. The main `soundness` is a structural recursion on `Prov` that dispatches to the individual soundness lemmas.
- Why it matters: This is the fundamental connection from the syntactic provability relation (Prov) to semantic truth in S5 models: provable => valid.

2) S5_Kripke.v
- What it claims: Basic semantic properties of the S5 modal operators on Kripke frames with reflexive, symmetric, transitive R.
- Key lemmas and intuition:
  - `K_sem`: distribution of `box` over implication (modal K axiom).
  - `T_sem`: reflexivity gives `box p -> p` (T axiom semantically).
  - `Four_sem`: transitivity gives `box p -> box box p` (4 axiom semantically).
  - `Five_sem`: symmetry+transitivity give `dia p -> box dia p` (5 axiom semantically).
  - `dual_*` lemmas: De Morgan-style dualities between `box` and `dia`.
  - `collapse_*` lemmas: in S5 the nesting of modalities collapses: `box p` <-> `box box p`, `dia p` <-> `box dia p`, etc.
- Proof strategy: Pointwise reasoning about worlds; unpack definitions of `box`/`dia` and apply frame axioms.

3) S5_Independence_Barcan.v
- What it claims: Demonstrates independence (countermodels) for modal axioms outside the core system and proves Barcan/Converse-Barcan under constant-domain assumptions.
- Components:
  - `NonReflexive_T.T_fails`: constructs a 2-world frame where reflexivity fails at one world, showing `T` is not valid universally.
  - Barcan/Converse_Barcan lemmas: In a constant-domain setting these two schematic translations are interchangeable with `forall`/`box` commuting; proofs are straightforward pointwise manipulations.
  - Imports `S5_CounterModels` for constructive models of `Four_fails` and `Five_fails`.
- Proof strategy: Build small Kripke-style frames (2–3 worlds) with carefully chosen accessibility and valuations to falsify specific modal axioms. For Barcan results, use pointwise reasoning over the constant domain.

4) S5_CounterModels.v
- What it claims: Provides explicit 3‑world countermodels showing `4` and `5` can fail when the frame is not transitive/symmetric respectively.
- Strategy and guarantees: The models are self-contained with an inductive `form`, a `model` record and `satisfies` predicate. Each failure lemma (`Four_fails`, `Five_fails`) constructs a world where the antecedent holds but the nested modality fails.

Notes for maintainers
- File ordering matters when compiling with `coqc`: `S5_Kripke.v` and `PXL_Deep_Soundness.v` must come before `S5_Independence_Barcan.v`.
- On Windows, `-Q` argument with an absolute path is safer than `-Q . PXLs`. Use `coqc-pxl.ps1 <file>.v` in the `coq` folder to compile single files reliably.
- `PHASE3_FULL_STATEMENTS.md` and `PHASE3_SUMMARY.md` give quick entry points: the former contains full Coq snippets; the latter has line numbers and brief summaries.

If you want, I can:
- Expand these plain-English explanations into a developer-oriented README section with links to the exact line numbers.
- Add `vscode` tasks to jump to lemma locations (I can generate `.vscode/tasks.json`).
- Produce a machine-readable JSON manifest mapping lemma names to file paths and line numbers.

