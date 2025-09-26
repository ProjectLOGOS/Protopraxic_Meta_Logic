# Phase-4 Completeness Execution

Exit criteria:
- No `Axiom`, no `Admitted`, no `*_ax` in Phase-4 path.
- `coqchk -R . PXLc` succeeds from a clean build.

Strike order:
1) eval_forces_equiv  structural induction.
2) truth_lemma_can → structural induction using maximal closure + Lindenbaum.
3) Replace prov_dual_box_dia* with derivations or imports.
4) can_R_euclidean from ax_5.
5) maximal_contains_theorems, maximal_MP_closed.
6) Hygiene scan; rebuild; coqchk.

Commands:
  pwsh -File .\scripts\phase4-scan.ps1
  Ctrl+Shift+B   # build task
  pwsh -File .\scripts\phase4-verify.ps1
  coqchk -R . PXLc
