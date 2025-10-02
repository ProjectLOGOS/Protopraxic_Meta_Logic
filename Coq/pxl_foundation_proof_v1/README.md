# PXLv3 Proof Kit

Full dual-tool proof-checking workspace for PXLv3.

## Quick start (Windows PowerShell)

```powershell
# Lean
cd .\lean
lake build

# Coq
cd ..\coq
if (!(Test-Path Makefile)) { coq_makefile -f _CoqProject -o Makefile }
make -j
```

## Quick start (Bash)

```bash
cd lean && lake build
cd ../coq
[ -f Makefile ] || coq_makefile -f _CoqProject -o Makefile
make -j
```

## Contents
- `lean/`: Lean 4 project with abstract system, deduction, model, soundness, meta.
- `coq/`: Coq project mirroring Lean sources.
- `data/`: Canonical sources (axioms, language definition).
- `reports/`: Static audits from uploaded corpus.
- `scripts/`: convenience runners.
- `ci/`: GitHub Actions example.

Generated: 2025-09-24T08:33:42
