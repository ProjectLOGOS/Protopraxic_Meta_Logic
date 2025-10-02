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

## Quickstart additions: Windows Coq / Lean

### Windows (PowerShell) — Coq
```powershell
cd coq
powershell -NoProfile -ExecutionPolicy Bypass -File .\coq-build.ps1 -Clean
# Artifacts: *.vo
```

### Linux/macOS — Coq

```bash
cd coq
coq_makefile -f _CoqProject -o Makefile
make -j
```

### Lean 4

```powershell
cd lean
lake env lean --version   # expect 4.10.x
lake update
lake build                # artifacts: build/lib/*.olean
```

## Contents
- `lean/`: Lean 4 project with abstract system, deduction, model, soundness, meta.
- `coq/`: Coq project mirroring Lean sources.
- `data/`: Canonical sources (axioms, language definition).
- `reports/`: Static audits from uploaded corpus.
- `scripts/`: convenience runners.
- `ci/`: GitHub Actions example.

Generated: 2025-09-24T08:33:42
