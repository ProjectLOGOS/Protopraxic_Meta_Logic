# PXLv3 Meta Proof Packet (S5, explicit proofs)

Policy-compliant Coq model and meta theorems:
- Explicit proofs (no automation).
- Top-level notations/definitions.
- Windows PowerShell build via `coqc`, reading `_CoqProject`.

## Files
- `coq/_CoqProject` — library map and file list.
- `coq/PXLv3_Meta.v` — trivial S5 model + full S5 meta theorems.
- `coq/meta-build.ps1` — Windows build script.

## Build (Windows PowerShell)
```powershell
cd coq
powershell -NoProfile -ExecutionPolicy Bypass -File .\meta-build.ps1 -Clean
```
Artifacts: `PXLv3_Meta.vo`
