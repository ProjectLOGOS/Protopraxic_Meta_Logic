# PXLv3 Proof Sets — S5 Kripke, Deep Soundness, Independence + Barcan

Policy-compliant Coq packet. Explicit proofs, top-level defs, Windows PS build.

Files:
- coq/_CoqProject
- coq/S5_Kripke.v
- coq/PXL_Deep_Soundness.v
- coq/S5_Independence_Barcan.v
- coq/meta-build.ps1

Build:
  cd coq
  powershell -NoProfile -ExecutionPolicy Bypass -File .\meta-build.ps1 -Clean
