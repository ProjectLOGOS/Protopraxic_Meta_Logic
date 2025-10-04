# PXLFinalProofs

Self-contained Coq packet for PXL Phases 1–5.

## Build
- Coq Platform: 8.20.x
- From this folder:
  \\\
  make          # builds all .vo via coq_makefile
  make check    # coqchk kernel check
  make hygiene  # scans for Axiom|Admitted|Parameter
  \\\

Logical path: \-Q coq PXLs\. Sources import with \From PXLs Require Import ...\.

## Contents
- coq/PXLv3.v                     — Phase 1 (syntax, Prov)
- coq/PXLv3_Meta.v                — Phase 2
- coq/S5_Kripke.v                 — Phase 3 (semantics)
- coq/PXL_Decidability.v          — Phase 5 (decidability)
- coq/PXL_Completeness_Truth_WF.v — Phase 4 (completeness)

## Reproduce
\\\
make clean && make && make check && make hygiene
\\\
"@ | Set-Content -NoNewline -Encoding UTF8 (Join-Path C:\Users\proje\OneDrive\Desktop\LOGOS SYSTEM\ROOT\PXLFinalProofs 'README.md')

# 7) Build scripts
@"
param()
Set-StrictMode -Version Latest
\System.Management.Automation.DefaultParameterDictionary['Out-File:Encoding'] = 'utf8'
Push-Location \\..
try {
  if (-not (Get-Command make -ErrorAction SilentlyContinue)) { Write-Host 'Note: make not found; installing via choco/scoop may be required.' }
  & make
  if (\2) { exit \2 }
  & make check
  if (\2) { exit \2 }
  & make hygiene
  exit \2
} finally { Pop-Location }