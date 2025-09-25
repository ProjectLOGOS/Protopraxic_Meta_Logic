Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Push-Location lean
lake build
Pop-Location

Push-Location coq
if (-not (Test-Path Makefile)) { coq_makefile -f _CoqProject -o Makefile }
make -j
Pop-Location

Write-Host "OK: Lean+Coq build passed."
