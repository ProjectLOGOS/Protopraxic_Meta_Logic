$phase = "proof_checking/pxl_completeness_proofs_v4/pxl_phase4_completeness/coq"
$hits = Get-ChildItem $phase -Recurse -Filter *.v | Select-String -Pattern '\b(Axiom|Admitted|_ax)\b'
if ($hits) {
  Write-Host "BLOCKED: Phase-4 still has stubs."
  $hits | ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line.Trim())" } | Set-Content PHASE4_AXIOMS.md
  exit 1
}
Write-Host "OK: Phase-4 path clean (no Axiom/Admitted/_ax)."
