$phase = "proof_checking/pxl_completeness_proofs_v4/pxl_phase4_completeness/coq"
$report = "PHASE4_AXIOMS.md"
Get-ChildItem $phase -Recurse -File -Include *.v |
  Select-String -Pattern '\b(Axiom|Admitted|_ax)\b' |
  Where-Object { $_.Line -notmatch '\(\*' } |
  ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line.Trim())" } |
  Set-Content $report
Write-Host "OK: wrote $report"
