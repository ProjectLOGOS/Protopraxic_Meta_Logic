$phase = "proof_checking/pxl_completeness_proofs_v4/pxl_phase4_completeness/coq"
$files = Get-ChildItem $phase -Recurse -File -Include *.v
$axioms = $files | Select-String -Pattern '\bAxiom\b' | Where-Object { $_.Line -notmatch '\(\*' }
if ($axioms) {
  Write-Host 'BLOCKED: Axiom lines remain.'
  $axioms | ForEach-Object { Write-Host ("{0}:{1}: {2}" -f $_.Path,$_.LineNumber,$_.Line.Trim()) }
} else {
  Write-Host 'OK: no Axiom lines in Phase-4.'
}
$adm = $files | Select-String -Pattern '\bAdmitted\b'
Write-Host ('Admitted count in Phase-4: ' + $adm.Count)
Get-Content PHASE4_AXIOMS.md | Select-Object -First 40 | ForEach-Object { Write-Host $_ }
