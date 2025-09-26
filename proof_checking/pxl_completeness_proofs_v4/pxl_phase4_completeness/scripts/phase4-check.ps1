$phase = "proof_checking/pxl_completeness_proofs_v4/pxl_phase4_completeness/coq"
$files = Get-ChildItem $phase -Recurse -File -Include *.v
$m = $files | Select-String -Pattern '\bAxiom\b' | Where-Object { $_.Line -notmatch '^\s*\(\*' }

$out = @()
if ($m) {
  $out += "BLOCKED: Axiom lines remain."
  $m | ForEach-Object { $out += ("{0}:{1}: {2}" -f $_.Path, $_.LineNumber, $_.Line.Trim()) }
} else {
  $out += "OK: no Axiom lines in Phase-4."
}

# Also show Admitted count
$adm = $files | Select-String -Pattern '\bAdmitted\b'
$out += ("Admitted count in Phase-4: {0}" -f ($adm.Count))

$out | Set-Content PHASE4_SCAN_RESULT.txt
Write-Host "Wrote PHASE4_SCAN_RESULT.txt"
