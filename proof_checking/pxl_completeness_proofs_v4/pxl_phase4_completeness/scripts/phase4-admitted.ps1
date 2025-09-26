$phase='proof_checking/pxl_completeness_proofs_v4/pxl_phase4_completeness/coq'
$files=Get-ChildItem $phase -Recurse -File -Include *.v
$count = ($files | Select-String -Pattern '\bAdmitted\b').Count
Write-Host ('Admitted count in Phase-4: ' + $count)
