# Generates a sorted admits/axioms log for the current coq folder
$files = Get-ChildItem -Recurse -Filter *.v
$out = @()
foreach ($f in $files) {
  $matches = Select-String -Path $f.FullName -Pattern 'Admitted\.|Axiom'
  foreach ($m in $matches) {
    $out += ("$($m.Path):$($m.LineNumber):$($m.Line.Trim())")
  }
}
$out = $out | Sort-Object
$out | Out-File admits_after_provimp_full.log -Encoding utf8
Write-Host "Wrote admits_after_provimp_full.log with $($out.Count) entries."
