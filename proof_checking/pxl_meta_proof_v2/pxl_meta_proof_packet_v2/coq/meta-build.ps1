param([switch]$Clean)
$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot
if ($Clean) {
  Get-ChildItem -Filter *.vo -Recurse | Remove-Item -Force -ErrorAction SilentlyContinue
  Get-ChildItem -Filter *.glob -Recurse | Remove-Item -Force -ErrorAction SilentlyContinue
}
$proj = Join-Path $PSScriptRoot "_CoqProject"
if (-not (Test-Path $proj)) { Write-Error "_CoqProject not found"; exit 1 }
$opts = @(); $files = @()
Get-Content $proj | ForEach-Object {
  $l = $_.Trim()
  if ($l -eq "" -or $l.StartsWith("#")) { return }
  if ($l.StartsWith("-Q") -or $l.StartsWith("-R")) { $opts += ($l -split "\s+") }
  elseif ($l -match "\.v$") { $files += $l }
}
foreach ($f in $files) {
  & coqc -q @opts $f
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}
exit 0
