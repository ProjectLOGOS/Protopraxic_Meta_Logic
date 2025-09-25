param(
  [string]$CoqProj = "$PSScriptRoot\_CoqProject",
  [string]$CoqExe = "coqc",
  [switch]$Clean
)
if (-not (Test-Path $CoqProj)) { Write-Error "_CoqProject not found"; exit 1 }

$opts = @(); $files = @()
Get-Content $CoqProj | ForEach-Object {
  $l = $_.Trim()
  if ($l -eq "" -or $l.StartsWith("#")) { return }
  if ($l.StartsWith("-Q") -or $l.StartsWith("-R")) { $opts += ($l -split "\s+") }
  elseif ($l -match "\.v$") { $files += $l }
}

if ($Clean) {
  Get-ChildItem -Filter *.vo -Recurse | Remove-Item -Force -ErrorAction SilentlyContinue
  Get-ChildItem -Filter *.glob -Recurse | Remove-Item -Force -ErrorAction SilentlyContinue
}

$LASTEXITCODE = 0
foreach ($f in $files) {
  & $CoqExe -q @opts $f
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

# compile any extra .v not listed in _CoqProject (best-effort)
$listed = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
$files | ForEach-Object { [void]$listed.Add($_) }
Get-ChildItem -Recurse -Filter *.v | ForEach-Object {
  $rel = $_.FullName.Substring((Get-Location).Path.Length+1)
  if (-not $listed.Contains($rel)) {
    & $CoqExe -q @opts $_.FullName
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
}
