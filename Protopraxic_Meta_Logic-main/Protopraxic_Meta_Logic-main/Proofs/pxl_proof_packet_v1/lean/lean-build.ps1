param([switch]$Clean)

$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot

if (-not (Test-Path ".\lakefile.lean")) { Write-Error "Run from the 'lean' folder"; exit 1 }

# Ensure toolchain from lean-toolchain is installed
try { & lake env lean --version | Out-Null } catch {
  Write-Host "Lean not available in PATH. Install elan + Lean 4.10.0, then re-run." -ForegroundColor Yellow
  exit 1
}

if ($Clean) {
  if (Test-Path ".\build") { Remove-Item -Recurse -Force ".\build" }
}

# Restore deps and build
& lake update
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

& lake build
exit $LASTEXITCODE
