<#
coqc-pxl.ps1
Helper to compile Coq files using the project's logical path mapping PXLs.
Usage: .\coqc-pxl.ps1 <file.v>

It makes the script robust on Windows by using the script directory as the absolute -Q mapping.
#>
param(
    [Parameter(Mandatory=$true)][string]$File
)

# Resolve script directory (the coq folder)
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Definition
$abs = (Get-Item $scriptDir).FullName

# If the user passed a full path, keep it; otherwise use the file as-is
if (-not (Test-Path $File)) {
    # try relative to script dir
    $candidate = Join-Path $abs $File
    if (Test-Path $candidate) { $File = $candidate }
}

Write-Host "Using -Q '$abs' PXLs to compile $File"

# Run coqc with the absolute mapping
coqc -Q "$abs" PXLs $File

if ($LASTEXITCODE -ne 0) { Write-Error "coqc failed with exit code $LASTEXITCODE"; exit $LASTEXITCODE }
else { Write-Host "coqc finished successfully" }
