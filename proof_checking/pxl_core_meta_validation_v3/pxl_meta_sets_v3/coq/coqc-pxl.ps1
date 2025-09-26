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

# Try to locate coqc.exe in a few likely places, then fallback to searching the user's ROOT
$coqc = @(
    "$PSScriptRoot\..\..\..\..\Coq-Platform~8.20~2025.01\bin\coqc.exe",
    "C:\\Program Files\\Coq Platform\\bin\\coqc.exe",
    "C:\\Program Files\\Coq\\bin\\coqc.exe"
) | Where-Object { Test-Path $_ } | Select-Object -First 1
if (-not $coqc) {
    $root = "C:\\Users\\proje\\OneDrive\\Desktop\\LOGOS SYSTEM\\ROOT"
    try {
        $coqc = Get-ChildItem -Recurse -Filter coqc.exe -Path $root -EA SilentlyContinue |
                        Select-Object -Expand FullName -First 1
    } catch {}
}
if (-not $coqc) { Write-Error "coqc.exe not found; please set PATH or adjust the script."; exit 1 }

Write-Host "Invoking coqc at: $coqc"
& $coqc -Q "$abs" PXLs $File

if ($LASTEXITCODE -ne 0) { Write-Error "coqc failed with exit code $LASTEXITCODE"; exit $LASTEXITCODE }
else { Write-Host "coqc finished successfully" }
