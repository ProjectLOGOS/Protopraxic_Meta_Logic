# 0) Go to the logical root for these modules
Set-Location -LiteralPath "proof_checking\pxl_completeness_proofs_v4\pxl_phase4_completeness\coq"
Get-Location

# 1) Hard clean compiled artifacts (non-blocking)
Get-ChildItem -Recurse -File -Include *.vo,*.vos,*.vok `
  | Remove-Item -Force -ErrorAction SilentlyContinue
Write-Host "[clean] removed .vo/.vos/.vok under coq/"

# 2) Rebuild TEMP files with a single -Q root
coqc -Q . PXLs TEMP_minimal.v;  Write-Host "[build] TEMP_minimal exit:$LASTEXITCODE"
coqc -Q . PXLs TEMP_linden.v;   Write-Host "[build] TEMP_linden  exit:$LASTEXITCODE"

# 3) Ensure Sketch has the import (add it if missing), then rebuild
$sketch = "PXL_Completeness_Sketch.v"
if (-not (Select-String -Path $sketch -Pattern 'From PXLs Require Import TEMP_minimal.' -Quiet)) {
  ('From PXLs Require Import TEMP_minimal.' + [Environment]::NewLine) + (Get-Content $sketch -Raw) `
    | Set-Content $sketch -NoNewline
  Write-Host "[patch] inserted 'From PXLs Require Import TEMP_minimal.' at top of $sketch"
}
coqc -Q . PXLs PXL_Completeness_Sketch.v; Write-Host "[build] Sketch     exit:$LASTEXITCODE"

# 4) Rebuild Truth Skeleton and run coqchk
coqc  -Q . PXLs PXL_Completeness_Truth_Skeleton.v; Write-Host "[build] Truth_Skel exit:$LASTEXITCODE"
coqchk -R . PXLs;                                   Write-Host "[check] coqchk     exit:$LASTEXITCODE"

# 5) If any build fails, show the first missing reference and confirm import/root
if ($LASTEXITCODE -ne 0) {
  Write-Host "[diag] showing first missing reference lines:"
  Select-String -Path $sketch -Pattern 'taut_imp_trans|TEMP_minimal' -n | Select-Object -First 10
  Write-Host "[diag] current root:" (Get-Location).Path
}
