coq/README.md

This folder contains the Coq sources for the packet and a small helper script
`coqc-pxl.ps1` that compiles files with the project's logical path mapping
(PXLs) in a Windows-friendly way.

Why this helper
- The project uses the logical path `PXLs` (see `_CoqProject`).
- On Windows, quoting and absolute paths can make ad-hoc `coqc` invocations
  fragile. `coqc-pxl.ps1` resolves the `coq` folder path and runs `coqc`
  with a robust `-Q "<absolute-path>" PXLs` mapping.

Quick usage (PowerShell)

# From inside this `coq` folder
.
```
# Compile a single file using the helper
.\coqc-pxl.ps1 S5_Independence_Barcan.v
```

# From any location (the script will try to resolve relative filenames)
```
# Use the full path or a filename relative to the `coq` folder
Path\To\coq\coqc-pxl.ps1 S5_Independence_Barcan.v
```

Direct `coqc` with the canonical mapping
- If you prefer not to use the helper, run `coqc` from the `coq` folder with the
  project's logical path mapping:

```
coqc -Q . PXLs S5_CounterModels.v
coqc -Q . PXLs S5_Independence_Barcan.v
```

Packet-level (recommended) verification
- Use the provided scripts to build and verify the whole packet. These set
  up the correct load paths and are the canonical way to check the project:

```
.\meta-build.ps1 -Clean
coqchk -R . PXLs
```

Notes
- `From PXLs Require Import ...` is the canonical import form used by the
  packet. The helper ensures `PXLs` is bound to this folder for single-file
  `coqc` runs.
- If you want me to add a small batch helper that builds all files in order,
  I can add that too.
