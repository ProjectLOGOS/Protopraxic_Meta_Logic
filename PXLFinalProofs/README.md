# PXL Final Proofs

This repository contains the final proofs for the Protopraxic Logic (PXL) system, a modal logic framework.

## Core Phases

- **Phase 1**: Inductive syntax and Prov relation (`PXLv3.v`)
- **Phase 2**: Meta-theorems (`PXLv3_Meta.v`)
- **Phase 3**: S5 Kripke semantics (`S5_Kripke.v`)
- **Phase 5**: Decidability (`PXL_Decidability.v`)

## Triune Overlay

The triune overlay provides theology-neutral proofs of triune grounding formulas using PXL semantics.

### Goals
- Prove necessary co-existence, unity, distinction, and grounded laws of thought.
- Maintain absolute neutrality: no theological axioms in the core.
- Non-intrusion guarantee: overlay can be removed without affecting core proofs.

### Building
```bash
make  # Builds core
coqchk -quiet -R coq PXLs  # Verifies core
```

### Enabling Overlay
To include the triune overlay:
```bash
# The overlay is included in the main build
make
coqchk -quiet -R coq PXLs
```

### Files
- `PXL_TriuneTheory.v`: Definitions and theorem statements.
- `PXL_Completeness_Interface.v`: Thin interface for proofs.
- `PXL_Completeness_Instance.v`: Concrete completeness instance.

### Hygiene
Zero `Axiom`/`Admitted`/`Parameter` in core; overlay has placeholders for proofs.

### Disabling Overlay
Remove `PXL_TriuneTheory.v`, `PXL_Completeness_Interface.v`, `PXL_Completeness_Instance.v` from `_CoqProject` and rebuild.