# D6 Exact Lean Extraction

This is the standalone Lean slice for the d=6 exact-base publication proof.

## Main entry point

- `E677.D6Publication`

## Included modules

- `E677.Basic`: magma operation and E677/E255 definitions.
- `E677.D6CoreMinimal`: finite E677 left-cancellation infrastructure used by the d=6 proof.
- `E677.ExactBaseGeneric`: row-local exact-base proof.
- `E677.D6Isolated`: compact d=6 context and supporting rows.
- `E677.D6Publication`: publication-facing API and exact-base packet theorem.

## Build

```bash
lake build
# or, for only the publication entry point:
lake build E677.D6Publication
```

The local `.lake/` directory is ignored. In this workspace it may be symlinked to the parent project's downloaded mathlib packages for validation. In a fresh repo, run the usual Lake dependency setup for Lean `v4.29.0` and mathlib `v4.29.0` before building.
