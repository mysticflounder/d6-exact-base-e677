# The d=6 Exact-Base Branch for E677 Magmas

Formal proof accompanying the paper:

> **The d=6 Exact-Base Branch for E677 Magmas**
> Adam McKenna, May 2026

## Summary

An E677 magma satisfies the identity `a = b ◇ (a ◇ ((b ◇ a) ◇ b))`. We isolate a
branch of the d=6 gap-1 classifier where an outsider element A satisfies
`A ◇ A = c₁`, `A ◇ x = c₃`, `c₃ ◇ c₃ = c₁`. Under these conditions we prove
`((x ◇ x) ◇ x) ◇ x = x`.

The Lean proof is fully verified: the publication theorem depends only on the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Repository Structure

```
paper/      Paper source (Pandoc Markdown) and compiled PDF
lean/       Self-contained Lean 4 formalization
```

## Building the Paper PDF

Requires [Pandoc](https://pandoc.org/) and a LaTeX distribution with TikZ.

```bash
pandoc paper/d6-exact-base-e677.md \
  --pdf-engine=xelatex \
  -o paper/d6-exact-base-e677.pdf
```

## Lean Proof

Requires [Lean 4](https://leanprover.github.io/) with `lake` and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
cd lean
lake build E677.D6Publication
```

The main entry point is `D6ExactBasePacket.fixer` in `lean/E677/D6Publication.lean`.
The minimal import slice is:

```
E677.Basic
E677.D6CoreMinimal
E677.ExactBaseGeneric
E677.D6Isolated
E677.D6Publication
```

## License

[MIT](LICENSE)
