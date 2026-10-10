# Changelog

## Unreleased

### Phase 1 — tensor algebra (in progress)
- `Tensor/Second`: `Lin E`, transpose, trace, determinant (`det Aᵀ = det A`), dyads.
- `Tensor/SymSkew`: `Sym E`, `Skw E`, `sym`/`skw`, `Lin E = Sym ⊕ Skw` with uniqueness.
- `Tensor/Contraction`: double contraction `A ⊡ B = tr(AᵀB)` as an inner product;
  `Frob E` Hilbert-space synonym.
- `Tensor/Spherical`: spherical/deviatoric decomposition.
- `Tensor/Invariants`: `I₁ I₂ I₃`, orthogonal invariance, characteristic polynomial and
  Cayley–Hamilton `A³ − I₁A² + I₂A − I₃I = 0` in dimension three.
- `Tensor/Orthogonal`: `Orth E = unitary (Lin E)`, `Rot E` (`det = 1`), `det Q = ±1`.
- `Tensor/Positive`: continuous functional calculus on real `Lin E` (transferred from
  matrices), `StarOrderedRing`, existence and uniqueness of positive square roots.

### Phase 0 — project setup
- Design documents `ARCHITECTURE.md`, `ROADMAP.md` (reviewed).
- Lake project pinned to Lean `v4.34.1` and Mathlib `v4.34.1`.
- CI: build with warnings as errors, sorry/axiom guard
  (`scripts/check_no_sorry_axiom.sh`), doc-gen4 documentation published to
  GitHub Pages from `main`.
- `ContinuumMechanics/Basic/Notation.lean`: scoped transpose notation `Aᵀ`.
