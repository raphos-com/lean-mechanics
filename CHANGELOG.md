# Changelog

## Unreleased

### Phase 6 — 1D structural theories (in progress)
- `Beams/Interval`: vanishing `(n+1)`-th derivative on `[a, b]` ⇒ Taylor polynomial.
- `Beams/Bar`: axial bar equilibrium; closed-form fixed–free (uniform + end load, linear
  load) and fixed–fixed (uniform) solutions; uniqueness for both boundary conditions.
- `Beams/Poly`: derivatives of polynomial deflections; `beam_poly` tactic macro.
- `Beams/EulerBernoulli/Basic`: `EI w'''' = q`; simply supported, cantilever, clamped–clamped,
  clamped–pinned boundary conditions; uniqueness of `C⁴` solutions for all four.
- `Beams/EulerBernoulli/Solutions`: simply supported and cantilever beams under uniform load,
  cantilever with tip load, simply supported beam with a point load anywhere (piecewise, with
  continuity and shear-jump conditions); `5qL⁴/384EI`, `qL⁴/8EI`, `PL³/3EI`, `PL³/48EI`.
- `Beams/Timoshenko/Basic`: Timoshenko equations; simply supported and cantilever boundary
  conditions; explicit homogeneous solutions; uniqueness of `C²` solutions.
- `Beams/Timoshenko/Limit`: Timoshenko solution built from any `C⁴` Euler–Bernoulli solution
  (`θ = w'`, `w_T = w − EI(w'' − c)/κGA`); **uniform convergence `w_T → w_EB` as `κGA → ∞` for
  general loads** (simply supported and cantilever), with rate `2EI‖w''‖∞/κGA`; non-vacuity of
  the hypotheses; canonical shear corrections `qL²/8κGA` and `PL/κGA`.

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
- `Tensor/Polar`: polar decomposition `F = RU = VR`, `V = RURᵀ`, uniqueness,
  `det R = 1 ↔ det F > 0`.
- `Tensor/Spectral`: spectral decomposition `S = ∑ λᵢ eᵢ ⊗ eᵢ`; invariants via eigenvalues;
  `S ≥ 0 ↔ λᵢ ≥ 0`.
- `Tensor/Fourth`: `Lin4 E`, minor/major symmetry, `𝕀ˢʸᵐ`, `I ⊗ I`, the isotropic tensor
  `λ I⊗I + 2μ 𝕀ˢʸᵐ` and its symmetries.

### Phase 0 — project setup
- Design documents `ARCHITECTURE.md`, `ROADMAP.md` (reviewed).
- Lake project pinned to Lean `v4.34.1` and Mathlib `v4.34.1`.
- CI: build with warnings as errors, sorry/axiom guard
  (`scripts/check_no_sorry_axiom.sh`), doc-gen4 documentation published to
  GitHub Pages from `main`.
- `ContinuumMechanics/Basic/Notation.lean`: scoped transpose notation `Aᵀ`.
