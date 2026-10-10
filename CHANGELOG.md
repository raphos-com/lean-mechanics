# Changelog

## Unreleased

### Phase 5 — linear elastostatics (in progress)
- `Elastostatics/Basic`: strain and stress fields `ε(u) = sym ∇u`, `σ = ℂε`; the **work
  identity** `∫_P σ : ε = ∫_∂P u·σn + ∫_P b·u`; **Clapeyron** `2U = ∫ b·u + ∫ u·σn`; **Betti
  reciprocity**; **Kirchhoff uniqueness** (solutions whose difference does no boundary work
  differ by an infinitesimal rigid displacement); `U ≥ 0`, and `U(u) = 0 ⇒ u` rigid.
- `Elastostatics/MinimumEnergy`: total potential energy `Φ`; `Φ(v) = Φ(u) + U(v − u)`;
  **principle of minimum potential energy** with the rigid-displacement equality case.

### Phase 4 — constitutive theory (in progress)
- `Tensor/DetDeriv`: `det` is smooth; **Jacobi's formula** `D det(F)[H] = det F · tr(F⁻¹H)`,
  i.e. `∂J/∂F = J F⁻ᵀ`.
- `Constitutive/Hyperelastic`: `P = ∂W/∂F` (`IsPiolaOf`), uniqueness of the stress;
  **frame indifference ⇔ `W(F) = Ŵ(FᵀF)`**; `P(QF) = Q P(F)` for frame-indifferent materials.
- `Constitutive/Hyperelastic/SVK`: `D E(F)[H] = sym(FᵀH)`; SVK energy, `P = F ℂ E` derived from
  `DW`; linearisation `d/dt P(I + tH)|₀ = ℂH`.
- `Constitutive/Hyperelastic/NeoHookean`: compressible neo-Hookean energy,
  `P = μF + (λ ln J − μ)F⁻ᵀ` derived from `DW`; linearisation to `λ tr(H) I + 2μ sym H`.
- `Constitutive/LinearIsotropic`: Lamé, `(E, ν)`, `(K, G)` moduli with round trips;
  **`λI⊗I + 2μ𝕀ˢʸᵐ` positive definite on `Sym` ⇔ `μ > 0 ∧ dλ + 2μ > 0`** (any `d ≥ 2`),
  ⇔ `E > 0 ∧ −1 < ν < ½` ⇔ `K > 0 ∧ G > 0` in 3D; steel example.

### Phase 3 — stress (in progress)
- `Stress/Balance`: divergence of vector and tensor fields; `DivergenceRegion` hypothesis
  structure (first entry in `GAPS.md`); `∫_∂P σn = ∫_P div σ`; localisation; **integral force
  balance ⇒ `div σ + b = 0`**; **moment balance ⇒ `σ` symmetric** (coordinate-free, any
  dimension).
- `Stress/Piola`: first and second Piola–Kirchhoff stresses, conversions, and
  `σ sym ⇔ S sym ⇔ PFᵀ sym`.
- `Stress/Criteria`: `J₂`, von Mises; principal stresses in 3D; `J₂` principal formula;
  `(√3/2) σ_T ≤ σ_vM ≤ σ_T`.

### Phase 2 — kinematics (in progress)
- `Kinematics/Strain`: `C`, `B`, Green–Lagrange, Almansi; `C = U²`, `B = V²`, `E = FᵀeF`,
  `C = I ⇔ F` orthogonal.
- `Kinematics/Observer`: objectivity of `B`, `V`; invariance of `C`, `E`, `U`; `R* = QR`.
- `Kinematics/Infinitesimal`: `E(I+H) = sym H + ½HᵀH`, `‖E − ε‖ ≤ ½‖H‖²`, `ε` as derivative of
  `E`; `ε = 0 ⇔ H` skew.
- `Kinematics/Body`: deformations of an open body, gradient, Jacobian, displacement,
  change of observer; `IsUnit F ↔ det F ≠ 0`.
- `Kinematics/Rigid`: skew displacement gradient (equivalently zero infinitesimal strain) on a
  connected open set ⇒ infinitesimal rigid displacement `u = a + Wx`.

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
- `Beams/EulerBernoulli/Energy`: Green's formula; fundamental lemma of the calculus of
  variations on an interval; **strong form + natural BCs ⇔ weak form** for simply supported
  beams; exact expansion and Gateaux derivative of `Π`; **minimum potential energy**.
- `Beams/Timoshenko/Basic`: Timoshenko equations; simply supported and cantilever boundary
  conditions; explicit homogeneous solutions; uniqueness of `C²` solutions.
- `Beams/Timoshenko/Limit`: Timoshenko solution built from any `C⁴` Euler–Bernoulli solution
  (`θ = w'`, `w_T = w − EI(w'' − c)/κGA`); **uniform convergence `w_T → w_EB` as `κGA → ∞` for
  general loads** (simply supported and cantilever), with rate `2EI‖w''‖∞/κGA`; non-vacuity of
  the hypotheses; canonical shear corrections `qL²/8κGA` and `PL/κGA`.
- `Beams/Buckling`: pinned–pinned column `EI w'''' + P w'' = 0`: nontrivial solutions exist iff
  `P = n²π²EI/L²` (modes `sin(nπx/L)`); **Euler load `π²EI/L²` is the least buckling load**.

### Phase 1 — tensor algebra (complete)
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
- `Tensor/Isotropic4`: reflections; **representation theorem** — every isotropic fourth-order
  tensor equals `λ I⊗I + 2μ 𝕀ˢʸᵐ` on symmetric tensors (any dimension `≥ 2`), and conversely.
- `Tensor/Matrix`: `3 × 3` matrix bridge (`ofMatrix`) with trace/det/transpose/invariant
  lemmas; worked examples (invariants of `diag(1,2,3)`, simple shear).

### Phase 0 — project setup
- Design documents `ARCHITECTURE.md`, `ROADMAP.md` (reviewed).
- Lake project pinned to Lean `v4.34.1` and Mathlib `v4.34.1`.
- CI: build with warnings as errors, sorry/axiom guard
  (`scripts/check_no_sorry_axiom.sh`), doc-gen4 documentation published to
  GitHub Pages from `main`.
- `ContinuumMechanics/Basic/Notation.lean`: scoped transpose notation `Aᵀ`.
