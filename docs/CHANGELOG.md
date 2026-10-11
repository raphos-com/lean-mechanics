# Changelog

## Unreleased

### Restructuring
- `Frames/` moved to the new library **`DiscreteMechanics`** (namespace `DiscreteMechanics`).
- `papers/` is a separate Lake project depending on both libraries; the root package and
  `CITATION.cff` describe the libraries only.
- Design and tracking documents moved to `docs/`.

### DiscreteMechanics
- `LongWave`: `(Σⱼ(2cos⟪k,tⱼ⟫ − 2) + Σⱼ⟪k,tⱼ⟫²)/‖k‖² → 0` for any lattice vectors, the
  isotropic limit `−c`, and the long-wave limit `s z → δ₀⁻¹ N₀ y₀` of Bloch solutions computed
  through an adjugate (`N M = δ I`).
- `Truss`: pin-jointed frames; compatibility matrix `C`, equilibrium matrix `Cᵀ`, virtual work;
  **Maxwell–Calladine** `N₀ − N_ss = d|N| − |B|` (index of a matrix by rank–nullity); rigid
  motions are zero modes; the triangle is rigid (`N₀ = 3`, `N_ss = 0`).
- `Periodic`: periodic frames; Bloch compatibility matrix `C(θ)`, Bloch reduction of the infinite
  frame, Maxwell–Calladine at every wave vector (complex index with `C(θ)ᴴ`), Maxwell lattices
  have as many zero modes as self-stresses at every `θ` and at least `d` self-stresses at `θ = 0`.
- `Winding`: winding number `(2πi)⁻¹∮ p'/p` of a polynomial around the unit circle; **argument
  principle**: it equals the number of roots in the open unit disk (with multiplicity), and is
  additive under products.

### Elastostatics
- `Elastostatics/Korn`: **Korn's first inequality** `∫|∇u|² ≤ 2∫|ε(u)|²` for compactly supported
  `C²` fields in `ℝⁿ`, via `∫|∇u|² + ∫(div u)² = 2∫|ε(u)|²` (integration by parts twice and
  symmetry of second derivatives).

### Kinematics
- `Kinematics/SaintVenant`: **Saint-Venant sufficiency** on open convex domains: a symmetric `C²`
  strain satisfying the compatibility conditions is `sym ∇u`, by two applications of Mathlib's
  Poincaré lemma (rotation field `W` with `∂ₖWᵢⱼ = ∂ⱼεᵢₖ − ∂ᵢεⱼₖ`, then `∇u = ε + W`).

### Plates
- `Plates/Energy`: Kirchhoff–Love bending form `a(w,v) = D∫ν ΔwΔv + (1−ν)∇²w:∇²v` in `ℝⁿ`, the
  classical 2D density, **null Lagrangian** `∫∇²w:∇²v = ∫ΔwΔv`, `a(w,v) = D∫Δ²w v`,
  **strong ⇔ stationary** (`DΔ²w = q` in an open `U` iff `a(w,v) = ∫qv` for all test functions
  in `U`), and **minimum potential energy** for compactly supported solutions.

### Papers (`papers/`, see each README)
- `Nexorade`, `Miura`, `KaneLubensky`, `Gridshells`, `BendingGradient`.
- `Gridshells/Sphere`: a Chebyshev net on the unit sphere satisfies the sine-Gordon equation
  `ω_uv = −sin ω`; its quadrilaterals have area `< 2π`.

### Phase 7 — plates (in progress)
- `Plates/KirchhoffLove`: rectangular plate, partial derivatives, biharmonic operator, plate
  equation `DΔ²w = q`, bending moments, simply supported edges.
- `Plates/Navier`: `Δ²(sin αx sin βy) = (α² + β²)² sin αx sin βy`; **Navier's single-mode solution**
  of the simply supported plate; central deflection `q₀a⁴/(4π⁴D)` of a square plate.
- `Plates/MindlinReissner`: Mindlin–Reissner equations and hard simple supports; single-mode Navier
  solution `W = W_K(1 + Dk²/S)`, `φ = −∇w_K`; **Kirchhoff limit** `W − W_K = q₀/(Sk²) → 0`.

### Phase 5 — linear elastostatics
- `Elastostatics/Weak`: abstract weak formulation `⟪ℂε(u), ε(v)⟫ = ℓ(v)` under the `KornSetting`
  hypothesis structure (Korn's inequality); **Lax–Milgram well-posedness**; the weak solution is the
  unique minimiser of `½a(v,v) − ℓ(v)`; non-vacuity witness.
- `Elastostatics/Basic`: strain and stress fields `ε(u) = sym ∇u`, `σ = ℂε`; the **work
  identity** `∫_P σ : ε = ∫_∂P u·σn + ∫_P b·u`; **Clapeyron** `2U = ∫ b·u + ∫ u·σn`; **Betti
  reciprocity**; **Kirchhoff uniqueness** (solutions whose difference does no boundary work
  differ by an infinitesimal rigid displacement); `U ≥ 0`, and `U(u) = 0 ⇒ u` rigid.
- `Elastostatics/MinimumEnergy`: total potential energy `Φ`; `Φ(v) = Φ(u) + U(v − u)`;
  **principle of minimum potential energy** with the rigid-displacement equality case.

### Phase 4 — constitutive theory
- `Constitutive/RivlinEricksen`: **Rivlin–Ericksen representation theorem**: an isotropic tensor
  function satisfies `G(A) = p(A)` for a polynomial `p` (any dimension, via reflections and
  Lagrange interpolation), and `G(A) = φ₀I + φ₁A + φ₂A²` in 3D (Cayley–Hamilton).
- `Constitutive/Hyperelastic/MooneyRivlin`: compressible Mooney–Rivlin energy; exact splitting
  `W_MR = W_neoHooke(λ, κ) + W_SVK(4c₂, −2c₂)`; `P = 2c₁F + 2c₂(I₁(C)F − FC) + (λ ln J − κ)F⁻ᵀ`;
  stress-free reference; linearisation with `μ' = 2c₁ + 2c₂(d − 2)`, `λ' = λ + 4c₂`.
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

### Phase 3 — stress
- `Stress/BoxRegion`: **non-vacuity of `DivergenceRegion`**: the unit box of any orthonormal basis,
  with face measures and normals `±eᵢ`, via Mathlib's divergence theorem on boxes.
- `Stress/Regions`: homothetic images `c + rP` of divergence regions; small boxes around every
  point; **balance of forces / moments on small boxes ⇒ `div σ + b = 0` and `σ = σᵀ`**,
  hypothesis-free.
- `Stress/Triangle`: surface integrals over flat triangles (affine parametrisation, Gram-determinant
  area); `h⁻² ∫_{x+hT} f dA → area(T) f(x)`.
- `Stress/Cauchy`: **Cauchy's theorem by the tetrahedron argument**. From force balance on Cauchy
  tetrahedra (`TetraBalance`, with genuine face integrals and `O(h³)` volume estimate) and
  continuity of `t`: the tetrahedron identity, **Cauchy's reciprocal theorem** `t(x,-n) = -t(x,n)`,
  and `t(x, n) = σ(x) n` with `σ` continuous. No hypothesis structure needed.
- `Stress/Balance`: divergence of vector and tensor fields; `DivergenceRegion` hypothesis
  structure (first entry in `GAPS.md`); `∫_∂P σn = ∫_P div σ`; localisation; **integral force
  balance ⇒ `div σ + b = 0`**; **moment balance ⇒ `σ` symmetric** (coordinate-free, any
  dimension).
- `Stress/Piola`: first and second Piola–Kirchhoff stresses, conversions, and
  `σ sym ⇔ S sym ⇔ PFᵀ sym`.
- `Stress/Criteria`: `J₂`, von Mises; principal stresses in 3D; `J₂` principal formula;
  `(√3/2) σ_T ≤ σ_vM ≤ σ_T`.

### Phase 2 — kinematics (in progress)
- `Kinematics/Compatibility`: full symmetry of `D³u`; `D²ε = sym D³u`; **Saint-Venant compatibility
  (necessity)** in coordinate-free form, any dimension.
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
- `Sobolev1D/Primitive`: `H¹(0,L)` modelled by primitives `u = ∫₀ˣ v`, `v ∈ L²((0,L])`: point
  evaluation `⟪χ_(0,x], v⟫`, Sobolev embedding `|u(x)| ≤ √L ‖u'‖`, Poincaré `∫u² ≤ L²‖u'‖²`,
  continuity, and a Fubini lemma `∫ f (P w) = ⟪∫_·ᴸ f, w⟫`.
- `Sobolev1D/BarWeak`: Lax–Milgram for `EA⟪v,w⟫ = ℓ(w)`; **weak forms of the fixed–free and
  fixed–fixed bar are well posed**, and classical `C²` solutions are the weak solutions (`P u' = u`).
- `Sobolev1D/BeamWeak`: `P` as a bounded operator on `L²`; bending moment of a cantilever
  `EI w'' = P(L − t) + ∫∫q`; **weak form of the Euler–Bernoulli cantilever is well posed**, and
  classical `C⁴` solutions are the weak solutions (`P² w'' = w`).
- `Beams/Wirtinger`: **Wirtinger's inequality** `(π/L)² ∫u² ≤ ∫u'²` (`u(0) = u(L) = 0`), proved
  with Picone's identity against `sin(k(x + δ))` and `δ → 0⁺` (no Fourier series);
  `(π/L)² ∫w'² ≤ ∫w''²`.
- `Beams/Rayleigh`: Rayleigh quotient of a pinned column; **`P_cr = π²EI/L²` is its minimum**,
  attained by `sin(πx/L)`.
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
