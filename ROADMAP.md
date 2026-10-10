# ContinuumMechanics — Roadmap

Status: **reviewed**. Progress: Phase 0 ✅; Phase 1 ✅ (1.1–1.12, plus Jacobi's formula);
Phase 2: 2.1–2.5 ✅ (2.6 open); Phase 3: 3.1, 3.3–3.5 ✅ (3.2 open); Phase 4: 4.1–4.5 ✅
(4.6–4.7 open); Phase 5: 5.1–5.3 ✅ (in `Elastostatics/Basic.lean`; 5.4–5.5 open);
Phase 6: 6.1–6.9 ✅ (6.10–6.13 open). Milestones are roughly one file each and map to
`ARCHITECTURE.md` §2. Each milestone ends with: definitions → API lemmas →
main theorems → `example` blocks → commit. Each phase ends with a
`CHANGELOG.md` entry and updates to `GAPS.md`, `TODO.md`, `UPSTREAM.md`.

Risk: 🟢 routine, 🟡 real work but clear path, 🔴 likely to hit a Mathlib gap
or need a hypothesis structure / scope decision.

Dimension: "any d" means stated for finite-dimensional `E`; "d = 3" means
`[Fact (finrank ℝ E = 3)]`.

---

## Phase 0 — Project setup

| # | Milestone | Content | Risk |
|---|---|---|---|
| 0.1 | Lake project | `lakefile.lean`, `lean-toolchain` (v4.34.1), Mathlib pinned at `v4.34.1`, root `ContinuumMechanics.lean` | 🟢 |
| 0.2 | CI | build with warnings-as-errors, `scripts/check_no_sorry_axiom.sh`, doc-gen4 → Pages | 🟢 |
| 0.3 | Tracking files | `GAPS.md`, `TODO.md`, `CHANGELOG.md`, `UPSTREAM.md`, `docs/references.bib` | 🟢 |
| 0.4 | `Basic/Notation.lean` | scoped notation `ᵀ`, `⊡`, `⊗`, `𝕀ˢʸᵐ` | 🟢 |

## Phase 1 — Tensor algebra (`Tensor/`)

| # | File | Content | Risk |
|---|---|---|---|
| 1.1 | `Second.lean` | `Lin E`, transpose = `star`, `(AB)ᵀ = BᵀAᵀ`, `tr`, `det`, `tr Aᵀ = tr A`, `det Aᵀ = det A`, dyads `a ⊗ b` and their algebra | 🟢 |
| 1.2 | `SymSkew.lean` | `Sym E`, `Skw E` as submodules; `sym`, `skw`; `A = sym A + skw A`; `Lin E = Sym ⊕ Skw` (`IsCompl`), uniqueness of the decomposition | 🟢 |
| 1.3 | `Contraction.lean` | `A ⊡ B = tr(AᵀB)`; symmetric, positive definite; basis formula; `Sym ⟂ Skw`; `Frob E` synonym with `InnerProductSpace ℝ`; `‖A‖_F² = A ⊡ A` | 🟡 |
| 1.4 | `Spherical.lean` | `sph A = (tr A / d) I`, `dev A`; `A = sph A + dev A`, `tr (dev A) = 0`, orthogonality | 🟢 |
| 1.5 | `Invariants.lean` (d = 3) | `I₁ = tr`, `I₂ = ½((tr A)² − tr A²)`, `I₃ = det`; `charpoly A = X³ − I₁X² + I₂X − I₃`; Cayley–Hamilton `A³ − I₁A² + I₂A − I₃I = 0` from `aeval_self_charpoly`; invariance under `QAQᵀ` | 🟡 |
| 1.6 | `Spectral.lean` | spectral decomposition `S = ∑ λᵢ eᵢ ⊗ eᵢ` from `eigenvectorBasis`; invariants in terms of eigenvalues (d = 3) | 🟡 |
| 1.7 | `Orthogonal.lean` | `Orth E := unitary (Lin E)`; `Q ∈ Orth ↔ ∀ u v, ⟪Qu,Qv⟫ = ⟪u,v⟫`; `det Q = ±1`; `Rot E` subgroup `det = 1`; skew ↔ infinitesimal rotation lemma used in Phase 2 | 🟡 |
| 1.8 | `Positive.lean` | real CFC on `Lin E` via `ContinuousFunctionalCalculus.transfer` from `Matrix`; `Psym`; `CFC.sqrt`; existence & uniqueness of positive square root; `FᵀF ∈ Psym` for invertible `F` | 🔴 (instance engineering) |
| 1.9 | `Polar.lean` | `F = RU = VR`, `R ∈ Orth`, `U, V ∈ Psym`; uniqueness; `R ∈ Rot` iff `det F > 0`; `V = RURᵀ` | 🟡 |
| 1.10 | `Fourth.lean` | `Lin4 E`; minor/major symmetry predicates; `𝕀`, `𝕀ˢʸᵐ`, `I ⊗ I`; composition and contraction lemmas; positive definiteness on `Sym` | 🟢 |
| 1.11 | `Isotropic4.lean` (d = 3) | isotropy `ℂ(QAQᵀ) = Qℂ(A)Qᵀ ∀Q ∈ Orth`; representation `ℂ|Sym = λ I⊗I + 2μ 𝕀ˢʸᵐ`; converse | 🔴 (classical proof uses rotations about axes; expect 300+ lines) |
| 1.12 | `Matrix.lean` | `Fin 3` bridge via `toMatrixOrthonormal`; `examples` computing invariants of concrete matrices | 🟢 |

Phase-1 exit: all Gurtin Ch. 1 tensor results used later are available, with
polar decomposition and the isotropic representation proved.

## Phase 2 — Kinematics (`Kinematics/`)

| # | File | Content | Risk |
|---|---|---|---|
| 2.1 | `Body.lean` | `Deformation Ω`; `F`, `J = det F > 0`; displacement `u`; composition / chain rule for `F` | 🟢 |
| 2.2 | `Strain.lean` | `C = FᵀF`, `B = FFᵀ`, `E_GL = ½(C − I)`, Almansi `e = ½(I − B⁻¹)`; `C, B ∈ Psym`; `C = U²`, `B = V²`; `E_GL = Fᵀ e F` | 🟢 |
| 2.3 | `Infinitesimal.lean` | `ε = sym ∇u`; `E_GL = ε + ½ ∇uᵀ∇u`; `‖E_GL − ε‖ ≤ ½‖∇u‖²` (exact bound, stronger than `O`) | 🟢 |
| 2.4 | `Rigid.lean` | `∇u` skew on connected open `Ω` ⇒ `u(x) = a + W x` with `W` skew constant (via the classical identity `∂ₖ∂ⱼuᵢ = 0` and `IsOpen.is_const_of_fderiv_eq_zero`); needs `C²` | 🟡 |
| 2.5 | `Observer.lean` | change of observer `x* = c(t) + Q(t)x`; objective scalars/vectors/tensors; `F* = QF`, `C* = C`, `B* = QBQᵀ` | 🟢 |
| 2.6 | `Compatibility.lean` (stretch) | necessity of Saint-Venant (`curl curl ε = 0`) proved; sufficiency under `SaintVenantCompatible` hypothesis | 🔴 |

## Phase 3 — Stress and balance laws (`Stress/`)

| # | File | Content | Risk |
|---|---|---|---|
| 3.1 | `Balance.lean` part A | `div` of tensor fields; `HasDivergenceTheorem` structure; witness on boxes from Mathlib | 🟡 |
| 3.2 | `Cauchy.lean` | traction `t(x, n)`; Cauchy's theorem (existence & linearity in `n`) by the tetrahedron argument, proved: each face of a tetrahedron is a flat triangle, so face integrals are ordinary 2D integrals via an affine parametrisation (no general surface measure needed). Physical hypothesis = force balance on every small tetrahedron + continuity of `t` | 🟡 |
| 3.3 | `Balance.lean` part B | integral ⇒ local balance `div σ + b = ρa` (localisation via `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`); angular momentum ⇒ `σ` symmetric | 🟡 |
| 3.4 | `Piola.lean` | `P = J σ F⁻ᵀ`, `S = F⁻¹P`; inverse conversions; `σ` sym ⇔ `S` sym ⇔ `PFᵀ` sym | 🟢 |
| 3.5 | `Criteria.lean` | principal stresses (spectral), stress invariants, `J₂`, von Mises `σ_vM = √(3 J₂)`, Tresca; invariance and basic inequalities (e.g. Tresca ≤ von Mises ≤ (2/√3) Tresca) | 🟡 |

## Phase 4 — Constitutive theory (`Constitutive/`)

| # | File | Content | Risk |
|---|---|---|---|
| 4.1 | `Elastic.lean` | response function `σ̂ : Lin⁺ E → Sym E`; hyperelastic `P = DW(F)`; Jacobi formula `D det(F)[A] = det F tr(F⁻¹A)` (upstream candidate) | 🟡 |
| 4.2 | `FrameIndifference.lean` | `W(QF) = W(F) ∀Q ∈ Rot` ⇔ `W(F) = Ŵ(C)` (via polar decomposition); symmetry groups; isotropy | 🟡 |
| 4.3 | `LinearIsotropic.lean` | `σ = λ tr(ε) I + 2μ ε`; conversions (λ,μ) ↔ (E,ν) ↔ (K,G) with round-trip lemmas; **`ℂ` positive definite on Sym ⇔ `μ > 0 ∧ 3λ + 2μ > 0`** ⇔ `G > 0 ∧ K > 0` ⇔ `E > 0 ∧ −1 < ν < ½` | 🟢 |
| 4.4 | `Hyperelastic/SVK.lean` | `W = λ/2 (tr E)² + μ tr E²`, `S = λ tr(E) I + 2μE` derived from `DW` | 🟡 |
| 4.5 | `Hyperelastic/NeoHookean.lean` | compressible neo-Hookean; stress formula derived; linearisation at `F = I` recovers `ℂ` | 🟡 |
| 4.6 | `Hyperelastic/MooneyRivlin.lean` | same programme | 🟡 |
| 4.7 | `RivlinEricksen.lean` (stretch, d = 3) | isotropic `G : Sym → Sym` ⇒ `G(A) = φ₀I + φ₁A + φ₂A²` | 🔴 |

## Phase 5 — Linear elastostatics (`Elastostatics/`)

Smooth setting on a body with `HasDivergenceTheorem`.

| # | File | Content | Risk |
|---|---|---|---|
| 5.1 | `Energy.lean` | strain energy `U = ½∫ ε ⊡ ℂε`; Clapeyron `2U = ∫ b·u + ∫ t·u` | 🟢 |
| 5.2 | `Reciprocity.lean` | Betti reciprocal theorem | 🟢 |
| 5.3 | `Uniqueness.lean` | Kirchhoff uniqueness for the mixed problem (up to rigid motions in pure traction); uses 2.4 and 4.3 | 🟡 |
| 5.4 | `MinimumEnergy.lean` | minimum total potential energy (smooth fields) | 🟡 |
| 5.5 | `Weak.lean` | abstract weak formulation on a Hilbert space `V` with `KornInequality` + `HasTraceOperator` hypotheses → existence & uniqueness via `IsCoercive.continuousLinearEquivOfBilin` | 🔴 (needs `V` as a hypothesis-level object; scope to be fixed when we get there) |

## Phase 6 — 1D structural theories (`Sobolev1D/`, `Beams/`) — fully rigorous

No hypothesis structures allowed in this phase.

| # | File | Content | Risk |
|---|---|---|---|
| 6.1 | `Beams/Interval.lean` | integration by parts twice, polynomial integrals on `[0,L]`, "4th derivative zero ⇒ cubic" | 🟢 |
| 6.2 | `Beams/Bar.lean` | `(EA u')' + f = 0`; energy; fixed–free and fixed–fixed solutions under end load / uniform load / linear load; uniqueness | 🟢 |
| 6.3 | `EulerBernoulli/Strong.lean` | `(EI w'')'' = q`; BCs (clamped, pinned, free) as predicates | 🟢 |
| 6.4 | `EulerBernoulli/Energy.lean` | `Π(w) = ½∫EI w''² − ∫ q w`; strong form ⇔ stationarity for smooth `w` with admissible variations (fundamental lemma) | 🟡 |
| 6.5 | `EulerBernoulli/Solutions.lean` | simply supported & cantilever, uniform & point loads: closed forms (e.g. `w = q x (L³ − 2Lx² + x³)/(24EI)`, `δ_max = 5qL⁴/384EI`) satisfy ODE + BCs; point loads via piecewise cubics + jump conditions | 🟢 |
| 6.6 | `EulerBernoulli/Uniqueness.lean` | uniqueness for the four canonical BC sets (energy argument) | 🟢 |
| 6.7 | `Timoshenko/Strong.lean`, `Energy.lean` | `(EIθ')' + κGA(w' − θ) = 0`, `(κGA(w' − θ))' + q = 0`; energy; strong ⇔ stationary | 🟡 |
| 6.8 | `Timoshenko/Solutions.lean` | closed forms for the same canonical cases (EB + shear term, e.g. `+ q x(L−x)/(2κGA)`) | 🟢 |
| 6.9 | `Timoshenko/Limit.lean` | **convergence to Euler–Bernoulli as `κGA → ∞`**: canonical cases (uniform convergence on `[0,L]` with explicit `O(1/κGA)` rate); then general smooth loads via the energy estimate `‖w_T − w_EB‖ ≤ C/κGA` | 🟡 (general case 🔴) |
| 6.10 | `Sobolev1D/H1.lean` | `H¹(0,L) := WithLp 2 (ℝ × L²)` with realisation map; continuity of point evaluation; norm equivalence; `H¹₀` | 🔴 (new infrastructure, upstream candidate) |
| 6.11 | `Sobolev1D/H2.lean`, `Inequalities.lean` | `H²(0,L)`; Poincaré inequalities on an interval; boundary-condition subspaces | 🔴 |
| 6.12 | `EulerBernoulli/Weak.lean`, `Timoshenko/Weak.lean`, bar | weak forms; coercivity; well-posedness via Lax–Milgram; weak solution = classical solution when the latter exists | 🟡 |
| 6.13 | `Buckling.lean` | pinned–pinned: `EI w'''' + P w'' = 0`; nontrivial solutions iff `P = n²π²EI/L²`; `P_cr = π²EI/L²` is the smallest; Rayleigh quotient `P_cr = inf ∫EI w''² / ∫ w'²`, via Wirtinger's inequality (odd extension + Parseval, `tsum_sq_fourierCoeff`) | 🔴 (Wirtinger) |

Phase-6 examples: a concrete steel I-beam, all canonical deflections
evaluated with `norm_num`.

## Phase 7 — Plates (stretch, `Plates/`)

| # | File | Content | Risk |
|---|---|---|---|
| 7.1 | `KirchhoffLove.lean` | `D Δ²w = q`; energy; strong ⇔ stationary on a rectangle (boxes allow Mathlib's divergence theorem) | 🟡 |
| 7.2 | `Navier.lean` | simply supported rectangle: single-mode Navier solutions verified | 🟢 |
| 7.3 | `MindlinReissner.lean` | equations and energy; the analogue of the Timoshenko → EB limit for single-mode solutions | 🟡 |

---

## Ordering and review points

1. Phase 0 + Phase 1 → **review** (the tensor API shapes everything else).
2. Phase 6 depends on nothing beyond Phase 0 and runs **in parallel** with
   Phases 1–5 (decided in review).
3. Phases 2 → 3 → 4 → 5 are sequential.
4. Stretch items (2.6, 4.7, 7.x) are attempted only after their phase's core
   is on `main`.

## Review decisions

1. **Real CFC instance** (1.8): defined library-wide as a global instance
   `ContinuousFunctionalCalculus ℝ (Lin E) IsSelfAdjoint` for finite-dimensional
   `E`; to be replaced if Mathlib gains its own.
2. **Beam ends** (§3.7 of ARCHITECTURE): smooth-setting theorems take
   `w : ℝ → ℝ` defined on all of ℝ (only values on `[0, L]` matter). Point
   loads use smooth pieces glued with `w, w', w''` continuous and a shear jump
   of `P`.
3. **Phase 6** runs in parallel with Phases 1–5.
4. **Cauchy's theorem** is proved (not assumed), integrating over the flat
   faces of a tetrahedron.
