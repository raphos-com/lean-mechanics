# ContinuumMechanics — Architecture

Status: **draft for review** (Process step 1). No Lean code exists yet.

This document fixes the module layout, the core type choices, naming
conventions, and the "hypotheses as structures" discipline. It also records
the Mathlib survey this design rests on (§7), so that every choice below can be
traced to what Mathlib does or does not provide.

---

## 1. Toolchain

| Item | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (latest stable release; Mathlib `master` is on `v4.35.0-rc4`) |
| Mathlib | tag `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| doc-gen4 | the tag matching the Lean toolchain |

`lean-toolchain` and `lake-manifest.json` are committed. Bumps happen only in a
dedicated `chore: bump toolchain` commit that fixes every breakage; never mixed
with feature work.

## 2. Module layout

```
ContinuumMechanics.lean                -- root: imports every module below
ContinuumMechanics/
  Basic/
    Notation.lean                       -- scoped notation (ᵀ, :, ⊗, 𝕀, …)
    Hypotheses.lean                     -- re-exports all hypothesis structures (see §5)
  Tensor/                               -- Phase 1
    Second.lean                         -- Lin E, transpose, identity, basic API
    SymSkew.lean                        -- Sym/Skw, sym/skw parts, decomposition
    Spherical.lean                      -- spherical/deviatoric decomposition
    Contraction.lean                    -- A : B, Frobenius norm, `Frob E` synonym
    Invariants.lean                     -- I₁ I₂ I₃, Cayley–Hamilton (via Mathlib)
    Spectral.lean                       -- spectral decomposition of Sym
    Orthogonal.lean                     -- Orth = unitary (Lin E), Orth⁺ (rotations)
    Positive.lean                       -- Psym, real CFC instance, square root
    Polar.lean                          -- F = R U = V R, existence and uniqueness
    Fourth.lean                         -- Lin4 E, minor/major symmetries, 𝕀, 𝕀ˢʸᵐ, I⊗I
    Isotropic4.lean                     -- isotropic 4th-order tensors, λ I⊗I + 2μ 𝕀ˢʸᵐ (dim 3)
    Matrix.lean                         -- Fin 3 matrix bridge for examples/computation
  Kinematics/                           -- Phase 2
    Body.lean                           -- reference body, deformation, F, J
    Strain.lean                         -- C, B, Green–Lagrange, Almansi
    Infinitesimal.lean                  -- ε = sym ∇u, linearisation estimate
    Rigid.lean                          -- skew gradient ⇒ infinitesimal rigid displacement
    Observer.lean                       -- change of observer, objectivity
    Compatibility.lean                  -- Saint-Venant (hypothesis-based)
  Stress/                               -- Phase 3
    Cauchy.lean                         -- traction, Cauchy stress, Cauchy's theorem
    Balance.lean                        -- local balance laws, symmetry of σ
    Piola.lean                          -- P, S and conversions
    Criteria.lean                       -- principal stresses, von Mises, Tresca
  Constitutive/                         -- Phase 4
    Elastic.lean                        -- response functions, hyperelasticity
    FrameIndifference.lean              -- W(F) = Ŵ(C), symmetry groups, isotropy
    LinearIsotropic.lean                -- λ μ E ν K G conversions, positivity
    Hyperelastic/SVK.lean
    Hyperelastic/NeoHookean.lean
    Hyperelastic/MooneyRivlin.lean
    RivlinEricksen.lean                 -- stretch
  Elastostatics/                        -- Phase 5
    Energy.lean                         -- strain energy, Clapeyron
    Reciprocity.lean                    -- Betti
    Uniqueness.lean                     -- Kirchhoff uniqueness
    MinimumEnergy.lean                  -- minimum potential energy
    Weak.lean                           -- weak form, Lax–Milgram + Korn hypothesis
  Sobolev1D/                            -- Phase 6 infrastructure (upstream candidate)
    H1.lean                             -- H¹(0,L) as ℝ × L²
    H2.lean                             -- H²(0,L)
    Inequalities.lean                   -- Poincaré / Wirtinger on an interval
  Beams/                                -- Phase 6
    Interval.lean                       -- shared 1D calculus helpers
    Bar.lean
    EulerBernoulli/{Strong,Energy,Solutions,Uniqueness,Weak}.lean
    Timoshenko/{Strong,Energy,Solutions,Limit,Weak}.lean
    Buckling.lean
  Plates/                               -- Phase 7 (stretch)
  Examples/                             -- cross-module worked examples (steel bar, …)
scripts/
  check_no_sorry_axiom.sh               -- CI guard (see §8)
```

Every file targets ≤ ~500 lines; a file that grows past that is split along
the `-- section` boundaries it already has.

## 3. Core type choices

### 3.1 Ambient space

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
```

The space of *vectors* (translations of Euclidean point space). Points are
identified with vectors, i.e. we use `E` itself as the affine space — Gurtin
does the same after fixing an origin; this avoids `EuclideanSpace`/`AffineSpace`
plumbing for no mathematical gain in this library. `[Fact (finrank ℝ E = 3)]`
appears **only** where dimension matters (Cayley–Hamilton in invariant form,
`I₂`, isotropic fourth-order representation, cross products, rotations as
`det = 1` being the right notion, Rivlin–Ericksen). Everything else is stated in
any finite dimension, which is both more general and usually easier to prove.

Concrete instance for examples: `EuclideanSpace ℝ (Fin 3)`.

### 3.2 Second-order tensors

```lean
abbrev Lin (E) := E →L[ℝ] E
```

`abbrev`, not `def`: we want every Mathlib instance on `E →L[ℝ] E` to apply
unchanged — `Ring`, `Algebra ℝ`, `StarRing` (star = Hilbert adjoint),
`CStarRing`, the Loewner `PartialOrder`, `ContinuousLinearMap.det`, `IsPositive`,
`IsSymmetric`, the spectral theorem.

Physical names are thin wrappers or notation over Mathlib, never new
definitions:

| Textbook | Lean | Mathlib object |
|---|---|---|
| `Aᵀ` | scoped notation `Aᵀ` | `star A` = `ContinuousLinearMap.adjoint A` |
| `I` | `1 : Lin E` | `ContinuousLinearMap.id` |
| `AB` | `A * B` | composition |
| `tr A`, `det A` | `Lin.tr A`, `A.det` | `LinearMap.trace ℝ E A`, `ContinuousLinearMap.det` |
| `sym A`, `skw A` | `Lin.sym`, `Lin.skw` | `selfAdjointPart ℝ`, `skewAdjointPart ℝ` (`StarModule`) |
| `Sym`, `Skw` | `Sym E`, `Skw E` | `selfAdjoint (Lin E)`, `skewAdjoint (Lin E)` (as ℝ-submodules) |
| `Orth` | `Orth E` | `unitary (Lin E)` (star = adjoint, so unitary = orthogonal) |
| `Orth⁺` | `Rot E` | `{Q ∈ unitary (Lin E) | Q.det = 1}` as a `Subgroup` |
| `Psym` | `Psym E` | `{A | IsStrictlyPositive A}` w.r.t. the Loewner order |
| `a ⊗ b` | `dyad a b` | `innerSL ℝ b` smul-right `a`, i.e. `v ↦ ⟪b, v⟫ a` |

### 3.3 Double contraction and the Frobenius structure

`E →L[ℝ] E` already carries Mathlib's **operator** norm. Putting a Frobenius
`InnerProductSpace` instance on the same type would create an instance diamond.
Therefore:

* `Lin.dcontr : Lin E →ₗ[ℝ] Lin E →ₗ[ℝ] ℝ`, `A : B := tr (Aᵀ * B)`, with
  symmetry, positivity (`A : A ≥ 0`, `= 0 ↔ A = 0`), and orthonormal-basis
  formula `A : B = ∑ i, ⟪A eᵢ, B eᵢ⟫` (from `LinearMap.trace_eq_sum_inner`).
  This is enough for all pointwise algebra.
* `Frob E` — a type synonym (`def Frob (E) := Lin E`, in the style of
  `WithLp`) carrying `NormedAddCommGroup`/`InnerProductSpace ℝ` with
  `⟪A, B⟫ = A : B`, plus the `LinearEquiv`/`ContinuousLinearEquiv` to `Lin E`.
  Used only when a genuine Hilbert-space structure on tensors is needed
  (e.g. `L²` tensor fields in the weak formulation, norms of `ℂ`).

### 3.4 Fourth-order tensors

```lean
abbrev Lin4 (E) := Lin E →L[ℝ] Lin E
```

* minor symmetries: `HasMinorSymm ℂ : ∀ A, ℂ (A) = ℂ (sym A) ∧ IsSelfAdjoint (ℂ A)`
* major symmetry: `HasMajorSymm ℂ : ∀ A B, ℂ A : B = A : ℂ B`
* `𝕀 := 1`, `𝕀ˢʸᵐ := sym` (as an element of `Lin4 E`), `I ⊗ I : A ↦ (tr A) I`
* positive definiteness on `Sym E`.

Isotropic representation (`ℂ(QAQᵀ) = Q ℂ(A) Qᵀ ∀ Q ∈ Orth` ⇒ `ℂ = λ I⊗I + 2μ 𝕀ˢʸᵐ`
on symmetric arguments) is a dimension-3 theorem and lives in
`Isotropic4.lean`.

### 3.5 Square roots and polar decomposition: the real CFC gap

Mathlib provides `CFC.sqrt`, `CFC.abs` and the full continuous functional
calculus on `H →L[ℂ] H`, and on `Matrix n n ℝ` (Hermitian functional calculus),
but **not** a `ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint`
instance for real Hilbert spaces. It does provide

* `LinearMap.toMatrixOrthonormal : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜`, and
* `ContinuousFunctionalCalculus.transfer` (transport a CFC along a `≃⋆ₐ`).

Plan (`Tensor/Positive.lean`): for finite-dimensional real `E`, build the
`≃⋆ₐ[ℝ]` `Lin E ≃ Matrix (Fin (finrank ℝ E)) (Fin _) ℝ` from a chosen
orthonormal basis and transfer the matrix CFC. Then `U := CFC.sqrt (Fᵀ F)`,
`CFC.abs`, uniqueness of positive square roots, and the rest of the CFC API
come for free. Proof obligations that the instance is basis-independent are
avoided by `CFC`'s own uniqueness (`UniqueContinuousFunctionalCalculus`).
This instance is global (review decision) and a prime **upstream
candidate**; if Mathlib gains its own instance, ours is deleted.

Polar decomposition is then `R := F * U⁻¹`, with `R ∈ Orth`, `det R = 1` when
`det F > 0`, `V := R U Rᵀ`, and uniqueness from uniqueness of positive square
roots.

### 3.6 Fields and bodies

* Reference body: `Ω : Set E` with `IsOpen Ω` (plus `IsConnected Ω`,
  bounded, etc. only where used). Bundled in `structure Body (E)` only once
  boundary data is needed (Phase 3+).
* Deformation: `structure Deformation (Ω : Set E)` with `toFun : E → E`,
  `contDiffOn : ContDiffOn ℝ 1 toFun Ω` (higher regularity as extra
  hypotheses), `det_pos : ∀ x ∈ Ω, 0 < (fderiv ℝ toFun x).det`. Fields are
  total functions `E → E` restricted to `Ω`; because `Ω` is open, `fderiv`
  agrees with `fderivWithin` and we always use `fderiv`.
* Deformation gradient `F x := fderiv ℝ φ x : Lin E`; displacement
  `u := φ - id`, `∇u = F - 1`.
* Divergence of a tensor field `σ : E → Lin E` is defined coordinate-free via
  the trace: `⟪div σ x, a⟫ = tr (fderiv ℝ (fun y ↦ (σ y)ᵀ a) x)`, with a lemma
  giving the orthonormal-basis formula.

### 3.7 One-dimensional theories (Phase 6)

* Domain `Set.Icc 0 L` with `(hL : 0 < L)`; integrals are `∫ x in (0)..L`.
* **Smooth setting**: displacement fields are `w : ℝ → ℝ` with
  `ContDiff ℝ k w` (globally defined). This avoids `derivWithin` at the
  endpoints and lets us use `deriv`/`iteratedDeriv` and
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul` directly. Closed-form
  solutions are polynomials, so this costs nothing there. For theorems where
  a global extension is a genuine restriction we state the `ContDiffOn … (Icc 0 L)`
  version separately.
* **Point loads** are not smooth; the canonical point-load solutions are
  piecewise cubics. They are verified (a) piecewise against the homogeneous
  ODE, (b) via continuity of `w, w', w''` and the shear jump `= P` at the load
  point, and (c) in the weak form. The strong-form "uniqueness" theorem is
  stated for smooth loads.
* **Sobolev spaces on an interval** (Mathlib only has Bessel-potential
  Sobolev spaces on whole vector spaces via the Fourier transform). We build
  the minimal 1D pieces by the absolute-continuity characterisation:

  ```
  H¹(0,L) ≅ WithLp 2 (ℝ × L²(0,L)),   (c, g) ↦ (x ↦ c + ∫₀ˣ g)
  H²(0,L) ≅ WithLp 2 (ℝ × H¹(0,L))
  ```

  These are Hilbert spaces *by construction* (completeness inherited), the
  norm is equivalent to the textbook one (proved), and boundary conditions are
  kernels of continuous linear functionals, hence closed subspaces. The weak
  forms then go through Mathlib's `IsCoercive.continuousLinearEquivOfBilin`
  (Lax–Milgram) with coercivity from Poincaré-type inequalities proved by
  Cauchy–Schwarz. Flagged as an upstream candidate.

## 4. Naming conventions

* Follow Mathlib style: `UpperCamelCase` for types/structures/classes,
  `lowerCamelCase` for definitions, `snake_case` for theorems, with the
  Mathlib naming grammar (`mul_comm`, `det_pos_of_…`, `…_iff_…`).
* Namespace root `ContinuumMechanics`; sub-namespaces mirror folders
  (`ContinuumMechanics.Kinematics`, …). Operations on `Lin E` live in the
  `ContinuumMechanics.Lin` namespace so dot notation `A.sym`, `A.dev` works.
* Physical symbols go into **scoped** notation (`open scoped ContinuumMechanics`):
  `Aᵀ`, `A ⊡ B` for `A : B` (a bare `:` is not usable), `a ⊗ b`, `𝕀ˢʸᵐ`.
  Single-letter names (`F`, `C`, `σ`, `ℂ`) are variables, never global constants.
* Material parameters are fields of structures (`LameParameters` with
  `lam mu : ℝ`; `YoungPoisson` with `young poisson : ℝ`), with conversion
  functions and round-trip lemmas.
* Every public definition and every main theorem carries a docstring giving
  the textbook name and a reference in the form
  `[Gurtin, §6, Thm 2]`, `[Ciarlet I, Thm 3.2-1]`, `[Marsden–Hughes, Ch. 3]`,
  `[Timoshenko–Gere, §…]`, `[Reddy, §…]`. Bibliography entries live in
  `docs/references.bib` and are cited via `[Gurtin1981]`-style keys
  understood by doc-gen4.
* Lemma tags: `@[simp]` only on lemmas whose RHS is simpler in an obvious
  normal form (e.g. `sym_sym`, `tr_one`); `@[ext]` on structure ext lemmas.

## 5. Hypotheses as structures

**Rule:** no `axiom`, ever. When a result needs analysis Mathlib lacks, the
missing fact becomes a `structure` (a `Prop`-valued one whenever possible)
that theorems take as an **explicit** argument.

```lean
/-- The divergence theorem holds on `Ω` with outward normal `n` and surface
measure `σ` for all `C¹(Ω̄)` vector fields.  [Gurtin, §5]  See GAPS.md#divergence. -/
structure HasDivergenceTheorem (Ω : Set E) (μS : Measure E) (n : E → E) : Prop where
  integral_div : ∀ v : E → E, ContDiffOn ℝ 1 v (closure Ω) →
    ∫ x in Ω, div v x = ∫ x, ⟪v x, n x⟫_ℝ ∂μS
```

Conventions:

1. **Structures, not classes.** Passing them explicitly keeps every
   assumption visible in the theorem statement and prevents instance search
   from silently discharging them. (A `class` is used only for genuinely
   canonical structure, e.g. `Fact (finrank ℝ E = 3)`.)
2. **Weakest useful statement.** State exactly what the downstream proof
   consumes, not the textbook's strongest form.
3. **Non-vacuity witnesses.** For each hypothesis structure we try to prove
   at least one nontrivial instance. Example: `HasDivergenceTheorem` for
   rectangular boxes in `Fin 3 → ℝ` follows from Mathlib's
   `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Where no
   witness is available yet, `GAPS.md` says so explicitly. This guards against
   hypotheses that are accidentally inconsistent (which would make every
   theorem using them vacuous).
4. **Documentation.** Each structure has a `GAPS.md` entry: statement, where
   it is used, the textbook source, and what Mathlib would need to discharge
   it (e.g. "divergence theorem for bounded Lipschitz domains; needs surface
   measure on rectifiable boundaries").
5. All hypothesis structures are re-exported from `Basic/Hypotheses.lean` so
   the full list of assumptions is greppable in one place.

Planned hypothesis structures (initial list, see `ROADMAP.md`):
`HasDivergenceTheorem`, `KornInequality`, `SaintVenantCompatible`
(sufficiency on simply connected domains), `HasTraceOperator` (Phase 5 weak
form on 3D domains).

## 6. Proof-engineering policy

* `main` builds with **zero `sorry`, zero `axiom`, zero warnings**.
  Feature branches may contain `sorry`; each is listed in `TODO.md`
  (`file:line — plan`).
* Each milestone: definitions → API lemmas (simp/ext/algebraic) → main
  theorems → `example` blocks → commit. Examples use concrete numbers
  (e.g. steel: `E = 210 GPa`, `ν = 0.3`) and are checked by `norm_num`.
* "Stop and report" rule: if a proof takes far longer than expected, stop
  and report what was tried, the missing Mathlib lemma, and options (weaken,
  hypothesis structure, upstream).
* Lemmas general enough for Mathlib are tagged in a comment
  `-- upstream candidate` and collected in `UPSTREAM.md`.

## 7. Mathlib survey (at `v4.34.1`)

### Reused as is

| Need | Mathlib |
|---|---|
| Adjoint / transpose | `ContinuousLinearMap.adjoint`, `star` on `E →L[𝕜] E` (`Analysis/InnerProductSpace/Adjoint`) |
| Sym/skew decomposition | `selfAdjointPart`, `skewAdjointPart`, `StarModule.selfAdjointPart_add_skewAdjointPart` |
| Symmetric operators | `LinearMap.IsSymmetric`, `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` |
| Trace | `LinearMap.trace`, `LinearMap.trace_eq_sum_inner` (orthonormal basis) |
| Determinant | `LinearMap.det`, `ContinuousLinearMap.det`, `LinearMap.det_comp` |
| Cayley–Hamilton | `LinearMap.aeval_self_charpoly`; coefficients via `LinearMap.det_eq_sign_charpoly_coeff`, `trace_eq_neg_charpoly_coeff` |
| Spectral theorem | `LinearMap.IsSymmetric.eigenvectorBasis`, `.eigenvalues`, `hasEigenvector_eigenvectorBasis` |
| Positivity / order | `ContinuousLinearMap.IsPositive`, Loewner order, `IsStrictlyPositive` |
| Orthogonal group | `unitary (E →L[ℝ] E)`; `Matrix.orthogonalGroup`, `Matrix.specialOrthogonalGroup`, `Matrix.det_of_mem_unitary` |
| Matrix bridge | `LinearMap.toMatrixOrthonormal : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜`, `Matrix.toEuclideanCLM` |
| CFC transport | `ContinuousFunctionalCalculus.transfer`, `StarAlgHomClass.map_cfc`; matrix CFC in `Analysis/Matrix/HermitianFunctionalCalculus` |
| `CFC.sqrt`, `CFC.abs` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/{Rpow/Basic,Abs}` |
| Rayleigh quotient | `ContinuousLinearMap.rayleighQuotient`, `IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` / `…iInf…` |
| Derivatives | `fderiv`, `HasFDerivAt`, `ContDiff`, `IsOpen.is_const_of_fderiv_eq_zero`, `isLocallyConstant_of_fderiv_eq_zero` |
| Fundamental lemma of calculus of variations | `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` |
| 1D calculus | `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `integral_mul_deriv_eq_deriv_mul` (integration by parts) |
| Lax–Milgram | `IsCoercive`, `IsCoercive.continuousLinearEquivOfBilin` (`Analysis/InnerProductSpace/LaxMilgram`) |
| Divergence theorem | only on boxes: `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` |
| Parseval on the circle | `tsum_sq_fourierCoeff` (for Wirtinger's inequality → Euler buckling) |

### Gaps found (each becomes a GAPS.md entry, an in-library lemma, or both)

| Gap | Plan |
|---|---|
| No real CFC on `E →L[ℝ] E` | Transfer from matrices (§3.5). Upstream candidate. |
| No Frobenius / Hilbert–Schmidt inner product on operators | `dcontr` + `Frob E` synonym (§3.3). Upstream candidate. |
| No polar decomposition | Prove from CFC (Phase 1). Upstream candidate. |
| No derivative of `det` (Jacobi's formula) | Prove `HasFDerivAt det (A ↦ tr(adj F · A))` for invertible `F` as `det F · tr(F⁻¹ A)` (needed for `∂J/∂F`, neo-Hookean). Upstream candidate. |
| No `det Aᵀ = det A` for the Hilbert adjoint (did not find it under expected names) | Prove via `toMatrixOrthonormal`. |
| Divergence theorem only for boxes | `HasDivergenceTheorem` hypothesis, witnessed on boxes. |
| No Sobolev spaces on bounded domains / intervals | 1D: build `H¹`, `H²` on an interval (§3.7). 3D: hypothesis structures (`KornInequality`, `HasTraceOperator`). |
| No Korn, Poincaré, Wirtinger inequalities | Korn: hypothesis. Poincaré on interval: prove (Cauchy–Schwarz). Wirtinger (for buckling): prove via odd extension + Parseval. |
| No simply-connectedness tools for open subsets of `E` usable for Saint-Venant | `SaintVenantCompatible` hypothesis (stretch). |

## 8. CI

GitHub Actions on every push / PR:

1. `lake exe cache get && lake build` with `-DwarningAsError=true`.
2. `scripts/check_no_sorry_axiom.sh`: fails if any `.lean` file under
   `ContinuumMechanics/` contains `sorry` or an `axiom` declaration
   (grep on the source **and** a `#print axioms`-based check on the root
   module's main theorems, which must report only `propext`,
   `Classical.choice`, `Quot.sound`). Runs as a required check on `main`;
   feature branches run it as informational.
3. doc-gen4 build, published to GitHub Pages from `main`.
