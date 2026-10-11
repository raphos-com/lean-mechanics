# Roadmap

The repository contains two libraries built on Mathlib (Lean `v4.34.1`):

* **`ContinuumMechanics`**: tensor algebra, kinematics, stress, constitutive theory, linear
  elastostatics, beams and plates;
* **`DiscreteMechanics`**: pin-jointed and periodic frames, Maxwell–Calladine counting, Bloch
  analysis and long-wave limits.

Formalizations of papers are a separate Lake project in [`papers/`](../papers), each with its own
README; they are not tracked here.

Each milestone ends with: definitions → API lemmas → main theorems → `example` blocks → commit, a
[`CHANGELOG.md`](CHANGELOG.md) entry and updates to [`GAPS.md`](GAPS.md), [`TODO.md`](TODO.md),
[`UPSTREAM.md`](UPSTREAM.md).

Status: ✅ done; 🟡 partly done (what is open is stated); ⬜ planned.

---

## ContinuumMechanics

### Tensor algebra (`Tensor/`)

| File | Content | Status |
|---|---|---|
| `Second.lean` | `Lin E`, transpose, trace, determinant, dyads | ✅ |
| `SymSkew.lean` | `Sym E ⊕ Skw E` | ✅ |
| `Contraction.lean` | `A ⊡ B = tr(AᵀB)`, Frobenius inner product (`Frob E`) | ✅ |
| `Spherical.lean` | spherical/deviatoric decomposition | ✅ |
| `Invariants.lean` | principal invariants, Cayley–Hamilton (d = 3) | ✅ |
| `Spectral.lean` | spectral decomposition of symmetric tensors | ✅ |
| `Orthogonal.lean` | orthogonal tensors, rotations | ✅ |
| `Positive.lean` | real continuous functional calculus on `Lin E`, square roots | ✅ |
| `Polar.lean` | polar decomposition `F = RU = VR` | ✅ |
| `DetDeriv.lean` | Jacobi's formula | ✅ |
| `Fourth.lean` | fourth-order tensors, symmetries | ✅ |
| `Isotropic4.lean` | isotropic fourth-order tensors `λ I⊗I + 2μ 𝕀ˢʸᵐ` | ✅ |
| `Matrix.lean` | `Fin 3` matrix bridge | ✅ |

### Kinematics (`Kinematics/`)

| File | Content | Status |
|---|---|---|
| `Body.lean`, `Strain.lean` | deformations, `F`, `J`, `C`, `B`, Green–Lagrange, Almansi | ✅ |
| `Infinitesimal.lean` | `ε = sym ∇u`, linearisation estimate | ✅ |
| `Rigid.lean` | skew gradient ⇒ infinitesimal rigid displacement | ✅ |
| `Observer.lean` | change of observer, objectivity | ✅ |
| `Compatibility.lean` | Saint-Venant compatibility | 🟡 necessity only; sufficiency needs a Poincaré lemma (`GAPS.md`) |

### Stress and balance laws (`Stress/`)

| File | Content | Status |
|---|---|---|
| `Cauchy.lean`, `Triangle.lean` | Cauchy's theorem by the tetrahedron argument | ✅ |
| `Balance.lean`, `BoxRegion.lean`, `Regions.lean` | local balance laws, symmetry of `σ`; divergence theorem as a hypothesis, witnessed on boxes | ✅ |
| `Piola.lean` | Piola–Kirchhoff stresses | ✅ |
| `Criteria.lean` | invariants, von Mises, Tresca | ✅ |

### Constitutive theory (`Constitutive/`)

| File | Content | Status |
|---|---|---|
| `Hyperelastic.lean` | hyperelasticity, frame indifference | ✅ |
| `Hyperelastic/SVK.lean`, `NeoHookean.lean`, `MooneyRivlin.lean` | classical hyperelastic materials | ✅ |
| `LinearIsotropic.lean` | Lamé/Young/bulk conversions, positivity | ✅ |
| `RivlinEricksen.lean` | representation of isotropic tensor functions | ✅ |

### Linear elastostatics (`Elastostatics/`)

| File | Content | Status |
|---|---|---|
| `Basic.lean` | work, Clapeyron, Betti, Kirchhoff uniqueness | ✅ |
| `MinimumEnergy.lean` | minimum potential energy | ✅ |
| `Weak.lean` | Lax–Milgram well-posedness | 🟡 under the `KornSetting` hypothesis (`GAPS.md`) |
| `Korn.lean` | Korn's first inequality for compactly supported `C²` fields | ✅ |

### Beams and 1D Sobolev spaces (`Beams/`, `Sobolev1D/`)

| File | Content | Status |
|---|---|---|
| `Interval.lean`, `Poly.lean` | calculus on an interval, polynomial deflections | ✅ |
| `Bar.lean` | axial bar | ✅ |
| `EulerBernoulli/` | equation, boundary conditions, uniqueness, energy, closed-form solutions | ✅ |
| `Timoshenko/` | equations, uniqueness, Euler–Bernoulli limit | ✅ |
| `Buckling.lean`, `Wirtinger.lean`, `Rayleigh.lean` | Euler buckling, Wirtinger's inequality, Rayleigh quotient | ✅ |
| `Sobolev1D/` | `L²` primitives, weak bar, weak Euler–Bernoulli cantilever | 🟡 other beam boundary conditions and Timoshenko weak forms open |

### Plates (`Plates/`)

| File | Content | Status |
|---|---|---|
| `KirchhoffLove.lean` | plate equation, moments, simply supported edges | 🟡 energy and strong ⇔ stationary open |
| `Navier.lean` | single-mode Navier solutions | ✅ |
| `MindlinReissner.lean` | equations, Navier solution, Kirchhoff limit | 🟡 energy open |

### Planned

| Item | Content | Status |
|---|---|---|
| Plate energies | Kirchhoff–Love and Mindlin–Reissner energies; strong ⇔ stationary | ⬜ |
| `H¹₀(Ω; ℝⁿ)` | Sobolev space on open sets; Korn's inequality by density | ⬜ |
| Saint-Venant sufficiency | compatible strains are symmetric gradients on simply connected domains | ⬜ |

## DiscreteMechanics

| File | Content | Status |
|---|---|---|
| `Truss.lean` | pin-jointed frames, compatibility/equilibrium matrices, virtual work, Maxwell–Calladine index theorem, rigid motions | ✅ |
| `Periodic.lean` | periodic frames, Bloch compatibility matrix, Bloch reduction, Maxwell–Calladine per wave vector, Maxwell lattices | ✅ |
| `LongWave.lean` | long-wave expansion of the discrete Laplacian; long-wave limit of Bloch solutions through an adjugate | ✅ |
| periodic beam frames | beam frames with rigid or pinned joints, their Bloch problem, convergence to an equivalent plate | ⬜ |

## Review decisions

1. **Real CFC instance**: defined library-wide as a global instance
   `ContinuousFunctionalCalculus ℝ (Lin E) IsSelfAdjoint` for finite-dimensional `E`; to be
   replaced if Mathlib gains its own.
2. **Beam ends**: smooth-setting theorems take `w : ℝ → ℝ` defined on all of `ℝ` (only values on
   `[0, L]` matter). Point loads use smooth pieces glued with `w, w', w''` continuous and a shear
   jump of `P`.
3. **Cauchy's theorem** is proved (not assumed), integrating over the flat faces of a
   tetrahedron.
4. **Papers** are a separate Lake project depending on both libraries, so that the libraries do
   not depend on, or cite, any particular paper.
