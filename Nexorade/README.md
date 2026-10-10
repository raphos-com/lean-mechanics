# Nexorade — a Lean formalization

Machine-checked formalization (Lean 4 + Mathlib, no axioms, no `sorry`) of

> L. Greco, A. Lebée, C. Douthe,
> **Investigation of the elastic behavior of reciprocal systems using homogenization techniques**,
> 2013.
> [ResearchGate](https://www.researchgate.net/publication/270451899_Investigation_of_the_elastic_behavior_of_reciprocal_systems_using_homogenization_techniques)

The paper homogenizes the square nexorade (reciprocal frame with spherical joints) as a
Kirchhoff–Love plate and finds a **degenerate** plate: only bi-axial bending stores energy. This
folder proves the paper's closed-form results from the statics of the two-beam unit cell. It builds
on the [`ContinuumMechanics`](../ContinuumMechanics) library (Kirchhoff–Love plates and their Navier
solutions).

Source used: the final version (Drive, 2013-09-18). The in-plane analysis comes from the authors'
earlier draft (`5.1`, May 2013); the final paper leaves membrane behaviour to future work.

## Correspondence with the paper

| Paper (final version) | Lean | Status |
|---|---|---|
| §2.2 Static homogenization: the plate energy is the minimum of the cell complementary energy (Hill–Mandel) | `Homogenized.lean`: `Cell.isLeast_outOfPlane` | proved for the nexorade |
| §3.1 Unit cell, `a = L sin φ`, `l = L (cos φ + sin φ)` (19) | `Parametric.lean`: `cellOf`, `area_cellOf`, `length_cellOf` | ✅ |
| §3.2 Only one admissible stress field: four-point bending | `OutOfPlane.lean`: `Cell.admissible_iff` | ✅ |
| (20) `M₁₂ = 0`, `M₁₁ = M₂₂` | `Cell.M11_eq_M22` (and `M₁₂ = 0` by construction) | ✅ |
| (22) Shear `r = M / (cos φ sin φ)` | `shear_cellOf` (`= 2M / sin 2φ`) | ✅ |
| (23) Moment `m = M L / cos φ` | `moment_cellOf` | ✅ |
| (24)–(27) Degenerate plate: `ΔM + p = 0`, energy only in the mean curvature, `K = d M` | `Plate.lean`: `legendre_le`, `legendre_eq`, `DegeneratePlate` | ✅ |
| (28)–(29) Compliance `d` and stiffness `D` | `Cell.compliance`, `Cell.energy_eq`, `compliance_cellOf`, `stiffness_cellOf` | ✅ |
| (31) Euler–Bernoulli members (`GSₛ → ∞`) | — | not yet (it is the `η = 0` case of `stiffness_cellOf`) |
| §4.1 `D → 0` as `a/l → 0` | `tendsto_stiffness_zero` | ✅ |
| (32)–(33) Moment minimal at `a/l = 1 − √2/2` (`φ = π/8`), `m_min = (2√2 − 2) m_max ≈ 0.828 m_max` | `normalized_moment_optimal`, `two_mul_cos_mul_le` | ✅ |
| §4.2 Stiffness optimum (`a/l → 0.5` for rigid shear, `→ 0.3966` for soft shear); 7% / 20% trade-off | — | not yet |
| §5.1 Navier solution (34)–(36) | `DegeneratePlate.navier`, `navier_kirchhoffLove` | ✅ |
| §5.2 Finite element comparison (ABAQUS) | — | out of scope (numerical) |
| Scale separation / convergence of the frame to the plate | — | assumed (see [`GAPS.md`](../GAPS.md)) |
| (draft) In-plane cell problem, `A₂₂₁₁ = 0`, `N₁₂ ≡ 0` | `InPlane.lean`, `Cell.isLeast_inPlane` | ✅ (beyond the final paper) |

## Points where the formalization differs from the text

* **Equivalent isotropic plate.** §3.3 says the static links (20) are those of an isotropic plate
  with Poisson ratio `ν = −1`. The formal result is `ν = +1`: with `M = D((1−ν)K + ν tr K I)`,
  only `ν = 1` gives `M₁₁ = M₂₂` and `M₁₂ = 0`, and an energy `½ D (tr K)²` of rank 1.
  See `DegeneratePlate.toPlate` and `moment_eq_momentX`.
* **Shear parameter.** In the `(L, φ)` form the stiffness is
  `D = EI cos φ / (2L ((1 − tan φ/3) + η/sin 2φ))` with `η = 4EI/(GSₛL²)`. Check this `η` against
  (28)–(30).
* **(draft) In-plane compliance.** The bending term of `A₁₁₁₁` is `a²b²(2a+b)/(12EI)`, not the
  draft's `a²b²(16a+b)/(24EI)`.

## Building

From the repository root:

```sh
lake build Nexorade
scripts/check_no_sorry_axiom.sh
```
