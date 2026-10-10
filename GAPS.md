# Gaps: hypothesis structures and missing Mathlib infrastructure

Every hypothesis structure used by the library is listed here with its
statement, users, source, non-vacuity witness (if any), and what Mathlib would
need in order to discharge it. See ARCHITECTURE.md §5.

## In use

### `DivergenceRegion` (`ContinuumMechanics/Stress/Balance.lean`)

*Statement.* A measurable region `P` with compact closure, a surface measure `dA` on `∂P` and an
outer normal `n` such that
* `∫_P div v dV = ∫_∂P v · n dA` for every `C¹` vector field `v` (the divergence theorem), and
* `x ↦ σ(x) n(x)` is `dA`-integrable for every continuous tensor field `σ`.

*Used by.* `DivergenceRegion.integral_traction`, `local_equilibrium`,
`symmetric_of_moment_balance` (balance of linear and angular momentum ⇒ `div σ + b = 0` and
`σ = σᵀ`). These theorems also assume the family of parts contains arbitrarily small regions of
positive volume around every point of the body.

*Source.* [Gurtin1981], §4; [Ciarlet1988], §2.2.

*Mathlib would need.* The divergence theorem on bounded Lipschitz (or at least piecewise smooth)
domains, with the surface (Hausdorff) measure on the boundary. Mathlib currently has it only for
rectangular boxes (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`), stated on
`Fin (n+1) → ℝ` with face integrals rather than a surface measure.

*Non-vacuity witness.* `ContinuumMechanics.boxRegion` (`Stress/BoxRegion.lean`): in any
finite-dimensional `E` and for any orthonormal basis `e`, the unit box `{x | 0 < x · eᵢ < 1}` with
`dA` = the sum of the Lebesgue measures of the open faces and `n = ±eᵢ`, transporting Mathlib's box
theorem along the (volume-preserving) coordinate map. `DivergenceRegion.homothety` rescales any
region, and `smallBoxes`/`exists_smallBox` (`Stress/Regions.lean`) supply the family of small parts
required by the localisation theorems, so `local_equilibrium_of_boxes` and
`symmetric_of_moment_balance_of_boxes` hold with no hypothesis structure at all.

### `KornSetting` (`ContinuumMechanics/Elastostatics/Weak.lean`)

*Statement.* Hilbert spaces `V` (admissible displacements) and `H` (strain fields), a continuous
strain operator `ε : V → H`, a symmetric elasticity operator `ℂ` with `⟪ℂe, e⟫ ≥ c‖e‖²`, and
**Korn's inequality** `‖v‖ ≤ K‖ε(v)‖`.

*Used by.* `KornSetting.existsUnique_weak` (Lax–Milgram well-posedness of 3D linear
elastostatics), `energy_eq_add`, `isMinOn_energy`, `eq_of_energy_eq` (minimum potential energy).

*Source.* [Ciarlet1988], §6.3; [Brezis2011], §9.4.

*Mathlib would need.* `H¹(Ω; ℝ³)` on Lipschitz domains, Korn's inequality (via Nečas / Lions
lemma), the trace theorem `H¹(Ω) → L²(∂Ω)` (continuity of the surface-load functional).

*Non-vacuity witness.* `KornSetting.ofIdentity` (`ε = id`, `ℂ = k I`, `K = 1`), the abstract form
of the 1D bar of `Sobolev1D/BarWeak`, whose `H¹` model is constructed without hypotheses.

### Modelling assumption: homogenization of periodic frames as plates (Phase 8)

*Statement.* For a periodic beam frame of cell size `ε → 0` under slowly varying loads, the frame
response converges to that of the Kirchhoff–Love plate whose compliance is given by the static
(Hill–Mandel) cell problem.

*Used by.* Nothing in Lean: Phase 8 *defines* the equivalent plate by the cell problem and proves
the cell results; the convergence statement is the modelling hypothesis that gives them physical
meaning, as in [GrecoLebeeDouthe2013], which recalls it from [Caillerie1984] and [LebeeSab2013].

*Mathlib would need.* Two-scale convergence / Γ-convergence for discrete lattices, Korn-type
inequalities for frames.

## Planned

| Structure | Needed for | Mathlib would need | Witness plan |
|---|---|---|---|
| `SaintVenantCompatible` | Phase 2 stretch | Poincaré lemma on simply connected open sets | — |
