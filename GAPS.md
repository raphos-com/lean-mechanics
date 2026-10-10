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

*Non-vacuity witness.* Planned: boxes in `EuclideanSpace ℝ (Fin 3)` with the sum of the face
measures as `dA`, transporting Mathlib's box theorem along
`EuclideanSpace.volume_preserving_measurableEquiv`. Not yet done.

## Planned

| Structure | Needed for | Mathlib would need | Witness plan |
|---|---|---|---|
| `KornInequality` | Phase 5 weak form | Sobolev spaces on bounded domains, Korn's inequality | — |
| `HasTraceOperator` | Phase 5 weak form | trace theorem `H¹(Ω) → L²(∂Ω)` | — |
| `SaintVenantCompatible` | Phase 2 stretch | Poincaré lemma on simply connected open sets | — |
