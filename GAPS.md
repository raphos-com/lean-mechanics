# Gaps: hypothesis structures and missing Mathlib infrastructure

Every hypothesis structure used by the library is listed here with its
statement, users, source, non-vacuity witness (if any), and what Mathlib would
need in order to discharge it. See ARCHITECTURE.md §5.

_No hypothesis structures yet._

## Planned (from the design survey, see ARCHITECTURE.md §7)

| Structure | Needed for | Mathlib would need | Witness plan |
|---|---|---|---|
| `HasDivergenceTheorem` | Phase 3 balance laws, Phase 5 | divergence theorem on bounded Lipschitz domains with surface measure | boxes, via `integral_divergence_of_hasFDerivAt_off_countable` |
| `KornInequality` | Phase 5 weak form | Sobolev spaces on bounded domains, Korn's inequality | — |
| `HasTraceOperator` | Phase 5 weak form | trace theorem `H¹(Ω) → L²(∂Ω)` | — |
| `SaintVenantCompatible` | Phase 2 stretch | Poincaré lemma on simply connected open sets | — |
