# Elastic gridshells: a Lean formalization

Machine-checked results (Lean 4 + Mathlib, no axioms, no `sorry`) on the geometry behind

> C. Baek, A. O. Sageman-Furnas, M. K. Jawed, P. M. Reis, **Form finding in elastic gridshells**,
> PNAS 115(1), 75–80 (2018).

The paper shows that rod inextensibility, not elasticity, sets the zeroth-order shape of an
actuated gridshell: the rods trace a **Chebyshev net**. The classical geometry of Chebyshev nets
is formalized here.

✅ proved; 🟡 proved from a stated hypothesis.

| Claim | Lean (`Gridshells/Chebyshev.lean`) | Status |
|---|---|---|
| Angle equation of a Chebyshev net, `ω_uv = −K sin ω` | `IsChebyshevAngle` (general `K`); `Sphere.lean`: `SphericalNet.sine_gordon` derives `ω_uv = −sin ω` for nets of unit-speed curves on the unit sphere | ✅ on the sphere; general surfaces taken as a hypothesis (no surface theory in Mathlib) |
| Hazzidakis formula `∬ K sin ω = −(ω(a,b) − ω(a,0) − ω(0,b) + ω(0,0))` | `hazzidakis` | 🟡 |
| On the unit sphere, area of a net quadrilateral `= 2π − Σ angles` | `area_eq` (with `SphericalNet.isChebyshevAngle`) | ✅ |
| … hence `< 2π`: one Chebyshev quadrilateral covers less than a hemisphere | `area_lt_two_pi`; for actual spherical nets `SphericalNet.area_lt_two_pi` | ✅ |
| Shapes, rigidity scaling and experiments of Baek et al. | — | out of scope (numerical/experimental) |

## Building

```sh
(cd papers && lake build Gridshells)
scripts/check_no_sorry_axiom.sh
```
