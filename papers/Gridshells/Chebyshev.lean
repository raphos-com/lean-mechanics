import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Chebyshev nets: the Hazzidakis formula

An elastic gridshell is made of inextensible rods crossing at pinned joints; its rods trace a
**Chebyshev net** on the deformed surface: the two families of coordinate curves `u ↦ r(u, v)`,
`v ↦ r(u, v)` are parametrized by arc length, and the shape is governed by the angle `ω(u, v)`
between them ([Baek2018], following Chebyshev 1878). On a surface of Gaussian curvature `K` the
angle satisfies the **Chebyshev-net (sine-Gordon) equation**

`∂²ω/∂u∂v = -K sin ω`

(Servant; the Gauss equation for a net with unit metric coefficients), which we take as the
definition of a Chebyshev net in terms of its angle (`IsChebyshevAngle`). The area element is
`sin ω du dv`.

**Hazzidakis formula.** Integrating the equation over a net quadrilateral `[0, a] × [0, b]`:

`∬ K sin ω du dv = -(ω(a, b) - ω(a, 0) - ω(0, b) + ω(0, 0))` (`hazzidakis`).

The interior angles of the quadrilateral are `ω(0,0)`, `π - ω(a,0)`, `ω(a,b)`, `π - ω(0,b)`, so on
the unit sphere (`K = 1`) its **area is `2π` minus the sum of its angles** (`area_eq`), hence
**less than `2π`** as long as the net does not degenerate (`area_lt_two_pi`): a single Chebyshev
quadrilateral covers less than a hemisphere. This is the geometric obstruction behind the
form-finding difficulty of hemispherical elastic gridshells discussed in [Baek2018].

## References

* [Baek2018] C. Baek, A. O. Sageman-Furnas, M. K. Jawed, P. M. Reis, *Form finding in elastic
  gridshells*, PNAS 115(1), 75–80 (2018).
* [Hazzidakis1880] J. N. Hazzidakis, *Über einige Eigenschaften der Flächen mit konstantem
  Krümmungsmaß*, J. Reine Angew. Math. 88 (1880).
* [Ghys2011] É. Ghys, *Sur la coupe des vêtements: variation autour d'un thème de Tchebychev*,
  Enseign. Math. (2011).
-/

open Real intervalIntegral

noncomputable section

namespace ContinuumMechanics.Gridshells

/-- The angle `ω` of a Chebyshev net on a surface of Gaussian curvature `K`, with its partial
derivatives `ω_v` and `ω_uv`: `ω_uv = -K sin ω`. -/
structure IsChebyshevAngle (K ω ωv ωuv : ℝ → ℝ → ℝ) : Prop where
  hasDerivAt_v : ∀ u v, HasDerivAt (ω u) (ωv u v) v
  hasDerivAt_u : ∀ u v, HasDerivAt (fun u => ωv u v) (ωuv u v) u
  continuous_ωv : ∀ u, Continuous (ωv u)
  continuous_ωuv : ∀ v, Continuous (fun u => ωuv u v)
  sine_gordon : ∀ u v, ωuv u v = -(K u v * sin (ω u v))

variable {K ω ωv ωuv : ℝ → ℝ → ℝ}

/-- **Hazzidakis formula**:
`∬_{[0,a]×[0,b]} K sin ω du dv = -(ω(a,b) - ω(a,0) - ω(0,b) + ω(0,0))`. -/
theorem hazzidakis (h : IsChebyshevAngle K ω ωv ωuv) (a b : ℝ) :
    ∫ v in (0 : ℝ)..b, ∫ u in (0 : ℝ)..a, K u v * sin (ω u v) =
      -(ω a b - ω a 0 - ω 0 b + ω 0 0) := by
  -- inner integral: `∫ u, ω_uv = ω_v(a, v) - ω_v(0, v)`
  have inner : ∀ v, ∫ u in (0 : ℝ)..a, K u v * sin (ω u v) = -(ωv a v - ωv 0 v) := fun v => by
    have hint : IntervalIntegrable (fun u => ωuv u v) MeasureTheory.volume 0 a :=
      (h.continuous_ωuv v).intervalIntegrable _ _
    rw [← integral_eq_sub_of_hasDerivAt (fun u _ => h.hasDerivAt_u u v) hint,
      ← intervalIntegral.integral_neg]
    exact integral_congr fun u _ => by simp [h.sine_gordon u v]
  simp_rw [inner]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_sub
      ((h.continuous_ωv a).intervalIntegrable _ _) ((h.continuous_ωv 0).intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt (fun v _ => h.hasDerivAt_v a v)
      ((h.continuous_ωv a).intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt (fun v _ => h.hasDerivAt_v 0 v)
      ((h.continuous_ωv 0).intervalIntegrable _ _)]
  ring

/-- The area `∬ sin ω du dv` of the net quadrilateral `[0, a] × [0, b]`. -/
def area (ω : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := ∫ v in (0 : ℝ)..b, ∫ u in (0 : ℝ)..a, sin (ω u v)

/-- The sum of the interior angles `ω(0,0) + (π - ω(a,0)) + ω(a,b) + (π - ω(0,b))`. -/
def angleSum (ω : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := ω 0 0 + (π - ω a 0) + ω a b + (π - ω 0 b)

/-- **On the unit sphere, the area of a Chebyshev quadrilateral is `2π` minus the sum of its
angles.** -/
theorem area_eq (h : IsChebyshevAngle (fun _ _ => 1) ω ωv ωuv) (a b : ℝ) :
    area ω a b = 2 * π - angleSum ω a b := by
  have := hazzidakis h a b
  simp only [one_mul] at this
  rw [area, this, angleSum]
  ring

/-- **A Chebyshev quadrilateral on the unit sphere has area less than `2π`** (a hemisphere) when
its corner angles lie in `(0, π)`. -/
theorem area_lt_two_pi (h : IsChebyshevAngle (fun _ _ => 1) ω ωv ωuv) (a b : ℝ)
    (h00 : 0 < ω 0 0) (ha0 : ω a 0 < π) (hab : 0 < ω a b) (h0b : ω 0 b < π) :
    area ω a b < 2 * π := by
  rw [area_eq h, angleSum]
  linarith

end ContinuumMechanics.Gridshells
