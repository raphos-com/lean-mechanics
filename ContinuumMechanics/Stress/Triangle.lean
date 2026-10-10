import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals over flat triangles

The flat triangle with vertex `p` and edge vectors `a`, `c` is parametrised over the unit square by
`(u, v) ↦ p + u a + (1 - u) v c`, whose area element is `(1 - u) |a × c|`. Coordinate-free,
`|a × c| = √(‖a‖²‖c‖² - (a · c)²)` (the Gram determinant). This gives the surface integral

`∫_T f dA = |a × c| ∫_{[0,1]²} (1 - u) f(p + u a + (1 - u) v c) du dv`

used in the tetrahedron argument for Cauchy's theorem ([Gurtin1981], §14).

## Main results

* `gramArea_smul`: `|ha × hc| = h² |a × c|`.
* `tendsto_triangleIntegral`: for continuous `f`, on the triangle `x + h T`,
  `h⁻² ∫_{x + hT} f dA → area(T) f(x)` as `h → 0⁺`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit square `[0,1]²`, the parameter domain of a triangle. -/
def unitSquare : Set (ℝ × ℝ) := Icc 0 1

theorem isCompact_unitSquare : IsCompact unitSquare := isCompact_Icc

/-- `∫_{[0,1]²} (1 - u) du dv = 1/2`. -/
theorem integral_unitSquare_one_sub : ∫ q in unitSquare, (1 - q.1) = (2⁻¹ : ℝ) := by
  have e : unitSquare = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    rw [unitSquare, Icc_prod_Icc]; rfl
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun u : ℝ => 1 - u) (fun _ : ℝ => (1 : ℝ)) (Icc 0 1) (Icc 0 1)
  simp only [mul_one] at h
  rw [e, Measure.volume_eq_prod, h, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_sub (by simp) intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  norm_num

/-- Twice the area of the triangle spanned by `a` and `c`: `|a × c| = √(‖a‖²‖c‖² - (a · c)²)`. -/
noncomputable def gramArea (a c : E) : ℝ := √(‖a‖ ^ 2 * ‖c‖ ^ 2 - ⟪a, c⟫_ℝ ^ 2)

theorem gramArea_smul {h : ℝ} (hh : 0 ≤ h) (a c : E) :
    gramArea (h • a) (h • c) = h ^ 2 * gramArea a c := by
  have e : ‖h • a‖ ^ 2 * ‖h • c‖ ^ 2 - ⟪h • a, h • c⟫_ℝ ^ 2 =
      (h ^ 2) ^ 2 * (‖a‖ ^ 2 * ‖c‖ ^ 2 - ⟪a, c⟫_ℝ ^ 2) := by
    rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs,
      abs_of_nonneg hh]
    ring
  rw [gramArea, gramArea, e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

variable [FiniteDimensional ℝ E]

/-- The **surface integral over a flat triangle** with vertex `p` and edges `a`, `c`:
`∫_T f dA = |a × c| ∫_{[0,1]²} (1 - u) f(p + u a + (1 - u) v c) du dv`. [Gurtin1981], §14. -/
noncomputable def triangleIntegral (f : E → E) (p a c : E) : E :=
  gramArea a c • ∫ q in unitSquare, (1 - q.1) • f (p + q.1 • a + ((1 - q.1) * q.2) • c)

/-- **Shrinking triangles**: `h⁻² ∫_{x + hT} f dA → ½ |a × c| f(x)` as `h → 0⁺`. -/
theorem tendsto_triangleIntegral {f : E → E} (hf : Continuous f) (x p a c : E) :
    Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • triangleIntegral f (x + h • p) (h • a) (h • c))
      (𝓝[>] 0) (𝓝 ((2⁻¹ * gramArea a c) • f x)) := by
  let F : ℝ → ℝ × ℝ → E := fun h q =>
    (1 - q.1) • f (x + h • (p + q.1 • a + ((1 - q.1) * q.2) • c))
  have hF : Continuous F.uncurry := by fun_prop
  have hI := (continuous_parametric_integral_of_continuous (μ := volume) hF
    isCompact_unitSquare).tendsto 0
  have h0 : ∫ q in unitSquare, F 0 q = (2⁻¹ : ℝ) • f x := by
    simp only [F, zero_smul, add_zero]
    rw [integral_smul_const, integral_unitSquare_one_sub]
  rw [h0] at hI
  have hI' := (hI.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).const_smul (gramArea a c)
  rw [smul_smul, mul_comm] at hI'
  refine hI'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [triangleIntegral, gramArea_smul (le_of_lt hh), F, smul_smul]
  have hh2 : (h ^ 2)⁻¹ * (h ^ 2 * gramArea a c) = gramArea a c := by
    field_simp [(ne_of_gt hh : h ≠ 0)]
  rw [hh2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun q _ => ?_
  congr 2
  module

/-- `tendsto_triangleIntegral` for a triangle with a vertex at `x`. -/
theorem tendsto_triangleIntegral_vertex {f : E → E} (hf : Continuous f) (x a c : E) :
    Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • triangleIntegral f x (h • a) (h • c))
      (𝓝[>] 0) (𝓝 ((2⁻¹ * gramArea a c) • f x)) := by
  simpa using tendsto_triangleIntegral hf x 0 a c

end ContinuumMechanics
