import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Nexorade.OutOfPlane

/-!
# Design formulas and optima in terms of the relative engagement length `a/l`

The paper expresses the results through the member length `l = 2a + b` and the relative
engagement length `x = a/l ∈ (0, 1/2]` ([GrecoLebeeDouthe2013], §§3–4). With `q(x) = x² + (1-x)²`
(so that the cell area is `A = l² q(x)`):

* shear `r / M = q(x) / (x (1 - x))` (32), independent of `l`;
* moment `m / M = l q(x) / (1 - x)` (32), minimal at `x = 1 - √2/2` where it is `(2√2 - 2) l`,
  maximal (`= l`) at `x = 0` and `x = 1/2` (33);
* Euler–Bernoulli members (31): `D = (3EI / 2l) (1 - x)² / ((3 - 4x) q(x))`, maximal at
  `x = 1/2` (§4.2);
* very soft members (`G Sₛ → 0`): `D / (G Sₛ) → (l/4) x (1 - x)² / q(x)`, maximal at the root
  `x₀ ≈ 0.3966` of `2x³ - 2x² + 3x - 1` (§4.2);
* trade-off (§4.2): choosing the stress optimum `x = 1 - √2/2` instead of the stiffness optimum
  `x = 1/2` increases the deflection by the factor `5√2 - 6 ≈ 1.071` (≈ 7%); conversely the
  stiffness optimum increases the bending stresses by `(√2 + 1)/2 ≈ 1.207` (≈ 20%).

## References

* [GrecoLebeeDouthe2013] L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of
  reciprocal systems using homogenization techniques* (2013).
-/

open Filter Topology Set

noncomputable section

namespace ContinuumMechanics.Nexorade

/-- `q(x) = x² + (1 - x)²`, so that `A = l² q(a/l)`. -/
def qShape (x : ℝ) : ℝ := x ^ 2 + (1 - x) ^ 2

theorem qShape_pos (x : ℝ) : 0 < qShape x := by
  unfold qShape; nlinarith [sq_nonneg (2 * x - 1)]

/-- Normalized nexor moment `m / (M l) = q(x) / (1 - x)`. -/
def momentShape (x : ℝ) : ℝ := qShape x / (1 - x)

/-- Normalized nexor shear `r / M = q(x) / (x (1 - x))`. -/
def shearShape (x : ℝ) : ℝ := qShape x / (x * (1 - x))

/-- Normalized Euler–Bernoulli stiffness `D · 2l / (3EI) = (1 - x)² / ((3 - 4x) q(x))`. -/
def eulerShape (x : ℝ) : ℝ := (1 - x) ^ 2 / ((3 - 4 * x) * qShape x)

/-- Normalized soft-shear stiffness `lim D / (G Sₛ) · 4 / l = x (1 - x)² / q(x)`. -/
def softShape (x : ℝ) : ℝ := x * (1 - x) ^ 2 / qShape x

namespace Cell

variable (c : Cell)

/-- The member length `l = 2a + b`. -/
def len : ℝ := 2 * c.a + c.b

theorem len_pos : 0 < c.len := by have := c.a_pos; have := c.b_nonneg; unfold len; linarith

/-- The relative engagement length `x = a / l`. -/
def x : ℝ := c.a / c.len

theorem _root_.ContinuumMechanics.Nexorade.qShape_div (u l : ℝ) (hl : l ≠ 0) :
    l ^ 2 * qShape (u / l) = u ^ 2 + (l - u) ^ 2 := by
  simp only [qShape]
  field_simp

theorem area_eq : c.area = c.len ^ 2 * qShape c.x := by
  rw [x, qShape_div _ _ c.len_pos.ne', area, len]
  ring

/-- (32) **Shear**: `r = M q(x) / (x (1 - x))`, independent of the member length. -/
theorem shear_eq (M : ℝ) : M * c.area / (c.a * (c.a + c.b)) = M * shearShape c.x := by
  have hl := c.len_pos.ne'
  have ha := c.a_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  rw [area_eq, shearShape, x]
  have hq := (qShape_pos (c.a / c.len)).ne'
  have hl' : c.len - c.a = c.a + c.b := by simp only [len]; ring
  have hxl : c.a / c.len * (1 - c.a / c.len) = c.a * (c.a + c.b) / c.len ^ 2 := by
    rw [← hl']; field_simp
  rw [hxl]
  field_simp

/-- (32) **Moment**: `m = M l q(x) / (1 - x)`. -/
theorem moment_eq (M : ℝ) :
    M * c.area / (c.a * (c.a + c.b)) * c.a = M * c.len * momentShape c.x := by
  have hl := c.len_pos.ne'
  have ha := c.a_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  rw [area_eq, momentShape, x]
  have hl' : c.len - c.a = c.a + c.b := by simp only [len]; ring
  have h1x : 1 - c.a / c.len = (c.a + c.b) / c.len := by rw [← hl']; field_simp
  rw [h1x]
  field_simp

/-- The bending part of the compliance (Euler–Bernoulli members). -/
def complianceEuler : ℝ := 2 * c.area * (2 * c.a + 3 * c.b) / (3 * c.EI * (c.a + c.b) ^ 2)

/-- (31) **Euler–Bernoulli stiffness**: `D = (3EI / 2l) (1 - x)² / ((3 - 4x) q(x))`. -/
theorem complianceEuler_inv :
    c.complianceEuler⁻¹ = 3 * c.EI / (2 * c.len) * eulerShape c.x := by
  have hl := c.len_pos.ne'
  have ha := c.a_pos.ne'
  have hE := c.EI_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  have h34 : 3 * c.len - 4 * c.a ≠ 0 := by
    have := c.a_pos; have := c.b_nonneg; simp only [len]; intro h; linarith
  have hq := (qShape_pos c.x).ne'
  rw [complianceEuler, area_eq, eulerShape]
  simp only [x, len] at *
  field_simp
  ring

/-- Infinitely shear-rigid members: the compliance tends to its bending part as `G Sₛ → ∞`. -/
theorem tendsto_compliance_shear_rigid :
    Tendsto (fun GS : ℝ => c.complianceEuler + 4 * c.area / (GS * c.a * (c.a + c.b) ^ 2))
      atTop (𝓝 c.complianceEuler) := by
  have hk : 0 < c.a * (c.a + c.b) ^ 2 := by
    have := c.a_pos; have := c.b_nonneg; positivity
  have : Tendsto (fun GS : ℝ => 4 * c.area / (GS * c.a * (c.a + c.b) ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_id.atTop_mul_const hk).const_div_atTop (4 * c.area)
    refine h.congr fun GS => ?_
    simp [mul_assoc]
  simpa using tendsto_const_nhds.add this

/-- Very soft members: `D / (G Sₛ) → (l/4) x (1 - x)² / q(x)` as `G Sₛ → 0⁺`. -/
theorem tendsto_stiffness_soft :
    Tendsto (fun GS : ℝ => (c.complianceEuler + 4 * c.area / (GS * c.a * (c.a + c.b) ^ 2))⁻¹ / GS)
      (𝓝[>] 0) (𝓝 (c.len / 4 * softShape c.x)) := by
  have hl := c.len_pos.ne'
  have ha := c.a_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  have hA := c.area_pos.ne'
  -- `D / GS = 1 / (GS d_E + 4A / (a (a+b)²))`
  have e : ∀ GS : ℝ, GS ≠ 0 →
      (c.complianceEuler + 4 * c.area / (GS * c.a * (c.a + c.b) ^ 2))⁻¹ / GS =
        (GS * c.complianceEuler + 4 * c.area / (c.a * (c.a + c.b) ^ 2))⁻¹ := fun GS hGS => by
    field_simp
  have hlim : Tendsto (fun GS : ℝ => (GS * c.complianceEuler + 4 * c.area /
      (c.a * (c.a + c.b) ^ 2))⁻¹) (𝓝 0) (𝓝 ((0 * c.complianceEuler + 4 * c.area /
      (c.a * (c.a + c.b) ^ 2))⁻¹)) :=
    ((tendsto_id.mul_const _).add tendsto_const_nhds).inv₀ (by
      rw [zero_mul, zero_add]; positivity)
  have hval : (0 * c.complianceEuler + 4 * c.area / (c.a * (c.a + c.b) ^ 2))⁻¹ =
      c.len / 4 * softShape c.x := by
    rw [zero_mul, zero_add, area_eq, softShape]
    have hq := (qShape_pos c.x).ne'
    simp only [x, len] at *
    field_simp
    ring
  rw [hval] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with GS hGS
  exact (e GS (ne_of_gt hGS)).symm

end Cell

/-! ### Optima -/

/-- (33) The normalized moment is at least `2√2 - 2`. -/
theorem momentShape_ge {x : ℝ} (hx : x < 1) : 2 * √2 - 2 ≤ momentShape x := by
  have hu : 0 < 1 - x := by linarith
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [momentShape, le_div_iff₀ hu, qShape]
  nlinarith [sq_nonneg (√2 * (1 - x) - 1)]

/-- The minimum is attained at `x = 1 - √2/2`. -/
theorem momentShape_opt : momentShape (1 - √2 / 2) = 2 * √2 - 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < √2 := by positivity
  rw [momentShape, qShape, div_eq_iff (by nlinarith)]
  nlinarith

theorem momentShape_zero : momentShape 0 = 1 := by norm_num [momentShape, qShape]

theorem momentShape_half : momentShape (1 / 2) = 1 := by norm_num [momentShape, qShape]

/-- §4.2 **Euler–Bernoulli members: the stiffness is maximal at `x = 1/2`**,
`eulerShape (1/2) - eulerShape x = (1 - 2x)³ / (2 (3 - 4x) q(x))`. -/
theorem eulerShape_le {x : ℝ} (hx : x ≤ 1 / 2) : eulerShape x ≤ eulerShape (1 / 2) := by
  have h34 : 0 < 3 - 4 * x := by linarith
  have hq := qShape_pos x
  have : eulerShape (1 / 2) = 1 / 2 := by norm_num [eulerShape, qShape]
  rw [this, eulerShape, div_le_iff₀ (by positivity), qShape]
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * x) 3]

/-- The cubic `p(x) = 2x³ - 2x² + 3x - 1` whose root is the soft-shear optimum. -/
def optPoly (x : ℝ) : ℝ := 2 * x ^ 3 - 2 * x ^ 2 + 3 * x - 1

theorem optPoly_strictMono : StrictMono optPoly := fun x y hxy => by
  simp only [optPoly]
  nlinarith [sq_nonneg (x + y - 1), sq_nonneg (x - y), mul_pos (sub_pos.2 hxy) (sub_pos.2 hxy)]

/-- The soft-shear optimum exists, is unique, and lies in `(0.3966, 0.3967)`. -/
theorem exists_unique_optPoly_root :
    ∃! x₀, x₀ ∈ Ioo (0 : ℝ) (1 / 2) ∧ optPoly x₀ = 0 := by
  have hc : ContinuousOn optPoly (Icc 0 (1 / 2)) := by unfold optPoly; fun_prop
  obtain ⟨x₀, hx₀, h0⟩ := intermediate_value_Ioo (by norm_num) hc
    (show (0 : ℝ) ∈ Ioo (optPoly 0) (optPoly (1 / 2)) by norm_num [optPoly])
  exact ⟨x₀, ⟨hx₀, h0⟩, fun y hy => optPoly_strictMono.injective (hy.2.trans h0.symm)⟩

theorem optPoly_root_bounds {x₀ : ℝ} (h : optPoly x₀ = 0) : 0.3966 < x₀ ∧ x₀ < 0.3967 := by
  constructor
  · by_contra hc
    have := optPoly_strictMono.monotone (not_lt.mp hc)
    rw [h] at this
    have hv : optPoly 0.3966 < 0 := by norm_num [optPoly]
    linarith
  · by_contra hc
    have := optPoly_strictMono.monotone (not_lt.mp hc)
    rw [h] at this
    have hv : 0 < optPoly 0.3967 := by norm_num [optPoly]
    linarith

/-- §4.2 **Soft members: the stiffness is maximal at the root `x₀ ≈ 0.3966` of `p`.**
`softShape x₀ - softShape x = (x₀ - x)² T(x, x₀) / (q(x) q(x₀))` with `T ≥ 0`. -/
theorem softShape_le {x x₀ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hx₀ : x₀ ∈ Icc (0 : ℝ) (1 / 2))
    (hp : optPoly x₀ = 0) : softShape x ≤ softShape x₀ := by
  have hq := qShape_pos x
  have hq₀ := qShape_pos x₀
  rw [softShape, softShape, div_le_div_iff₀ hq hq₀]
  have key : x₀ * (1 - x₀) ^ 2 * qShape x - x * (1 - x) ^ 2 * qShape x₀ =
      (x₀ - x) ^ 2 * (-2 * x * x₀ ^ 2 + 2 * x * x₀ - x - 2 * x₀ ^ 3 + 4 * x₀ ^ 2 - 4 * x₀ + 2) +
        (x₀ - x) * (x₀ - 1) * optPoly x₀ := by
    simp only [qShape, optPoly]; ring
  rw [hp, mul_zero, add_zero] at key
  have hT : 0 ≤ -2 * x * x₀ ^ 2 + 2 * x * x₀ - x - 2 * x₀ ^ 3 + 4 * x₀ ^ 2 - 4 * x₀ + 2 := by
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hx₀
    nlinarith [mul_nonneg h1 h3, mul_nonneg h3 h3, mul_nonneg (mul_nonneg h3 h3) h3,
      mul_nonneg (mul_nonneg h1 h3) h3, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
  nlinarith [mul_nonneg (sq_nonneg (x₀ - x)) hT]

/-- §4.2 **Trade-off, deflection**: with Euler–Bernoulli members, choosing the stress optimum
`x = 1 - √2/2` instead of `x = 1/2` multiplies the deflection by `5√2 - 6 ≈ 1.071`. -/
theorem deflection_ratio : eulerShape (1 / 2) / eulerShape (1 - √2 / 2) = 5 * √2 - 6 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 1.4 < √2 := by
    rw [show (1.4 : ℝ) = √(1.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have e0 : eulerShape (1 / 2) = 1 / 2 := by norm_num [eulerShape, qShape]
  have e1 : (1 - (1 - √2 / 2)) ^ 2 = 1 / 2 := by nlinarith
  have e2 : (3 - 4 * (1 - √2 / 2)) * qShape (1 - √2 / 2) = 5 * √2 - 6 := by
    simp only [qShape]; nlinarith
  have hK : 0 < 5 * √2 - 6 := by linarith
  rw [e0, eulerShape, e1, e2]
  field_simp

/-- §4.2 **Trade-off, stresses**: choosing the stiffness optimum `x = 1/2` instead of the stress
optimum multiplies the bending moment by `(√2 + 1)/2 ≈ 1.207`. -/
theorem moment_ratio : momentShape (1 / 2) / momentShape (1 - √2 / 2) = (√2 + 1) / 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 1 < √2 := by
    rw [show (1 : ℝ) = √(1 ^ 2) by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [momentShape_half, momentShape_opt, div_eq_iff (by linarith)]
  nlinarith

end ContinuumMechanics.Nexorade

end
