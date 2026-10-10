import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Nexorade.OutOfPlane

/-!
# Parametric study of the square nexorade

The square nexorade cell is described by the scale `L > 0` and the angle `φ ∈ (0, π/4]` between
the nexors and the Cartesian axes ([Greco2013], (4.1)):

`a = L sin φ`,  `b = L (cos φ - sin φ)`,  so `a + b = L cos φ`, `A = L²`,
nexor length `l = 2a + b = L (cos φ + sin φ)`.

## Main results

* `Nexorade.cellOf`: the cell of parameters `(L, φ)`.
* `area_cellOf`: `A = L²`.
* `compliance_cellOf`: `d = (2L / (EI cos φ)) ((1 - tan φ / 3) + η / sin 2φ)`,
  `η = 4 EI / (G Sₛ L²)`; hence the stiffness `D = EI cos φ / (2L ((1 - tan φ / 3) + η / sin 2φ))`
  ([Greco2013], (5.3)).
* `shear_cellOf`: the nexor shear is `r = 2M / sin 2φ`, independent of `L` ([Greco2013], (5.5)).
* `moment_cellOf`: the maximal nexor moment is `m = L M / cos φ` ([Greco2013], (5.6)).
* `two_mul_cos_mul_le`, `normalized_moment_optimal`: the moment per unit nexor length,
  `m / (2l) = M / (2 cos φ (cos φ + sin φ))`, is smallest at **`φ = π/8`**, where it is
  `2(√2 - 1) ≈ 0.828` times its value at `φ = 0` or `π/4` (a 17% reduction).
* `tendsto_stiffness_zero`: with shear flexibility, `D → 0` as `φ → 0⁺`.

## References

* [Greco2013] L. Greco, *Nexorade* (homogenization of reciprocal systems), draft 2013, §§4–5.
-/

open Real Filter Topology
open scoped Real

noncomputable section

namespace ContinuumMechanics.Nexorade

theorem sin_le_cos_of_le_pi_div_four {φ : ℝ} (h0 : 0 ≤ φ) (h : φ ≤ π / 4) : sin φ ≤ cos φ := by
  rw [← sin_pi_div_two_sub]
  exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)

theorem cos_pos_of_le_pi_div_four {φ : ℝ} (h0 : 0 ≤ φ) (h : φ ≤ π / 4) : 0 < cos φ :=
  cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩

theorem sin_pos_of_le_pi_div_four {φ : ℝ} (h0 : 0 < φ) (h : φ ≤ π / 4) : 0 < sin φ :=
  sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])

/-- The nexorade cell of scale `L` and angle `φ ∈ (0, π/4]`. [Greco2013], (4.1). -/
def cellOf (L EI GS φ : ℝ) (hL : 0 < L) (hEI : 0 < EI) (hGS : 0 < GS) (hφ₀ : 0 < φ)
    (hφ : φ ≤ π / 4) : Cell where
  a := L * sin φ
  b := L * (cos φ - sin φ)
  EI := EI
  GS := GS
  a_pos := mul_pos hL (sin_pos_of_le_pi_div_four hφ₀ hφ)
  b_nonneg := mul_nonneg hL.le (sub_nonneg.2 (sin_le_cos_of_le_pi_div_four hφ₀.le hφ))
  EI_pos := hEI
  GS_pos := hGS

variable {L EI GS φ : ℝ} (hL : 0 < L) (hEI : 0 < EI) (hGS : 0 < GS) (hφ₀ : 0 < φ)
  (hφ : φ ≤ π / 4)

include hL hEI hGS hφ₀ hφ

theorem area_cellOf : (cellOf L EI GS φ hL hEI hGS hφ₀ hφ).area = L ^ 2 := by
  simp only [Cell.area, cellOf]
  linear_combination L ^ 2 * sin_sq_add_cos_sq φ

/-- `d = (2L / (EI cos φ)) ((1 - tan φ / 3) + η / sin 2φ)` with `η = 4 EI / (G Sₛ L²)`.
[Greco2013], (5.1)–(5.3). -/
theorem compliance_cellOf :
    (cellOf L EI GS φ hL hEI hGS hφ₀ hφ).compliance =
      2 * L / (EI * cos φ) * ((1 - tan φ / 3) + 4 * EI / (GS * L ^ 2) / sin (2 * φ)) := by
  have hc := cos_pos_of_le_pi_div_four hφ₀.le hφ
  have hs := sin_pos_of_le_pi_div_four hφ₀ hφ
  rw [Cell.compliance, area_cellOf, tan_eq_sin_div_cos, sin_two_mul]
  simp only [cellOf]
  field_simp [hc.ne', hs.ne']
  ring

/-- The stiffness `D = EI cos φ / (2L ((1 - tan φ / 3) + η / sin 2φ))`. [Greco2013], (5.3). -/
theorem stiffness_cellOf :
    (cellOf L EI GS φ hL hEI hGS hφ₀ hφ).stiffness =
      EI * cos φ / (2 * L * ((1 - tan φ / 3) + 4 * EI / (GS * L ^ 2) / sin (2 * φ))) := by
  rw [Cell.stiffness, compliance_cellOf]
  have hc := (cos_pos_of_le_pi_div_four hφ₀.le hφ).ne'
  field_simp

/-- The nexor **shear** under the plate moment `M` is `2M / sin 2φ`, independent of the scale `L`.
[Greco2013], (5.5). -/
theorem shear_cellOf (M : ℝ) :
    let c := cellOf L EI GS φ hL hEI hGS hφ₀ hφ
    M * c.area / (c.a * (c.a + c.b)) = 2 * M / sin (2 * φ) := by
  intro c
  have hc := (cos_pos_of_le_pi_div_four hφ₀.le hφ).ne'
  have hs := (sin_pos_of_le_pi_div_four hφ₀ hφ).ne'
  rw [area_cellOf, sin_two_mul]
  simp only [c, cellOf]
  field_simp [hc, hs]
  ring

/-- The maximal nexor **moment** (`s a`, on the middle segment) is `L M / cos φ`.
[Greco2013], (5.6). -/
theorem moment_cellOf (M : ℝ) :
    let c := cellOf L EI GS φ hL hEI hGS hφ₀ hφ
    M * c.area / (c.a * (c.a + c.b)) * c.a = L * M / cos φ := by
  intro c
  have hc := (cos_pos_of_le_pi_div_four hφ₀.le hφ).ne'
  have hs := (sin_pos_of_le_pi_div_four hφ₀ hφ).ne'
  rw [area_cellOf]
  simp only [c, cellOf]
  field_simp [hc, hs]
  ring

/-- The nexor length `l = 2a + b = L (cos φ + sin φ)`. [Greco2013], (4.2). -/
theorem length_cellOf :
    let c := cellOf L EI GS φ hL hEI hGS hφ₀ hφ
    2 * c.a + c.b = L * (cos φ + sin φ) := by
  intro c; simp only [c, cellOf]; ring

omit hL hEI hGS hφ₀ hφ

/-- `2 cos φ (cos φ + sin φ) ≤ 1 + √2`. -/
theorem two_mul_cos_mul_le (φ : ℝ) : 2 * cos φ * (cos φ + sin φ) ≤ 1 + √2 := by
  have e : 2 * cos φ * (cos φ + sin φ) = 1 + (cos (2 * φ) + sin (2 * φ)) := by
    rw [cos_two_mul, sin_two_mul]; ring
  have h : (cos (2 * φ) + sin (2 * φ)) ^ 2 ≤ 2 := by
    nlinarith [sin_sq_add_cos_sq (2 * φ), sq_nonneg (cos (2 * φ) - sin (2 * φ))]
  have h2 : cos (2 * φ) + sin (2 * φ) ≤ √2 := Real.le_sqrt_of_sq_le h
  linarith

/-- Equality at `φ = π/8`. -/
theorem two_mul_cos_mul_pi_div_eight :
    2 * cos (π / 8) * (cos (π / 8) + sin (π / 8)) = 1 + √2 := by
  have e : 2 * cos (π / 8) * (cos (π / 8) + sin (π / 8)) =
      1 + (cos (2 * (π / 8)) + sin (2 * (π / 8))) := by
    rw [cos_two_mul, sin_two_mul]; ring
  rw [e, show 2 * (π / 8) = π / 4 by ring, cos_pi_div_four, sin_pi_div_four]
  ring

/-- **Optimal angle for the normalized moment**: the moment per unit nexor length
`m / (2l) = M / (2 cos φ (cos φ + sin φ))` is minimal at `φ = π/8`, where it equals
`M / (1 + √2)`, i.e. `2(√2 - 1) ≈ 0.828` times its value `M / 2` at `φ = 0` and `φ = π/4`.
[Greco2013], §5. -/
theorem normalized_moment_optimal {M : ℝ} (hM : 0 ≤ M) (φ : ℝ)
    (hφ : 0 < 2 * cos φ * (cos φ + sin φ)) :
    M / (2 * cos (π / 8) * (cos (π / 8) + sin (π / 8))) ≤
      M / (2 * cos φ * (cos φ + sin φ)) ∧
    M / (2 * cos (π / 8) * (cos (π / 8) + sin (π / 8))) = 2 * (√2 - 1) * (M / 2) := by
  rw [two_mul_cos_mul_pi_div_eight]
  have hs : (0 : ℝ) < √2 := by positivity
  refine ⟨div_le_div_of_nonneg_left hM hφ (two_mul_cos_mul_le φ), ?_⟩
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [h2]

theorem two_mul_cos_mul_zero : 2 * cos 0 * (cos 0 + sin 0) = 2 := by simp

theorem two_mul_cos_mul_pi_div_four : 2 * cos (π / 4) * (cos (π / 4) + sin (π / 4)) = 2 := by
  rw [cos_pi_div_four, sin_pi_div_four]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-- **Shear-dominated limit**: with finite shear stiffness, the plate stiffness
`D(φ) = EI cos φ / (2L ((1 - tan φ / 3) + η / sin 2φ))` (`η > 0`) tends to `0` as `φ → 0⁺`;
for Euler–Bernoulli nexors (`η = 0`) it tends to `EI / (2L)` instead. [Greco2013], §5. -/
theorem tendsto_stiffness_zero {EI L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    Tendsto (fun φ => EI * cos φ / (2 * L * ((1 - tan φ / 3) + η / sin (2 * φ))))
      (𝓝[>] 0) (𝓝 0) := by
  have hnum : Tendsto (fun φ : ℝ => EI * cos φ) (𝓝[>] 0) (𝓝 (EI * cos 0)) :=
    ((continuous_const.mul continuous_cos).tendsto 0).mono_left nhdsWithin_le_nhds
  have htan : Tendsto (fun φ : ℝ => 1 - tan φ / 3) (𝓝[>] 0) (𝓝 (1 - sin 0 / cos 0 / 3)) := by
    have : Tendsto (fun φ : ℝ => sin φ / cos φ) (𝓝 0) (𝓝 (sin 0 / cos 0)) :=
      (continuous_sin.tendsto 0).div (continuous_cos.tendsto 0) (by simp)
    simp_rw [tan_eq_sin_div_cos]
    exact (tendsto_const_nhds.sub (this.div_const 3)).mono_left nhdsWithin_le_nhds
  have hsin : Tendsto (fun φ : ℝ => sin (2 * φ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun φ : ℝ => sin (2 * φ) :=
        continuous_sin.comp (continuous_const.mul continuous_id)
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with φ hφ
      exact sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2])
  have hinv : Tendsto (fun φ : ℝ => η / sin (2 * φ)) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv]
    exact (tendsto_inv_nhdsGT_zero.comp hsin).const_mul_atTop hη
  have hden : Tendsto (fun φ => 2 * L * ((1 - tan φ / 3) + η / sin (2 * φ))) (𝓝[>] 0) atTop :=
    (htan.add_atTop hinv).const_mul_atTop (by positivity)
  exact hnum.div_atTop hden

end ContinuumMechanics.Nexorade

end
