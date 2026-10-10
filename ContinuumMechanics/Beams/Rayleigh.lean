import ContinuumMechanics.Beams.Buckling
import ContinuumMechanics.Beams.Wirtinger

/-!
# The Rayleigh quotient of a pinned column

For a pinned–pinned column the **Rayleigh quotient** of a lateral deflection `w` is

`R(w) = ∫₀ᴸ EI w''² / ∫₀ᴸ w'²`,

the ratio of the bending energy to the work of a unit axial load. Wirtinger's inequality gives
`R(w) ≥ π² EI / L²` for every admissible `w` (`C²`, `w(0) = w(L) = 0`, `w' ≢ 0`), with equality
for the buckling mode `sin(πx/L)`. Hence the Euler load is the minimum of the Rayleigh quotient
([TimoshenkoGere1961], §2.1).

## Main results

* `EBBeam.euler_load_le_rayleigh`: `π² EI / L² ≤ R(w)`.
* `EBBeam.rayleigh_mode`: `R(sin(πx/L)) = π² EI / L²`.
* `EBBeam.euler_load_isLeast_rayleigh`: `P_cr = min R`.

## References

* [TimoshenkoGere1961] S. P. Timoshenko, J. M. Gere, *Theory of Elastic Stability*, §2.1.
-/

open Set Real intervalIntegral
open scoped Real

namespace ContinuumMechanics.Beams

namespace EBBeam

variable (b : EBBeam)

/-- The **Rayleigh quotient** `R(w) = ∫ EI w''² / ∫ w'²`. [TimoshenkoGere1961], §2.1. -/
noncomputable def rayleigh (w : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..b.L, b.EI * deriv (deriv w) x ^ 2) / ∫ x in (0 : ℝ)..b.L, deriv w x ^ 2

/-- Admissible deflections of a pinned column: `C²`, vanishing at both ends, not rigid. -/
def RayleighAdmissible (w : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 w ∧ w 0 = 0 ∧ w b.L = 0 ∧ 0 < ∫ x in (0 : ℝ)..b.L, deriv w x ^ 2

/-- **Rayleigh's bound**: the Euler load bounds the Rayleigh quotient from below. -/
theorem euler_load_le_rayleigh {w : ℝ → ℝ} (hw : b.RayleighAdmissible w) :
    π ^ 2 * b.EI / b.L ^ 2 ≤ b.rayleigh w := by
  obtain ⟨hw, h0, h1, hpos⟩ := hw
  have := wirtinger_deriv b.L_pos hw h0 h1
  rw [rayleigh, integral_const_mul, le_div_iff₀ hpos]
  have hEI := b.EI_pos
  have e : π ^ 2 * b.EI / b.L ^ 2 * ∫ x in (0 : ℝ)..b.L, deriv w x ^ 2 =
      b.EI * ((π / b.L) ^ 2 * ∫ x in (0 : ℝ)..b.L, deriv w x ^ 2) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left this hEI.le

/-- The first buckling mode `sin(πx/L)`. -/
noncomputable def mode : ℝ → ℝ := fun x => sin (π / b.L * x)

theorem deriv_mode : deriv b.mode = fun x => π / b.L * cos (π / b.L * x) := by
  funext x
  have := ((hasDerivAt_id' x).const_mul (π / b.L)).sin
  unfold mode
  rw [this.deriv]
  ring

theorem deriv_deriv_mode : deriv (deriv b.mode) = fun x => -((π / b.L) ^ 2 * b.mode x) := by
  rw [deriv_mode]
  funext x
  have := (((hasDerivAt_id' x).const_mul (π / b.L)).cos).const_mul (π / b.L)
  rw [this.deriv]
  unfold mode
  ring

theorem contDiff_mode : ContDiff ℝ 2 b.mode :=
  contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem integral_mode_sq_pos : 0 < ∫ x in (0 : ℝ)..b.L, b.mode x ^ 2 := by
  refine intervalIntegral_pos_of_pos_on ((b.contDiff_mode.continuous.pow 2).intervalIntegrable _ _)
    (fun x hx => ?_) b.L_pos
  have hL := b.L_pos
  have : 0 < sin (π / b.L * x) := by
    apply sin_pos_of_pos_of_lt_pi
    · have := hx.1; positivity
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hL]
      nlinarith [hx.2, pi_pos]
  exact pow_pos this 2

theorem integral_deriv_mode_sq :
    ∫ x in (0 : ℝ)..b.L, deriv b.mode x ^ 2 =
      (π / b.L) ^ 2 * ∫ x in (0 : ℝ)..b.L, b.mode x ^ 2 := by
  rw [integral_deriv_sq_eq b.contDiff_mode (by simp [mode]) (by
      simp only [mode]; rw [div_mul_cancel₀ _ b.L_pos.ne', sin_pi]),
    deriv_deriv_mode, ← integral_const_mul, ← integral_neg]
  exact integral_congr fun x _ => by simp only; ring

theorem mode_admissible : b.RayleighAdmissible b.mode := by
  refine ⟨b.contDiff_mode, by simp [mode], by
    simp only [mode]; rw [div_mul_cancel₀ _ b.L_pos.ne', sin_pi], ?_⟩
  rw [integral_deriv_mode_sq]
  have := b.integral_mode_sq_pos
  have := b.L_pos
  positivity

/-- The buckling mode attains the Euler load. -/
theorem rayleigh_mode : b.rayleigh b.mode = π ^ 2 * b.EI / b.L ^ 2 := by
  have hI := b.integral_mode_sq_pos
  have hL := b.L_pos
  have h2 : ∫ x in (0 : ℝ)..b.L, b.EI * deriv (deriv b.mode) x ^ 2 =
      b.EI * (π / b.L) ^ 4 * ∫ x in (0 : ℝ)..b.L, b.mode x ^ 2 := by
    rw [deriv_deriv_mode, ← integral_const_mul]
    exact integral_congr fun x _ => by simp only; ring
  rw [rayleigh, h2, integral_deriv_mode_sq]
  field_simp

/-- **The Euler load is the minimum of the Rayleigh quotient**. [TimoshenkoGere1961], §2.1. -/
theorem euler_load_isLeast_rayleigh :
    IsLeast (b.rayleigh '' {w | b.RayleighAdmissible w}) (π ^ 2 * b.EI / b.L ^ 2) :=
  ⟨⟨b.mode, b.mode_admissible, b.rayleigh_mode⟩, by
    rintro _ ⟨w, hw, rfl⟩
    exact b.euler_load_le_rayleigh hw⟩

/-- The minimum of the Rayleigh quotient is the smallest buckling load. -/
theorem isLeast_bucklingLoads_eq_rayleigh :
    IsLeast b.bucklingLoads (π ^ 2 * b.EI / b.L ^ 2) ∧
      IsLeast (b.rayleigh '' {w | b.RayleighAdmissible w}) (π ^ 2 * b.EI / b.L ^ 2) :=
  ⟨b.euler_critical_load, b.euler_load_isLeast_rayleigh⟩

end EBBeam

end ContinuumMechanics.Beams
