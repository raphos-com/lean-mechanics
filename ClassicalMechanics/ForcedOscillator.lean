import ClassicalMechanics.Oscillator
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The driven damped oscillator and resonance

A mass `m > 0` on a spring of stiffness `k > 0` with viscous damping `c ≥ 0`, driven by the
periodic force `F₀ cos Ωt`, obeys

`m ẍ + c ẋ + k x = F₀ cos Ωt`.

Write `ω₀² = k/m` and `γ = c/(2m)` ([Goldstein2002], §6; [Landau1976], §§22, 26).

* **Steady state** (`Driven.xp_solves`): with `D = (k - mΩ²)² + c²Ω² ≠ 0`, the function
  `x_p(t) = A cos Ωt + B sin Ωt`, `A = F₀ (k - mΩ²)/D`, `B = F₀ c Ω / D`, solves the equation.
  In amplitude–phase form (`Driven.xp_eq_amplitude_mul_cos`) `x_p(t) = X cos(Ωt - φ)` with
  `X(Ω) = (F₀/m)/√((ω₀² - Ω²)² + 4γ²Ω²)` and `tan φ = 2γΩ/(ω₀² - Ω²)` (`Driven.tan_phase`).
* **General solution** (`Driven.Motion`): if `x` solves the forced equation, `x - x_p` solves
  the free damped equation (`Driven.Motion.transient`), so its energy is non-increasing
  (`Driven.Motion.transient_energy_antitone`).
* **Resonance** (`Driven.amplitude_le_resonance`): if `ω₀² > 2γ²` and `c > 0`, the amplitude is
  maximal at `Ω_r = √(ω₀² - 2γ²)`, where it equals `(F₀/m)/(2γ√(ω₀² - γ²))`
  (`Driven.amplitude_resonance`).
* **Undamped resonance** (`undamped_resonance_solves`, `undamped_resonance_unbounded`): for
  `c = 0`, `Ω = ω₀`, the motion `x(t) = (F₀/(2mω₀)) t sin ω₀t` grows without bound.
* **Power balance** (`Driven.power_balance`): over one period, the work done by the driving
  force on the steady state equals the energy dissipated, `∫ F ẋ = ∫ c ẋ² = (2π/Ω)·½ c Ω² X²`.
* **Beats** (`beats_solves`, `beats_eq_sin_mul_sin`): for `c = 0`, `Ω ≠ ω₀`, the motion
  starting at rest from equilibrium is `x(t) = (F₀/(m(ω₀² - Ω²)))(cos Ωt - cos ω₀t)`, a product
  `2 sin((ω₀ - Ω)t/2) sin((ω₀ + Ω)t/2)` times a constant.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §6.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §§22, 26.
-/

open Real
open scoped Real

noncomputable section

namespace ClassicalMechanics

/-- A **driven damped oscillator** `m ẍ + c ẋ + k x = F₀ cos Ωt`; the driving frequency `Ω` is
kept as a parameter of the definitions below. -/
structure Driven where
  m : ℝ
  c : ℝ
  k : ℝ
  F₀ : ℝ
  m_pos : 0 < m
  c_nonneg : 0 ≤ c
  k_pos : 0 < k

namespace Driven

variable (P : Driven)

/-- The determinant `D(Ω) = (k - mΩ²)² + c²Ω²` of the linear system for the steady state. -/
def denom (Ω : ℝ) : ℝ := (P.k - P.m * Ω ^ 2) ^ 2 + (P.c * Ω) ^ 2

/-- The determinant is non-negative. -/
theorem denom_nonneg (Ω : ℝ) : 0 ≤ P.denom Ω := by unfold denom; positivity

/-- With damping and `Ω ≠ 0` the determinant is positive. -/
theorem denom_pos_of_damped (hc : 0 < P.c) {Ω : ℝ} (hΩ : Ω ≠ 0) : 0 < P.denom Ω := by
  unfold denom
  have : 0 < (P.c * Ω) ^ 2 := by positivity
  positivity

/-- Off the undamped resonance `Ω² = k/m` the determinant is positive. -/
theorem denom_pos_of_ne {Ω : ℝ} (hΩ : Ω ^ 2 ≠ P.k / P.m) : 0 < P.denom Ω := by
  unfold denom
  have : P.k - P.m * Ω ^ 2 ≠ 0 := by
    intro h; apply hΩ; field_simp [P.m_pos.ne']; linarith
  have : 0 < (P.k - P.m * Ω ^ 2) ^ 2 := by positivity
  positivity

/-- The cosine coefficient `A = F₀ (k - mΩ²)/D` of the steady state. -/
def coefA (Ω : ℝ) : ℝ := P.F₀ * (P.k - P.m * Ω ^ 2) / P.denom Ω

/-- The sine coefficient `B = F₀ c Ω / D` of the steady state. -/
def coefB (Ω : ℝ) : ℝ := P.F₀ * (P.c * Ω) / P.denom Ω

/-- The **steady-state** particular solution `x_p(t) = A cos Ωt + B sin Ωt`. -/
def xp (Ω t : ℝ) : ℝ := P.coefA Ω * cos (Ω * t) + P.coefB Ω * sin (Ω * t)

/-- Its velocity `ẋ_p(t) = Ω (-A sin Ωt + B cos Ωt)`. -/
def vp (Ω t : ℝ) : ℝ := Ω * (-P.coefA Ω * sin (Ω * t) + P.coefB Ω * cos (Ω * t))

/-- `ẋ_p` is the derivative of `x_p`. -/
theorem hasDerivAt_xp (Ω t : ℝ) : HasDerivAt (P.xp Ω) (P.vp Ω t) t := by
  have hC := ((hasDerivAt_id t).const_mul Ω).cos.const_mul (P.coefA Ω)
  have hS := ((hasDerivAt_id t).const_mul Ω).sin.const_mul (P.coefB Ω)
  convert hC.add hS using 1
  · funext y; simp only [xp, id, Pi.add_apply]
  simp only [vp, id, mul_one]
  ring

/-- `ẍ_p = -Ω² x_p`. -/
theorem hasDerivAt_vp (Ω t : ℝ) : HasDerivAt (P.vp Ω) (-Ω ^ 2 * P.xp Ω t) t := by
  have hS := ((hasDerivAt_id t).const_mul Ω).sin.const_mul (-P.coefA Ω)
  have hC := ((hasDerivAt_id t).const_mul Ω).cos.const_mul (P.coefB Ω)
  convert (hS.add hC).const_mul Ω using 1
  · funext y; simp only [vp, id, Pi.add_apply]
  simp only [xp, id, mul_one]
  ring

/-- **The steady state solves the driven equation** `m ẍ + c ẋ + k x = F₀ cos Ωt`
(the coefficients `A`, `B` solve the 2×2 linear system obtained by matching the `cos Ωt` and
`sin Ωt` terms). -/
theorem xp_solves {Ω : ℝ} (hD : P.denom Ω ≠ 0) (t : ℝ) :
    HasDerivAt (P.xp Ω) (P.vp Ω t) t ∧
      HasDerivAt (P.vp Ω) (-Ω ^ 2 * P.xp Ω t) t ∧
      P.m * (-Ω ^ 2 * P.xp Ω t) + P.c * P.vp Ω t + P.k * P.xp Ω t = P.F₀ * cos (Ω * t) := by
  refine ⟨P.hasDerivAt_xp Ω t, P.hasDerivAt_vp Ω t, ?_⟩
  simp only [xp, vp, coefA, coefB]
  field_simp
  unfold denom
  ring

/-- `A² + B² = F₀²/D`. -/
theorem coefA_sq_add_coefB_sq (Ω : ℝ) :
    P.coefA Ω ^ 2 + P.coefB Ω ^ 2 = P.F₀ ^ 2 / P.denom Ω := by
  rcases eq_or_ne (P.denom Ω) 0 with h | h
  · simp [coefA, coefB, h]
  simp only [coefA, coefB]
  field_simp
  unfold denom
  ring

/-- The **amplitude** `X(Ω) = (F₀/m)/√((ω₀² - Ω²)² + 4γ²Ω²)`, `ω₀² = k/m`, `γ = c/(2m)`. -/
def amplitude (Ω : ℝ) : ℝ :=
  P.F₀ / P.m / √((P.k / P.m - Ω ^ 2) ^ 2 + 4 * (P.c / (2 * P.m)) ^ 2 * Ω ^ 2)

/-- `X(Ω) = F₀/√D(Ω)`. -/
theorem amplitude_eq (Ω : ℝ) : P.amplitude Ω = P.F₀ / √(P.denom Ω) := by
  have hm := P.m_pos
  have h : (P.k / P.m - Ω ^ 2) ^ 2 + 4 * (P.c / (2 * P.m)) ^ 2 * Ω ^ 2 =
      P.denom Ω / P.m ^ 2 := by
    unfold denom; field_simp; ring
  rw [amplitude, h, sqrt_div' _ (by positivity), sqrt_sq hm.le]
  rcases eq_or_ne (√(P.denom Ω)) 0 with h0 | h0
  · simp [h0]
  field_simp

/-- `X² = A² + B²`. -/
theorem amplitude_sq (Ω : ℝ) : P.amplitude Ω ^ 2 = P.coefA Ω ^ 2 + P.coefB Ω ^ 2 := by
  rw [coefA_sq_add_coefB_sq, amplitude_eq, div_pow, sq_sqrt (P.denom_nonneg Ω)]

/-- The **phase lag** `φ = arg (A + iB)`. -/
def phase (Ω : ℝ) : ℝ := Complex.arg ⟨P.coefA Ω, P.coefB Ω⟩

/-- For `F₀ ≥ 0`, `‖A + iB‖ = X`. -/
theorem norm_coef (hF : 0 ≤ P.F₀) (Ω : ℝ) :
    ‖(⟨P.coefA Ω, P.coefB Ω⟩ : ℂ)‖ = P.amplitude Ω := by
  have hX : 0 ≤ P.amplitude Ω := by rw [amplitude_eq]; positivity
  rw [Complex.norm_def, Complex.normSq_mk, ← pow_two, ← pow_two, ← amplitude_sq,
    sqrt_sq hX]

/-- **Amplitude–phase form** of the steady state: `x_p(t) = X cos(Ωt - φ)` (for `F₀ ≥ 0`). -/
theorem xp_eq_amplitude_mul_cos (hF : 0 ≤ P.F₀) (Ω t : ℝ) :
    P.xp Ω t = P.amplitude Ω * cos (Ω * t - P.phase Ω) := by
  have hc := Complex.norm_mul_cos_arg (⟨P.coefA Ω, P.coefB Ω⟩ : ℂ)
  have hs := Complex.norm_mul_sin_arg (⟨P.coefA Ω, P.coefB Ω⟩ : ℂ)
  rw [P.norm_coef hF] at hc hs
  rw [cos_sub, xp, phase]
  simp only at hc hs
  linear_combination (-cos (Ω * t)) * hc - sin (Ω * t) * hs

/-- The phase lag satisfies `tan φ = 2γΩ/(ω₀² - Ω²)` (for `F₀ ≠ 0`). -/
theorem tan_phase (hF : P.F₀ ≠ 0) {Ω : ℝ} (hD : P.denom Ω ≠ 0) :
    tan (P.phase Ω) = 2 * (P.c / (2 * P.m)) * Ω / (P.k / P.m - Ω ^ 2) := by
  have hm := P.m_pos.ne'
  rw [phase, Complex.tan_arg]
  simp only [coefA, coefB]
  rcases eq_or_ne (P.k - P.m * Ω ^ 2) 0 with h | h
  · have h' : P.k / P.m - Ω ^ 2 = 0 := by field_simp; linarith
    simp [h, h']
  have h' : P.k / P.m - Ω ^ 2 ≠ 0 := by
    intro h'; apply h; field_simp at h'; linarith
  field_simp

/-! ### Resonance -/

/-- The **resonance frequency** `Ω_r = √(ω₀² - 2γ²)`. -/
def resonanceFreq : ℝ := √(P.k / P.m - 2 * (P.c / (2 * P.m)) ^ 2)

/-- **Peak amplitude**: `X(Ω_r) = (F₀/m)/(2γ√(ω₀² - γ²))` when `ω₀² > 2γ²`, `γ ≥ 0`. -/
theorem amplitude_resonance (hr : 2 * (P.c / (2 * P.m)) ^ 2 < P.k / P.m) :
    P.amplitude P.resonanceFreq =
      P.F₀ / P.m / (2 * (P.c / (2 * P.m)) * √(P.k / P.m - (P.c / (2 * P.m)) ^ 2)) := by
  set w := P.k / P.m
  set g := P.c / (2 * P.m)
  have hg : 0 ≤ g := div_nonneg P.c_nonneg (by linarith [P.m_pos])
  have hΩ : P.resonanceFreq ^ 2 = w - 2 * g ^ 2 := sq_sqrt (by linarith)
  rw [amplitude, hΩ]
  congr 1
  rw [show (w - (w - 2 * g ^ 2)) ^ 2 + 4 * g ^ 2 * (w - 2 * g ^ 2) = (2 * g) ^ 2 * (w - g ^ 2)
    by ring, sqrt_mul (by positivity), sqrt_sq (by positivity)]

/-- **Resonance**: for `c > 0` and `ω₀² > 2γ²` the amplitude `X(Ω)` is maximal at
`Ω = Ω_r = √(ω₀² - 2γ²)` (for `F₀ ≥ 0`). -/
theorem amplitude_le_resonance (hF : 0 ≤ P.F₀) (hc : 0 < P.c)
    (hr : 2 * (P.c / (2 * P.m)) ^ 2 < P.k / P.m) (Ω : ℝ) :
    P.amplitude Ω ≤ P.amplitude P.resonanceFreq := by
  have hm := P.m_pos
  set w := P.k / P.m
  set g := P.c / (2 * P.m)
  have hg : 0 < g := div_pos hc (by linarith)
  have hΩ : P.resonanceFreq ^ 2 = w - 2 * g ^ 2 := sq_sqrt (by linarith)
  simp only [amplitude]
  rw [hΩ]
  apply div_le_div_of_nonneg_left (div_nonneg hF hm.le)
  · apply sqrt_pos.mpr
    nlinarith [mul_pos (pow_pos hg 2) (show 0 < w - g ^ 2 by nlinarith)]
  · apply sqrt_le_sqrt
    nlinarith [sq_nonneg (Ω ^ 2 - w + 2 * g ^ 2)]

/-! ### General solution: steady state plus transient -/

/-- A **motion** of the driven oscillator at driving frequency `Ω`:
`m ẍ + c ẋ + k x = F₀ cos Ωt`. -/
structure Motion (Ω : ℝ) where
  x : ℝ → ℝ
  v : ℝ → ℝ
  a : ℝ → ℝ
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  eq : ∀ t, P.m * a t + P.c * v t + P.k * x t = P.F₀ * cos (Ω * t)

namespace Motion

variable {P} {Ω : ℝ} (M : P.Motion Ω)

/-- **Linearity**: the **transient** `x - x_p` solves the free damped equation
`m ẍ + c ẋ + k x = 0`. -/
def transient (hD : P.denom Ω ≠ 0) : Damped where
  m := P.m
  c := P.c
  k := P.k
  m_pos := P.m_pos
  c_nonneg := P.c_nonneg
  k_pos := P.k_pos
  x t := M.x t - P.xp Ω t
  v t := M.v t - P.vp Ω t
  a t := M.a t - -Ω ^ 2 * P.xp Ω t
  hasDerivAt_x t := (M.hasDerivAt_x t).sub (P.hasDerivAt_xp Ω t)
  hasDerivAt_v t := (M.hasDerivAt_v t).sub (P.hasDerivAt_vp Ω t)
  eq t := by linear_combination M.eq t - (P.xp_solves hD t).2.2

/-- **General solution** = steady state + transient. -/
theorem eq_xp_add_transient (hD : P.denom Ω ≠ 0) (t : ℝ) :
    M.x t = P.xp Ω t + (M.transient hD).x t := by
  simp [transient]

/-- The energy `½ m (ẋ - ẋ_p)² + ½ k (x - x_p)²` of the transient is non-increasing
(it is dissipated at the rate `c (ẋ - ẋ_p)²`). -/
theorem transient_energy_antitone (hD : P.denom Ω ≠ 0) :
    Antitone (M.transient hD).energy :=
  (M.transient hD).energy_antitone

end Motion

/-! ### Power balance over a period -/

/-- **Work done by the driving force** over one period `2π/Ω` on the steady state:
`∫₀^{2π/Ω} F₀ cos(Ωt) ẋ_p dt = π F₀ B`. -/
theorem integral_power_input {Ω : ℝ} (hΩ : Ω ≠ 0) :
    ∫ t in (0 : ℝ)..2 * π / Ω, P.F₀ * cos (Ω * t) * P.vp Ω t = π * P.F₀ * P.coefB Ω := by
  set A := P.coefA Ω
  set B := P.coefB Ω
  have key : ∀ t, HasDerivAt (fun t => P.F₀ * (-A * (sin (Ω * t) * sin (Ω * t)) / 2 +
      B * (Ω * t / 2 + sin (Ω * t) * cos (Ω * t) / 2)))
      (P.F₀ * cos (Ω * t) * P.vp Ω t) t := by
    intro t
    have hs := ((hasDerivAt_id t).const_mul Ω).sin
    have hc := ((hasDerivAt_id t).const_mul Ω).cos
    have h := (((((hs.mul hs).const_mul (-A)).div_const 2).add
      (((((hasDerivAt_id t).const_mul Ω).div_const 2).add
        ((hs.mul hc).div_const 2)).const_mul B)).const_mul P.F₀)
    refine h.congr_deriv ?_
    simp only [vp, id, mul_one]
    linear_combination (-(P.F₀ * B * Ω / 2)) * sin_sq_add_cos_sq (Ω * t)
  have hcont : Continuous fun t => P.F₀ * cos (Ω * t) * P.vp Ω t := by
    unfold vp; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => key t)
    (hcont.intervalIntegrable _ _)]
  have hT : Ω * (2 * π / Ω) = 2 * π := by field_simp
  simp only [hT, sin_two_pi, cos_two_pi, mul_zero, sin_zero, cos_zero]
  field_simp
  ring

/-- **Energy dissipated** by friction over one period on the steady state:
`∫₀^{2π/Ω} c ẋ_p² dt = π c Ω (A² + B²)`. -/
theorem integral_dissipation {Ω : ℝ} (hΩ : Ω ≠ 0) :
    ∫ t in (0 : ℝ)..2 * π / Ω, P.c * P.vp Ω t ^ 2 =
      π * P.c * Ω * (P.coefA Ω ^ 2 + P.coefB Ω ^ 2) := by
  set A := P.coefA Ω
  set B := P.coefB Ω
  have key : ∀ t, HasDerivAt (fun t => P.c * Ω * (A ^ 2 * (Ω * t / 2 -
      sin (Ω * t) * cos (Ω * t) / 2) - A * B * (sin (Ω * t) * sin (Ω * t)) +
      B ^ 2 * (Ω * t / 2 + sin (Ω * t) * cos (Ω * t) / 2)))
      (P.c * P.vp Ω t ^ 2) t := by
    intro t
    have hs := ((hasDerivAt_id t).const_mul Ω).sin
    have hc := ((hasDerivAt_id t).const_mul Ω).cos
    have hl := ((hasDerivAt_id t).const_mul Ω).div_const 2
    have h := ((((hl.sub ((hs.mul hc).div_const 2)).const_mul (A ^ 2)).sub
      ((hs.mul hs).const_mul (A * B))).add
      ((hl.add ((hs.mul hc).div_const 2)).const_mul (B ^ 2))).const_mul (P.c * Ω)
    refine h.congr_deriv ?_
    simp only [vp, id, mul_one]
    linear_combination (-(P.c * Ω ^ 2 * (A ^ 2 + B ^ 2) / 2)) * sin_sq_add_cos_sq (Ω * t)
  have hcont : Continuous fun t => P.c * P.vp Ω t ^ 2 := by
    unfold vp; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => key t)
    (hcont.intervalIntegrable _ _)]
  have hT : Ω * (2 * π / Ω) = 2 * π := by field_simp
  simp only [hT, sin_two_pi, cos_two_pi, mul_zero, sin_zero, cos_zero]
  field_simp
  ring

/-- **Power balance**: over one period the work of the driving force on the steady state equals
the energy dissipated by friction, and both equal `(2π/Ω) · ½ c Ω² X²` (average power
`½ c Ω² X²`). -/
theorem power_balance {Ω : ℝ} (hΩ : Ω ≠ 0) (hD : P.denom Ω ≠ 0) :
    ∫ t in (0 : ℝ)..2 * π / Ω, P.F₀ * cos (Ω * t) * P.vp Ω t =
        ∫ t in (0 : ℝ)..2 * π / Ω, P.c * P.vp Ω t ^ 2 ∧
      ∫ t in (0 : ℝ)..2 * π / Ω, P.c * P.vp Ω t ^ 2 =
        2 * π / Ω * (1 / 2 * P.c * Ω ^ 2 * P.amplitude Ω ^ 2) := by
  rw [P.integral_power_input hΩ, P.integral_dissipation hΩ, P.coefA_sq_add_coefB_sq,
    amplitude_sq, P.coefA_sq_add_coefB_sq]
  refine ⟨?_, ?_⟩
  · simp only [coefB]
    field_simp
  · field_simp

end Driven

/-- **Undamped resonance** (`c = 0`, `Ω = ω₀ = √(k/m)`): the secular motion
`x(t) = (F₀/(2mω₀)) t sin ω₀t` solves `m ẍ + k x = F₀ cos ω₀t`. -/
theorem undamped_resonance_solves {m k F₀ : ℝ} (hm : 0 < m) (hk : 0 < k) (t : ℝ) :
    let ω₀ := √(k / m)
    let C := F₀ / (2 * m * ω₀)
    let x := fun t => C * t * sin (ω₀ * t)
    let v := fun t => C * (sin (ω₀ * t) + ω₀ * t * cos (ω₀ * t))
    let a := fun t => C * (2 * ω₀ * cos (ω₀ * t) - ω₀ ^ 2 * t * sin (ω₀ * t))
    HasDerivAt x (v t) t ∧ HasDerivAt v (a t) t ∧ m * a t + k * x t = F₀ * cos (ω₀ * t) := by
  intro ω₀ C x v a
  have hω : 0 < ω₀ := sqrt_pos.mpr (div_pos hk hm)
  have hω2 : ω₀ ^ 2 = k / m := sq_sqrt (div_pos hk hm).le
  have hS := ((hasDerivAt_id t).const_mul ω₀).sin
  have hC := ((hasDerivAt_id t).const_mul ω₀).cos
  have hL := (hasDerivAt_id t).const_mul ω₀
  refine ⟨?_, ?_, ?_⟩
  · refine (((hasDerivAt_id t).const_mul C).mul hS).congr_deriv ?_
    simp only [v, id, mul_one]
    ring
  · refine ((hS.add (hL.mul hC)).const_mul C).congr_deriv ?_
    simp only [a, id, mul_one]
    ring
  · simp only [a, x, C]
    have hk' : k = m * ω₀ ^ 2 := by rw [hω2]; field_simp
    rw [hk']
    field_simp
    ring

/-- The undamped resonant motion is **unbounded** (for `F₀ ≠ 0`). -/
theorem undamped_resonance_unbounded {m k F₀ : ℝ} (hm : 0 < m) (hk : 0 < k) (hF : F₀ ≠ 0)
    (M : ℝ) : ∃ t, M < |F₀ / (2 * m * √(k / m)) * t * sin (√(k / m) * t)| := by
  set ω := √(k / m)
  have hω : 0 < ω := sqrt_pos.mpr (div_pos hk hm)
  set C := F₀ / (2 * m * ω)
  have hC : 0 < |C| := abs_pos.mpr (div_ne_zero hF (by positivity))
  obtain ⟨n, hn⟩ := exists_nat_gt (M * ω / (2 * π * |C|))
  refine ⟨(π / 2 + n * (2 * π)) / ω, ?_⟩
  have ht : ω * ((π / 2 + n * (2 * π)) / ω) = π / 2 + n * (2 * π) := by field_simp
  rw [ht, sin_add_nat_mul_two_pi, sin_pi_div_two, mul_one, abs_mul,
    abs_of_pos (by positivity : 0 < (π / 2 + n * (2 * π)) / ω), mul_div_assoc', lt_div_iff₀ hω]
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith [pi_pos]

/-- **Beats** (`c = 0`, `Ω² ≠ ω₀² = k/m`): `x(t) = (F₀/(m(ω₀² - Ω²)))(cos Ωt - cos ω₀t)` solves
`m ẍ + k x = F₀ cos Ωt` with `x(0) = ẋ(0) = 0`. -/
theorem beats_solves {m k F₀ Ω : ℝ} (hm : 0 < m) (hk : 0 < k) (hΩ : Ω ^ 2 ≠ k / m) (t : ℝ) :
    let ω₀ := √(k / m)
    let K := F₀ / (m * (ω₀ ^ 2 - Ω ^ 2))
    let x := fun t => K * (cos (Ω * t) - cos (ω₀ * t))
    let v := fun t => K * (-Ω * sin (Ω * t) + ω₀ * sin (ω₀ * t))
    HasDerivAt x (v t) t ∧
      HasDerivAt v (K * (-Ω ^ 2 * cos (Ω * t) + ω₀ ^ 2 * cos (ω₀ * t))) t ∧
      m * (K * (-Ω ^ 2 * cos (Ω * t) + ω₀ ^ 2 * cos (ω₀ * t))) + k * x t =
        F₀ * cos (Ω * t) ∧
      x 0 = 0 ∧ v 0 = 0 := by
  intro ω₀ K x v
  have hω2 : ω₀ ^ 2 = k / m := sq_sqrt (div_pos hk hm).le
  have hd : ω₀ ^ 2 - Ω ^ 2 ≠ 0 := by rw [hω2]; exact sub_ne_zero.mpr (Ne.symm hΩ)
  have hSΩ := ((hasDerivAt_id t).const_mul Ω).sin
  have hCΩ := ((hasDerivAt_id t).const_mul Ω).cos
  have hS0 := ((hasDerivAt_id t).const_mul ω₀).sin
  have hC0 := ((hasDerivAt_id t).const_mul ω₀).cos
  refine ⟨?_, ?_, ?_, by simp [x], by simp [v]⟩
  · refine ((hCΩ.sub hC0).const_mul K).congr_deriv ?_
    simp only [v, id, mul_one]
    ring
  · refine (((hSΩ.const_mul (-Ω)).add (hS0.const_mul ω₀)).const_mul K).congr_deriv ?_
    simp only [id, mul_one]
    ring
  · simp only [x, K]
    have hk' : k = m * ω₀ ^ 2 := by rw [hω2]; field_simp
    rw [hk']
    field_simp
    ring

/-- **Beats as a product of sines**:
`K (cos Ωt - cos ω₀t) = 2K sin((ω₀ - Ω)t/2) sin((ω₀ + Ω)t/2)`, a fast oscillation at the mean
frequency modulated by a slow envelope at half the frequency difference. -/
theorem beats_eq_sin_mul_sin (K ω₀ Ω t : ℝ) :
    K * (cos (Ω * t) - cos (ω₀ * t)) =
      2 * K * sin ((ω₀ - Ω) * t / 2) * sin ((ω₀ + Ω) * t / 2) := by
  rw [cos_sub_cos, show (Ω * t + ω₀ * t) / 2 = (ω₀ + Ω) * t / 2 by ring,
    show (Ω * t - ω₀ * t) / 2 = -((ω₀ - Ω) * t / 2) by ring, sin_neg]
  ring

end ClassicalMechanics
