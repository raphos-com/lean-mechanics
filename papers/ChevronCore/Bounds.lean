import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Transverse shear stiffness of chevron folded cores: analytical bounds

Formalization of the closed-form results of [LebeeSab2010] on the transverse shear moduli
`G₁₃`, `G₂₃` of a chevron folded core (member angle `δ`, closure angle `φ`, wall thickness `t`,
side `a₀`, wall material `E_s`, `ν_s`, `G_s = E_s / (2(1 + ν_s))`). The moduli are normalized by
the relative density `ρ = t / (a₀ sin φ sin δ cos δ)` (eq. 15): `𝓔_α = G_α3 / (ρ G_s)` (eq. 14).

* `normalize_lower`: the lower bound `G₁₃⁻ = (t / a₀) E_s sin δ cos δ / sin φ` normalizes to
  `𝓔₁⁻ = 2(1 + ν) sin²δ cos²δ`.
* `lowerE1_le`, `lowerE1_quarter`: `𝓔₁⁻ ≤ (1 + ν)/2`, with equality for `δ = π/4`
  ("maximum for `δ = π/4` as for Warren truss beams").
* `lowerE1_le_upperE1`: the analytical bounds are ordered, `𝓔₁⁻ ≤ 𝓔₁⁺` (eq. 21), for every
  `ν < 1`, with `𝓔₁⁺ = 2/(1 - ν) sin²δ cos²δ sin⁴φ + cos²φ`.
* `exact_quarter`: for `δ = π/4` and `cos²φ = ν` the bounds coincide, `𝓔₁⁻ = 𝓔₁⁺ = (1 + ν)/2`:
  the piecewise uniform fields are exact.
* `upperE2_prismatic`: for the prismatic pattern `φ = π/2`, `𝓔₂⁺ = sin²δ`.
* `upper_sum`: `𝓔₁⁺ + 𝓔₂⁺ = R⁺(cos²δ sin²φ)` with `R⁺(x) = (2x/(1 - ν) + 1)(1 - x)` (eq. 23).
* `Rplus_le`, `Rplus_max`: `R⁺ ≤ (3 - ν)²/(8(1 - ν))`, attained at `x = (1 + ν)/4` (eqs. 24–25),
  and the maximum is reached by actual geometries (`exists_max_geometry`).
* `honeycomb_sum`, `chevron_beats_honeycomb`: the upper bounds of hexagonal honeycombs
  `(1 + cos²θ)/2`, `sin²θ/2` (eq. 22) always sum to `1`, while the chevron maximum exceeds `1` by
  `(1 + ν)²/(8(1 - ν))`; for `ν = 0.4` it is `≥ 1.4` ("≈ 40%").

## References

* [LebeeSab2010] A. Lebée, K. Sab, *Transverse shear stiffness of a chevron folded core used in
  sandwich construction*, Int. J. Solids Struct. 47, 2620–2629 (2010).
* [Kelsey1958] S. Kelsey, R. Gellatly, B. Clark, *The shear modulus of foil honeycomb cores*,
  Aircraft Eng. 30 (1958).
-/

open Real

noncomputable section

namespace ContinuumMechanics.ChevronCore

/-- Normalized lower bound in direction 1, `𝓔₁⁻ = 2(1 + ν) sin²δ cos²δ`. -/
def lowerE1 (ν δ : ℝ) : ℝ := 2 * (1 + ν) * (sin δ ^ 2 * cos δ ^ 2)

/-- Normalized upper bound in direction 1, `𝓔₁⁺ = 2/(1 - ν) sin²δ cos²δ sin⁴φ + cos²φ`. -/
def upperE1 (ν δ φ : ℝ) : ℝ := 2 / (1 - ν) * (sin δ ^ 2 * cos δ ^ 2) * sin φ ^ 4 + cos φ ^ 2

/-- Normalized upper bound in direction 2, `𝓔₂⁺ = 2/(1 - ν) cos²δ cos²φ sin²φ + sin²δ sin²φ`. -/
def upperE2 (ν δ φ : ℝ) : ℝ :=
  2 / (1 - ν) * cos δ ^ 2 * cos φ ^ 2 * sin φ ^ 2 + sin δ ^ 2 * sin φ ^ 2

/-- Relative density of the core, `ρ = t / (a₀ sin φ sin δ cos δ)` (eq. 15). -/
def density (t a₀ δ φ : ℝ) : ℝ := t / (a₀ * sin φ * sin δ * cos δ)

/-- The lower bound `G₁₃⁻ = (t / a₀) E_s sin δ cos δ / sin φ`. -/
def G13lower (Es t a₀ δ φ : ℝ) : ℝ := t / a₀ * Es * sin δ * cos δ / sin φ

/-- `G₁₃⁻ / (ρ G_s) = 𝓔₁⁻` with `G_s = E_s / (2(1 + ν))`. -/
theorem normalize_lower {Es ν t a₀ δ φ : ℝ} (hE : Es ≠ 0) (hν : 1 + ν ≠ 0) (ht : t ≠ 0)
    (ha : a₀ ≠ 0) (hφ : sin φ ≠ 0) (hs : sin δ ≠ 0) (hc : cos δ ≠ 0) :
    G13lower Es t a₀ δ φ / (density t a₀ δ φ * (Es / (2 * (1 + ν)))) = lowerE1 ν δ := by
  simp only [G13lower, density, lowerE1]
  field_simp

/-- `sin²δ cos²δ ≤ 1/4`. -/
theorem sin_sq_mul_cos_sq_le (δ : ℝ) : sin δ ^ 2 * cos δ ^ 2 ≤ 1 / 4 := by
  nlinarith [sin_sq_add_cos_sq δ, sq_nonneg (sin δ ^ 2 - cos δ ^ 2)]

theorem sin_sq_mul_cos_sq_quarter : sin (π / 4) ^ 2 * cos (π / 4) ^ 2 = 1 / 4 := by
  rw [sin_pi_div_four, cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `𝓔₁⁻ ≤ (1 + ν)/2`. -/
theorem lowerE1_le {ν : ℝ} (hν : -1 ≤ ν) (δ : ℝ) : lowerE1 ν δ ≤ (1 + ν) / 2 := by
  unfold lowerE1
  nlinarith [sin_sq_mul_cos_sq_le δ]

/-- The maximum `(1 + ν)/2` of `𝓔₁⁻` is attained at the member angle `δ = π/4`. -/
theorem lowerE1_quarter (ν : ℝ) : lowerE1 ν (π / 4) = (1 + ν) / 2 := by
  rw [lowerE1, sin_sq_mul_cos_sq_quarter]
  ring

/-- **The bounds are ordered** (eq. 21): `𝓔₁⁻ ≤ 𝓔₁⁺` for `ν < 1`. With `S = sin²δ cos²δ` and
`y = sin²φ`, `(1 - ν)(𝓔₁⁺ - 𝓔₁⁻) = (1 - 4S)(1 - ν)(1 - y) + 2S(y - 1 + ν)²`. -/
theorem lowerE1_le_upperE1 {ν : ℝ} (hν : ν < 1) (δ φ : ℝ) : lowerE1 ν δ ≤ upperE1 ν δ φ := by
  have h1 : 0 < 1 - ν := by linarith
  set S := sin δ ^ 2 * cos δ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hS1 : S ≤ 1 / 4 := sin_sq_mul_cos_sq_le δ
  have hy : sin φ ^ 2 ≤ 1 := sin_sq_le_one φ
  have hc : cos φ ^ 2 = 1 - sin φ ^ 2 := by rw [cos_sq']
  have key : (1 - ν) * (upperE1 ν δ φ - lowerE1 ν δ) =
      (1 - 4 * S) * (1 - ν) * (1 - sin φ ^ 2) + 2 * S * (sin φ ^ 2 - 1 + ν) ^ 2 := by
    simp only [upperE1, lowerE1, ← hS, hc]
    field_simp
    ring
  have : 0 ≤ (1 - ν) * (upperE1 ν δ φ - lowerE1 ν δ) := by
    rw [key]
    have : 0 ≤ (1 - 4 * S) * (1 - ν) * (1 - sin φ ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) h1.le) (by linarith)
    positivity
  nlinarith

/-- **Exact solution**: for `δ = π/4` and `cos²φ = ν` the bounds coincide at `(1 + ν)/2`. -/
theorem exact_quarter {ν φ : ℝ} (hν : ν < 1) (hφ : cos φ ^ 2 = ν) :
    lowerE1 ν (π / 4) = (1 + ν) / 2 ∧ upperE1 ν (π / 4) φ = (1 + ν) / 2 := by
  refine ⟨lowerE1_quarter ν, ?_⟩
  have h1 : 1 - ν ≠ 0 := by linarith
  have hs : sin φ ^ 2 = 1 - ν := by rw [sin_sq, hφ]
  rw [upperE1, sin_sq_mul_cos_sq_quarter, hφ, show sin φ ^ 4 = (sin φ ^ 2) ^ 2 by ring, hs]
  field_simp
  ring

/-- For the prismatic pattern `φ = π/2`, `𝓔₂⁺ = sin²δ`. -/
theorem upperE2_prismatic (ν δ : ℝ) : upperE2 ν δ (π / 2) = sin δ ^ 2 := by
  simp [upperE2]

/-- `R⁺(x) = (2x/(1 - ν) + 1)(1 - x)` (eq. 23). -/
def Rplus (ν x : ℝ) : ℝ := (2 * x / (1 - ν) + 1) * (1 - x)

/-- `𝓔₁⁺ + 𝓔₂⁺ = R⁺(cos²δ sin²φ)`. -/
theorem upper_sum (ν δ φ : ℝ) (hν : ν ≠ 1) :
    upperE1 ν δ φ + upperE2 ν δ φ = Rplus ν (cos δ ^ 2 * sin φ ^ 2) := by
  have h1 : 1 - ν ≠ 0 := sub_ne_zero.mpr (Ne.symm hν)
  have hc : cos φ ^ 2 = 1 - sin φ ^ 2 := by rw [cos_sq']
  have hs : sin δ ^ 2 = 1 - cos δ ^ 2 := by rw [sin_sq]
  simp only [upperE1, upperE2, Rplus, hc, hs]
  field_simp
  ring

/-- `R⁺ ≤ (3 - ν)²/(8(1 - ν))` (eq. 24). -/
theorem Rplus_le {ν : ℝ} (hν : ν < 1) (x : ℝ) : Rplus ν x ≤ (3 - ν) ^ 2 / (8 * (1 - ν)) := by
  have h1 : 0 < 1 - ν := by linarith
  rw [Rplus, div_add_one h1.ne', div_mul_eq_mul_div, div_le_div_iff₀ h1 (by positivity)]
  nlinarith [sq_nonneg (4 * x - 1 - ν)]

/-- The maximum is attained at `x = (1 + ν)/4` (eq. 25). -/
theorem Rplus_max {ν : ℝ} (hν : ν < 1) :
    Rplus ν ((1 + ν) / 4) = (3 - ν) ^ 2 / (8 * (1 - ν)) := by
  have h1 : 1 - ν ≠ 0 := by linarith
  rw [Rplus]
  field_simp
  ring

/-- The optimum `cos²δ sin²φ = (1 + ν)/4` is realized by the prismatic pattern `φ = π/2` with a
member angle `δ = arccos(√((1 + ν)/4))` in `(0, π/2)`, for `-1 < ν < 1`. -/
theorem exists_max_geometry {ν : ℝ} (hν₀ : -1 < ν) (hν₁ : ν < 1) :
    ∃ δ ∈ Set.Ioo 0 (π / 2), cos δ ^ 2 * sin (π / 2) ^ 2 = (1 + ν) / 4 := by
  set c := √((1 + ν) / 4)
  have hc0 : 0 < c := sqrt_pos.mpr (by linarith)
  have hc1 : c < 1 := (sqrt_lt' one_pos).mpr (by linarith)
  refine ⟨arccos c, ⟨arccos_pos.mpr hc1, arccos_lt_pi_div_two.mpr hc0⟩, ?_⟩
  rw [cos_arccos (by linarith) hc1.le, sin_pi_div_two, one_pow, mul_one,
    sq_sqrt (by linarith)]

/-- Hexagonal honeycomb upper bounds (eq. 22) sum to `1` for every angle `θ`. -/
theorem honeycomb_sum (θ : ℝ) : (1 + cos θ ^ 2) / 2 + sin θ ^ 2 / 2 = 1 := by
  have := sin_sq_add_cos_sq θ
  linarith

/-- **Chevron cores can outperform honeycombs**: the maximal `R⁺` exceeds the honeycomb value
`1` by `(1 + ν)²/(8(1 - ν))`, which is positive for `-1 < ν < 1`. -/
theorem chevron_beats_honeycomb {ν : ℝ} (hν₀ : -1 < ν) (hν₁ : ν < 1) :
    (3 - ν) ^ 2 / (8 * (1 - ν)) - 1 = (1 + ν) ^ 2 / (8 * (1 - ν)) ∧
      1 < (3 - ν) ^ 2 / (8 * (1 - ν)) := by
  have h1 : 0 < 1 - ν := by linarith
  have e : (3 - ν) ^ 2 / (8 * (1 - ν)) - 1 = (1 + ν) ^ 2 / (8 * (1 - ν)) := by
    field_simp
    ring
  refine ⟨e, ?_⟩
  have : 0 < (1 + ν) ^ 2 / (8 * (1 - ν)) := by
    have : 0 < 1 + ν := by linarith
    positivity
  linarith

/-- For `ν_s = 0.4` the chevron pattern can outperform honeycombs by about 40%. -/
theorem forty_percent : (7 / 5 : ℝ) < (3 - 2 / 5) ^ 2 / (8 * (1 - 2 / 5)) := by
  norm_num

end ContinuumMechanics.ChevronCore
