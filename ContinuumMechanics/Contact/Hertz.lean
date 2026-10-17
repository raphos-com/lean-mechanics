import ContinuumMechanics.Elastostatics.Torsion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hertzian contact of elastic spheres and cylinders

Two elastic bodies with smooth convex surfaces (radii of curvature `R₁, R₂`, Young's moduli
`E₁, E₂`, Poisson ratios `ν₁, ν₂`) pressed together by a normal force `P` touch on a small
circular area. Hertz's theory describes the contact through the **effective radius** and the
**effective (contact) modulus**

`1/R = 1/R₁ + 1/R₂`,   `1/E* = (1 - ν₁²)/E₁ + (1 - ν₂²)/E₂`.

For spheres the contact radius, mutual approach, maximum pressure and pressure distribution are

`a = (3PR/(4E*))^{1/3}`,  `δ = a²/R`,  `p₀ = 3P/(2πa²)`,  `p(r) = p₀ √(1 - r²/a²)` (`r ≤ a`).

We take these formulas as given and prove their mathematical consequences. The derivation from
the Boussinesq Green's function of the elastic half-space (showing that the semi-ellipsoidal
pressure produces a parabolic surface displacement) is **out of scope** of this file.

* **Effective quantities** (`effRadius`, `effModulus`): positivity for physical parameters
  (`R₁, R₂, E₁, E₂ > 0`, `-1 < νᵢ < 1`) and `R < R₁, R₂`.
* **Force balance** (`integral_disk_hertz`, `force_balance`): in polar coordinates
  `∫∫_{r ≤ a} p₀ √(1 - r²/a²) = 2π ∫₀ᵃ p₀ √(1 - r²/a²) r dr = (2/3) π a² p₀`, using the
  antiderivative `-(a²/3)(1 - r²/a²)^{3/2}`; hence the Hertz pressure carries the load `P`.
* **Load–approach law** (`load_approach`): `P = (4/3) E* √R δ^{3/2}`.
* **Maximum pressure** (`maxPressure_eq`): `p₀ = (6 P E*² / (π³ R²))^{1/3}`.
* **Scaling** (`contactRadius_smul`, `approach_smul`, `maxPressure_smul`): `a ∝ P^{1/3}`,
  `δ ∝ P^{2/3}`, `p₀ ∝ P^{1/3}`.
* **Contact stiffness** (`hasDerivAt_hertzLoad`, `contact_stiffness`): `dP/dδ = 2 E* a`.
* **Cylinders** (`halfWidth`, `force_balance_cyl`, `lineMaxPressure_sq`): for line contact
  with load `P'` per unit length, `b = √(4P'R/(πE*))`, `p(x) = p₀ √(1 - x²/b²)`,
  `p₀ = 2P'/(πb)`; then `∫_{-b}^{b} p = P'` and `p₀² = P'E*/(πR)`.

## Main results

* `force_balance`: `∫∫_{disk a} p = P`.
* `load_approach`: `P = (4/3) E* √R δ^{3/2}`.
* `maxPressure_eq`: `p₀ = (6 P E*² / (π³ R²))^{1/3}`.
* `contactRadius_smul`, `approach_smul`, `maxPressure_smul`: power-law scaling in `P`.
* `contact_stiffness`: `dP/dδ = 2 E* a`.
* `force_balance_cyl`: `∫_{-b}^{b} p₀ √(1 - x²/b²) dx = P'`.

## References

* [Johnson1985] K. L. Johnson, *Contact Mechanics*, Cambridge University Press, Ch. 4.
* [Hertz1882] H. Hertz, *Über die Berührung fester elastischer Körper*, J. reine angew. Math. 92.
* [Timoshenko1970] S. P. Timoshenko, J. N. Goodier, *Theory of Elasticity*, §140.
-/

open MeasureTheory Real

noncomputable section

namespace ContinuumMechanics.Contact

open ContinuumMechanics.Torsion

/-! ### Effective quantities -/

section Effective

/-- The **effective radius** `R = (1/R₁ + 1/R₂)⁻¹`. -/
def effRadius (R₁ R₂ : ℝ) : ℝ := (R₁⁻¹ + R₂⁻¹)⁻¹

/-- The **effective contact modulus** `E* = ((1 - ν₁²)/E₁ + (1 - ν₂²)/E₂)⁻¹`. -/
def effModulus (E₁ ν₁ E₂ ν₂ : ℝ) : ℝ := ((1 - ν₁ ^ 2) / E₁ + (1 - ν₂ ^ 2) / E₂)⁻¹

/-- The defining relation `1/R = 1/R₁ + 1/R₂`. -/
theorem inv_effRadius (R₁ R₂ : ℝ) : (effRadius R₁ R₂)⁻¹ = R₁⁻¹ + R₂⁻¹ := inv_inv _

/-- The defining relation `1/E* = (1 - ν₁²)/E₁ + (1 - ν₂²)/E₂`. -/
theorem inv_effModulus (E₁ ν₁ E₂ ν₂ : ℝ) :
    (effModulus E₁ ν₁ E₂ ν₂)⁻¹ = (1 - ν₁ ^ 2) / E₁ + (1 - ν₂ ^ 2) / E₂ := inv_inv _

/-- The effective radius of two convex bodies is positive. -/
theorem effRadius_pos {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) : 0 < effRadius R₁ R₂ := by
  unfold effRadius; positivity

/-- The effective radius is smaller than the first radius. -/
theorem effRadius_lt_left {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) : effRadius R₁ R₂ < R₁ := by
  unfold effRadius
  rw [inv_lt_comm₀ (by positivity) h₁]
  linarith [inv_pos.2 h₂]

/-- The effective radius is symmetric. -/
theorem effRadius_comm (R₁ R₂ : ℝ) : effRadius R₁ R₂ = effRadius R₂ R₁ := by
  simp only [effRadius, add_comm]

/-- The effective radius is smaller than the second radius. -/
theorem effRadius_lt_right {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) : effRadius R₁ R₂ < R₂ := by
  rw [effRadius_comm]; exact effRadius_lt_left h₂ h₁

/-- The effective modulus is positive for physical parameters `Eᵢ > 0`, `-1 < νᵢ < 1`. -/
theorem effModulus_pos {E₁ ν₁ E₂ ν₂ : ℝ} (hE₁ : 0 < E₁) (hE₂ : 0 < E₂) (hν₁ : |ν₁| < 1)
    (hν₂ : |ν₂| < 1) : 0 < effModulus E₁ ν₁ E₂ ν₂ := by
  have h₁ : 0 < 1 - ν₁ ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one ν₁).2 hν₁; linarith
  have h₂ : 0 < 1 - ν₂ ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one ν₂).2 hν₂; linarith
  unfold effModulus; positivity

end Effective

/-! ### Real powers -/

section Pow

/-- The cube of a cube root: `(x^{1/3})³ = x` for `x ≥ 0`. -/
theorem cbrt_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← rpow_natCast, ← rpow_mul hx]; norm_num

/-- The cube root of a cube: `(x³)^{1/3} = x` for `x ≥ 0`. -/
theorem pow_three_cbrt {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ (1 / 3 : ℝ) = x := by
  rw [← rpow_natCast, ← rpow_mul hx]; norm_num

end Pow

/-! ### The Hertz solution for spheres -/

section Sphere

variable {P R E : ℝ}

/-- The **Hertz contact radius** `a = (3PR/(4E*))^{1/3}`. -/
def contactRadius (P R E : ℝ) : ℝ := (3 * P * R / (4 * E)) ^ (1 / 3 : ℝ)

/-- The **mutual approach** of distant points `δ = a²/R`. -/
def approach (P R E : ℝ) : ℝ := contactRadius P R E ^ 2 / R

/-- The **maximum contact pressure** `p₀ = 3P/(2πa²)` (at the centre of the contact). -/
def maxPressure (P R E : ℝ) : ℝ := 3 * P / (2 * π * contactRadius P R E ^ 2)

/-- The **Hertz pressure** `p₀ √(1 - (x₁² + x₂²)/a²)` at the point `q = (x₁, x₂)`. -/
def hertzPressure (p₀ a : ℝ) (q : ℝ × ℝ) : ℝ := p₀ * √(1 - (q.1 ^ 2 + q.2 ^ 2) / a ^ 2)

/-- The cube of the contact radius: `a³ = 3PR/(4E*)`. -/
theorem contactRadius_pow_three (hP : 0 ≤ P) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    contactRadius P R E ^ 3 = 3 * P * R / (4 * E) :=
  cbrt_pow_three (by positivity)

/-- The contact radius is positive. -/
theorem contactRadius_pos (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) : 0 < contactRadius P R E :=
  rpow_pos_of_pos (by positivity) _

/-- The radial antiderivative: `d/dr [-(a²/3)(1 - r²/a²)^{3/2}] = r √(1 - r²/a²)`. -/
theorem hasDerivAt_hertz_antideriv (a r : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun r => -(a ^ 2 / 3) * (1 - r ^ 2 / a ^ 2) ^ (3 / 2 : ℝ))
      (r * √(1 - r ^ 2 / a ^ 2)) r := by
  have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2 / a ^ 2) (-(2 * r / a ^ 2)) r := by
    have := ((hasDerivAt_pow 2 r).div_const (a ^ 2)).const_sub 1
    convert this using 1; push_cast; ring
  have h2 := (h1.rpow_const (p := 3 / 2) (Or.inr (by norm_num))).const_mul (-(a ^ 2 / 3))
  convert h2 using 1
  rw [sqrt_eq_rpow]
  norm_num
  field_simp

/-- The radial integral `∫₀ᵃ r √(1 - r²/a²) dr = a²/3`. -/
theorem integral_radial_hertz {a : ℝ} (ha : 0 < a) :
    ∫ r in (0 : ℝ)..a, r * √(1 - r ^ 2 / a ^ 2) = a ^ 2 / 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_hertz_antideriv a r ha.ne')
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : (1 : ℝ) - a ^ 2 / a ^ 2 = 0 := by field_simp; ring
  simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
    one_rpow]
  rw [zero_rpow (by norm_num)]
  ring

/-- The **Hertz pressure integral** over the contact disk:
`∫∫_{disk a} p₀ √(1 - r²/a²) = (2/3) π a² p₀`, computed in polar coordinates. -/
theorem integral_disk_hertz (p₀ : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ q in disk a, hertzPressure p₀ a q = 2 / 3 * π * a ^ 2 * p₀ := by
  rw [← integral_indicator (measurableSet_disk a), ← integral_comp_polarCoord_symm]
  have key : ∀ q ∈ polarCoord.target, q.1 • (disk a).indicator (hertzPressure p₀ a)
      (polarCoord.symm q) = (Set.Iic a).indicator (fun r => p₀ * (r * √(1 - r ^ 2 / a ^ 2)))
        q.1 * (fun _ => (1 : ℝ)) q.2 :=
    fun q hq => by
    have h1 : 0 < q.1 := hq.1
    have hs : (q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2 = q.1 ^ 2 := by
      have := sin_sq_add_cos_sq q.2
      linear_combination q.1 ^ 2 * this
    by_cases h : q.1 ≤ a
    · have hd : polarCoord.symm q ∈ disk a := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs]
        exact pow_le_pow_left₀ h1.le h 2
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem (Set.mem_Iic.mpr h)]
      simp only [hertzPressure, polarCoord_symm_apply, smul_eq_mul, hs]
      ring
    · have hd : polarCoord.symm q ∉ disk a := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs, not_le]
        exact pow_lt_pow_left₀ (lt_of_not_ge h) ha.le two_ne_zero
      rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (by simpa using h)]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key]
  have hp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    ((Set.Iic a).indicator (fun r => p₀ * (r * √(1 - r ^ 2 / a ^ 2)))) (fun _ => (1 : ℝ))
    (Set.Ioi 0) (Set.Ioo (-π) π)
  rw [← Measure.volume_eq_prod] at hp
  change ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π, _ = _
  rw [hp, setIntegral_indicator measurableSet_Iic,
    Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_const_mul, integral_radial_hertz ha]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo]
  rw [max_eq_left (by linarith [pi_pos])]
  ring

/-- **Force balance**: the Hertz pressure with `p₀ = 3P/(2πa²)` integrates over the contact
disk to the applied load, `∫∫_{disk a} p = P`. -/
theorem force_balance (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) :
    ∫ q in disk (contactRadius P R E),
      hertzPressure (maxPressure P R E) (contactRadius P R E) q = P := by
  have ha := contactRadius_pos hP hR hE
  rw [integral_disk_hertz _ ha, maxPressure]
  field_simp

/-- The **load–approach law** `P = (4/3) E* √R δ^{3/2}`. -/
theorem load_approach (hP : 0 ≤ P) (hR : 0 < R) (hE : 0 < E) :
    P = 4 / 3 * E * √R * approach P R E ^ (3 / 2 : ℝ) := by
  set a := contactRadius P R E
  have ha : 0 ≤ a := rpow_nonneg (by positivity) _
  have h3 : a ^ 3 = 3 * P * R / (4 * E) := contactRadius_pow_three hP hR.le hE.le
  have hsR : 0 < √R := sqrt_pos.2 hR
  have hδ : approach P R E = (a / √R) ^ 2 := by
    rw [approach, div_pow, sq_sqrt hR.le]
  have hpow : approach P R E ^ (3 / 2 : ℝ) = (a / √R) ^ 3 := by
    rw [hδ, ← rpow_natCast, ← rpow_mul (by positivity), ← rpow_natCast]; norm_num
  rw [hpow, div_pow]
  have : √R ^ 3 = R * √R := by rw [pow_succ, sq_sqrt hR.le]
  rw [this, h3]
  field_simp

/-- The maximum pressure in terms of the load: `p₀ = (6 P E*² / (π³ R²))^{1/3}`. -/
theorem maxPressure_eq (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) :
    maxPressure P R E = (6 * P * E ^ 2 / (π ^ 3 * R ^ 2)) ^ (1 / 3 : ℝ) := by
  have ha := contactRadius_pos hP hR hE
  have h3 := contactRadius_pow_three hP.le hR.le hE.le
  have hp : 0 ≤ maxPressure P R E := by unfold maxPressure; positivity
  rw [← pow_three_cbrt hp]
  congr 1
  rw [maxPressure, div_pow, mul_pow, mul_pow, ← pow_mul,
    show contactRadius P R E ^ (2 * 3) = (contactRadius P R E ^ 3) ^ 2 by ring, h3]
  field_simp
  ring

/-- **Scaling of the contact radius**: `a(λP) = λ^{1/3} a(P)`. -/
theorem contactRadius_smul {l : ℝ} (hl : 0 ≤ l) (hP : 0 ≤ P) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    contactRadius (l * P) R E = l ^ (1 / 3 : ℝ) * contactRadius P R E := by
  rw [contactRadius, contactRadius, ← mul_rpow hl (by positivity)]
  congr 1; ring

/-- **Scaling of the approach**: `δ(λP) = λ^{2/3} δ(P)`. -/
theorem approach_smul {l : ℝ} (hl : 0 ≤ l) (hP : 0 ≤ P) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    approach (l * P) R E = l ^ (2 / 3 : ℝ) * approach P R E := by
  rw [approach, approach, contactRadius_smul hl hP hR hE, mul_pow, ← rpow_natCast,
    ← rpow_mul hl]
  norm_num; ring

/-- **Scaling of the maximum pressure**: `p₀(λP) = λ^{1/3} p₀(P)`. -/
theorem maxPressure_smul {l : ℝ} (hl : 0 < l) (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) :
    maxPressure (l * P) R E = l ^ (1 / 3 : ℝ) * maxPressure P R E := by
  have ha := contactRadius_pos hP hR hE
  have hl3 : 0 < l ^ (1 / 3 : ℝ) := rpow_pos_of_pos hl _
  have hcube : (l ^ (1 / 3 : ℝ)) ^ 3 = l := cbrt_pow_three hl.le
  rw [maxPressure, maxPressure, contactRadius_smul hl.le hP.le hR.le hE.le]
  generalize l ^ (1 / 3 : ℝ) = c at hl3 hcube ⊢
  subst hcube
  field_simp

/-- The **Hertz load** as a function of the approach, `P(δ) = (4/3) E* √R δ^{3/2}`. -/
def hertzLoad (R E δ : ℝ) : ℝ := 4 / 3 * E * √R * δ ^ (3 / 2 : ℝ)

/-- Derivative of the load–approach law: `dP/dδ = 2 E* √R √δ`. -/
theorem hasDerivAt_hertzLoad (R E δ : ℝ) :
    HasDerivAt (hertzLoad R E) (2 * E * √R * √δ) δ := by
  unfold hertzLoad
  have h := (hasDerivAt_rpow_const (x := δ) (p := 3 / 2) (Or.inr (by norm_num))).const_mul
    (4 / 3 * E * √R)
  convert h using 1
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← sqrt_eq_rpow]
  ring

/-- The **contact stiffness** `dP/dδ = 2 E* a` at the Hertz approach `δ = a²/R`. -/
theorem contact_stiffness (hP : 0 ≤ P) (hR : 0 < R) (hE : 0 ≤ E) :
    HasDerivAt (hertzLoad R E) (2 * E * contactRadius P R E) (approach P R E) := by
  convert hasDerivAt_hertzLoad R E (approach P R E) using 1
  have ha : 0 ≤ contactRadius P R E := rpow_nonneg (by positivity) _
  rw [approach, sqrt_div' _ hR.le, sqrt_sq ha]
  have : 0 < √R := sqrt_pos.2 hR
  field_simp

/-- The Hertz load at the Hertz approach is the applied load. -/
theorem hertzLoad_approach (hP : 0 ≤ P) (hR : 0 < R) (hE : 0 < E) :
    hertzLoad R E (approach P R E) = P :=
  (load_approach hP hR hE).symm

end Sphere

/-! ### Line contact of cylinders -/

section Cylinder

variable {P R E : ℝ}

/-- The **half-width** of the contact strip of two cylinders, `b = √(4P'R/(πE*))`, for the load
`P'` per unit length. -/
def halfWidth (P R E : ℝ) : ℝ := √(4 * P * R / (π * E))

/-- The maximum pressure of the line contact, `p₀ = 2P'/(πb)`. -/
def lineMaxPressure (P R E : ℝ) : ℝ := 2 * P / (π * halfWidth P R E)

/-- The **line-contact pressure** `p(x) = p₀ √(1 - x²/b²)`. -/
def linePressure (p₀ b x : ℝ) : ℝ := p₀ * √(1 - x ^ 2 / b ^ 2)

/-- The half-width is positive. -/
theorem halfWidth_pos (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) : 0 < halfWidth P R E :=
  sqrt_pos.2 (by positivity)

/-- The square of the half-width: `b² = 4P'R/(πE*)`. -/
theorem halfWidth_sq (hP : 0 ≤ P) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    halfWidth P R E ^ 2 = 4 * P * R / (π * E) :=
  sq_sqrt (by positivity)

/-- The elliptic pressure integral `∫_{-b}^{b} p₀ √(1 - x²/b²) dx = π b p₀ / 2`. -/
theorem integral_linePressure (p₀ : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ x in -b..b, linePressure p₀ b x = π * b * p₀ / 2 := by
  have h : ∀ x : ℝ, linePressure p₀ b x = p₀ * (fun y : ℝ => √(1 - y ^ 2)) (x / b) := fun x => by
    simp only [linePressure, div_pow]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun y => √(1 - y ^ 2)) hb.ne',
    neg_div, div_self hb.ne', integral_sqrt_one_sub_sq, smul_eq_mul]
  ring

/-- **Force balance for cylinders**: `∫_{-b}^{b} p(x) dx = P'`. -/
theorem force_balance_cyl (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) :
    ∫ x in -halfWidth P R E..halfWidth P R E,
      linePressure (lineMaxPressure P R E) (halfWidth P R E) x = P := by
  have hb := halfWidth_pos hP hR hE
  rw [integral_linePressure _ hb, lineMaxPressure]
  field_simp

/-- The maximum line-contact pressure in terms of the load: `p₀² = P'E*/(πR)`. -/
theorem lineMaxPressure_sq (hP : 0 < P) (hR : 0 < R) (hE : 0 < E) :
    lineMaxPressure P R E ^ 2 = P * E / (π * R) := by
  rw [lineMaxPressure, div_pow, mul_pow, mul_pow, halfWidth_sq hP.le hR.le hE.le]
  field_simp
  ring

end Cylinder

end ContinuumMechanics.Contact
