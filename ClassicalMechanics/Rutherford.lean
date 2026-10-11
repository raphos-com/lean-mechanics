import ClassicalMechanics.Kepler
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Rutherford scattering

We study unbound (`E > 0`) Kepler orbits `m ẍ = -(k / r³) x` (see `ClassicalMechanics.Kepler`),
for an attractive (`k > 0`) or repulsive (`k < 0`) inverse-square force, and derive the
classical results of Rutherford scattering.

* **Hyperbolic orbits** (`lrl_sq_gt`, `one_lt_hypEcc`): if `E > 0`, `L ≠ 0` and `k ≠ 0`, then
  `|A|² > m² k²`, i.e. the eccentricity `e = |A| / (m |k|)` exceeds `1`; moreover
  `e² = 1 + 2 E |L|² / (m k²)` (`hypEcc_sq`).
* **The orbit lies in a cone around `A`** (`lrl_dot_gt`, `cos_angle_gt`): from the orbit equation
  `A · x + m k r = |L|² > 0`, the angle `θ` between `x` and `A` satisfies
  `cos θ > -m k / |A|`, i.e. `cos θ > -1/e` in the attractive case and `cos θ > 1/e` in the
  repulsive case. The asymptotic directions are `cos θ∞ = -1/e` (`asymptoteAngle`).
* **Deflection angle**: `Θ = 2 θ∞ - π = 2 arcsin (1/e)` (`two_asymptoteAngle_sub_pi`), so that
  `sin (Θ/2) = 1/e` (`sin_half_deflectionAngle`), `0 < Θ < π` (`deflectionAngle_pos`,
  `deflectionAngle_lt_pi`) and `tan (Θ/2) = 1 / √(e² - 1)` (`tan_half_deflectionAngle`).
* **Rutherford's relation** (`rutherford_tan`): with the impact parameter
  `b = |L| / √(2 m E)` (since `|L| = m v∞ b` and `E = ½ m v∞²`),
  `tan (Θ/2) = |k| / (2 E b)`; for a Kepler motion this is `KeplerMotion.rutherford_tan`.
* **Rutherford cross section** (`hasDerivAt_impactOfAngle`, `rutherford_cross_section`): with
  `b(Θ) = (|k| / (2E)) cot (Θ/2)`, one has `db/dΘ = -|k| / (4 E sin² (Θ/2))` and
  `dσ/dΩ = (b / sin Θ) |db/dΘ| = (k / (4E))² / sin⁴ (Θ/2)`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.10–3.11.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §§18–19.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

namespace Rutherford

/-- The eccentricity `e = √(1 + 2 E ℓ² / (m k²))` of a Kepler orbit with mass `m`, force constant
`k`, energy `E` and squared angular momentum `ℓ² = L2`. -/
def ecc (m k E L2 : ℝ) : ℝ := √(1 + 2 * E * L2 / (m * k ^ 2))

/-- The polar angle `θ∞ = arccos (-1/e)` of the asymptotes of a hyperbolic orbit, measured from
the LRL vector: there `1 + e cos θ∞ = 0`. -/
def asymptoteAngle (e : ℝ) : ℝ := arccos (-1 / e)

/-- The **deflection (scattering) angle** `Θ = 2 arcsin (1/e)` of a hyperbolic orbit. -/
def deflectionAngle (e : ℝ) : ℝ := 2 * arcsin (1 / e)

/-- The **impact parameter** `b = ℓ / √(2 m E)`, where `ℓ = √L2` is the angular momentum. -/
def impactParam (m E L2 : ℝ) : ℝ := √L2 / √(2 * m * E)

/-- The impact parameter as a function of the deflection angle,
`b(Θ) = (|k| / (2E)) cot (Θ/2)`. -/
def impactOfAngle (k E Θ : ℝ) : ℝ := |k| / (2 * E) * (cos (Θ / 2) / sin (Θ / 2))

/-- The Rutherford differential cross section `dσ/dΩ = (b / sin Θ) |db/dΘ|`, given `b` and
`db/dΘ`. -/
def crossSection (Θ b db : ℝ) : ℝ := b / sin Θ * |db|

/-- The asymptotes satisfy `1 + e cos θ∞ = 0`. -/
theorem one_add_mul_cos_asymptoteAngle {e : ℝ} (he : 1 ≤ e) :
    1 + e * cos (asymptoteAngle e) = 0 := by
  have he0 : 0 < e := by linarith
  have h1 : 1 / e ≤ 1 := by rw [div_le_one he0]; exact he
  have h2 : 0 ≤ 1 / e := by positivity
  rw [asymptoteAngle, cos_arccos (by rw [neg_div]; linarith) (by rw [neg_div]; linarith)]
  field_simp
  ring

/-- The deflection angle is `Θ = 2 θ∞ - π`. -/
theorem two_asymptoteAngle_sub_pi (e : ℝ) :
    2 * asymptoteAngle e - π = deflectionAngle e := by
  rw [asymptoteAngle, deflectionAngle, neg_div, arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  ring

/-- `sin (Θ/2) = 1/e`. -/
theorem sin_half_deflectionAngle {e : ℝ} (he : 1 ≤ e) : sin (deflectionAngle e / 2) = 1 / e := by
  have he0 : 0 < e := by linarith
  have h1 : 1 / e ≤ 1 := by rw [div_le_one he0]; exact he
  have h2 : 0 ≤ 1 / e := by positivity
  rw [deflectionAngle, mul_div_cancel_left₀ _ two_ne_zero, sin_arcsin (by linarith) h1]

/-- For a hyperbola (`e > 1`), the deflection angle is positive. -/
theorem deflectionAngle_pos {e : ℝ} (he : 1 < e) : 0 < deflectionAngle e := by
  have : 0 < arcsin (1 / e) := arcsin_pos.mpr (by positivity)
  rw [deflectionAngle]; linarith

/-- For a hyperbola (`e > 1`), the deflection angle is less than `π`. -/
theorem deflectionAngle_lt_pi {e : ℝ} (he : 1 < e) : deflectionAngle e < π := by
  have : arcsin (1 / e) < π / 2 :=
    arcsin_lt_pi_div_two.mpr (by rw [div_lt_one (by linarith)]; exact he)
  rw [deflectionAngle]; linarith

/-- `tan (Θ/2) = 1 / √(e² - 1)`. -/
theorem tan_half_deflectionAngle {e : ℝ} (he : 1 < e) :
    tan (deflectionAngle e / 2) = 1 / √(e ^ 2 - 1) := by
  have he0 : 0 < e := by linarith
  rw [deflectionAngle, mul_div_cancel_left₀ _ two_ne_zero, tan_arcsin]
  have h : 1 - (1 / e) ^ 2 = (e ^ 2 - 1) / e ^ 2 := by field_simp
  rw [h, sqrt_div' _ (by positivity), sqrt_sq he0.le]
  have : 0 < √(e ^ 2 - 1) := sqrt_pos.mpr (by nlinarith)
  field_simp

/-- For `E > 0`, `ℓ² > 0`, `k ≠ 0`, the eccentricity exceeds `1`. -/
theorem one_lt_ecc {m k E L2 : ℝ} (hm : 0 < m) (hk : k ≠ 0) (hE : 0 < E) (hL : 0 < L2) :
    1 < ecc m k E L2 := by
  have : 0 < 2 * E * L2 / (m * k ^ 2) := by positivity
  rw [ecc, lt_sqrt zero_le_one]; linarith

/-- The key identity `e² - 1 = (2 E b / k)²`. -/
theorem ecc_sq_sub_one {m k E L2 : ℝ} (hm : 0 < m) (hk : k ≠ 0) (hE : 0 < E) (hL : 0 ≤ L2) :
    ecc m k E L2 ^ 2 - 1 = (2 * E * impactParam m E L2 / k) ^ 2 := by
  have h0 : 0 ≤ 1 + 2 * E * L2 / (m * k ^ 2) := by positivity
  rw [ecc, sq_sqrt h0, impactParam, div_pow, mul_pow, div_pow, sq_sqrt hL,
    sq_sqrt (by positivity)]
  field_simp
  ring

/-- **Rutherford's relation** `tan (Θ/2) = |k| / (2 E b)`, where `Θ` is the deflection angle and
`b = ℓ / √(2 m E)` the impact parameter. -/
theorem rutherford_tan {m k E L2 : ℝ} (hm : 0 < m) (hk : k ≠ 0) (hE : 0 < E) (hL : 0 < L2) :
    tan (deflectionAngle (ecc m k E L2) / 2) = |k| / (2 * E * impactParam m E L2) := by
  rw [tan_half_deflectionAngle (one_lt_ecc hm hk hE hL), ecc_sq_sub_one hm hk hE hL.le,
    sqrt_sq_eq_abs, abs_div, one_div_div]
  have hb : 0 < impactParam m E L2 := div_pos (sqrt_pos.mpr hL) (sqrt_pos.mpr (by positivity))
  rw [abs_of_pos (by positivity : 0 < 2 * E * impactParam m E L2)]

/-- Equivalently, `cot (Θ/2) = 2 E b / |k|`. -/
theorem rutherford_cot {m k E L2 : ℝ} (hm : 0 < m) (hk : k ≠ 0) (hE : 0 < E) (hL : 0 < L2) :
    cos (deflectionAngle (ecc m k E L2) / 2) / sin (deflectionAngle (ecc m k E L2) / 2) =
      2 * E * impactParam m E L2 / |k| := by
  rw [← inv_div, ← tan_eq_sin_div_cos, rutherford_tan hm hk hE hL, inv_div]

/-- The derivative of the impact parameter as a function of the deflection angle:
`db/dΘ = -|k| / (4 E sin² (Θ/2))`. -/
theorem hasDerivAt_impactOfAngle (k E : ℝ) {Θ : ℝ} (hs : sin (Θ / 2) ≠ 0) :
    HasDerivAt (impactOfAngle k E) (-|k| / (4 * E * sin (Θ / 2) ^ 2)) Θ := by
  have hh : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) Θ := (hasDerivAt_id Θ).div_const 2
  have hc := (hasDerivAt_cos (Θ / 2)).comp Θ hh
  have hsn := (hasDerivAt_sin (Θ / 2)).comp Θ hh
  have hq := ((hc.div hsn hs).const_mul (|k| / (2 * E)))
  refine HasDerivAt.congr_deriv (f := impactOfAngle k E) hq ?_
  have h := sin_sq_add_cos_sq (Θ / 2)
  simp only [Function.comp_apply]
  field_simp
  linear_combination (-(abs k) * 4 * E⁻¹) * h

/-- **Rutherford cross section**: for `0 < Θ < π`, with `b = (|k|/(2E)) cot (Θ/2)` and
`db/dΘ = -|k| / (4 E sin² (Θ/2))`, `(b / sin Θ) |db/dΘ| = (k / (4 E))² / sin⁴ (Θ/2)`. -/
theorem rutherford_cross_section {k E Θ : ℝ} (hE : 0 < E) (h0 : 0 < Θ) (hπ : Θ < π) :
    crossSection Θ (impactOfAngle k E Θ) (-|k| / (4 * E * sin (Θ / 2) ^ 2)) =
      (k / (4 * E)) ^ 2 / sin (Θ / 2) ^ 4 := by
  have hs : 0 < sin (Θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < cos (Θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h2 : sin Θ = 2 * sin (Θ / 2) * cos (Θ / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [crossSection, impactOfAngle, h2, abs_div, abs_neg, abs_abs,
    abs_of_pos (by positivity : 0 < 4 * E * sin (Θ / 2) ^ 2)]
  rw [div_pow, ← sq_abs k]
  field_simp
  ring

/-- The cross section in terms of the derivative of `b(Θ)`: if `b' = db/dΘ` then
`(b / sin Θ) |b'| = (k / (4 E))² / sin⁴ (Θ/2)`. -/
theorem rutherford_cross_section_deriv {k E Θ : ℝ} (hE : 0 < E) (h0 : 0 < Θ) (hπ : Θ < π)
    {b' : ℝ} (hb : HasDerivAt (impactOfAngle k E) b' Θ) :
    crossSection Θ (impactOfAngle k E Θ) b' = (k / (4 * E)) ^ 2 / sin (Θ / 2) ^ 4 := by
  have hs : 0 < sin (Θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hb.unique (hasDerivAt_impactOfAngle k E hs.ne'), rutherford_cross_section hE h0 hπ]

/-- The impact parameter `b(Θ)` recovers `b` at the deflection angle of the orbit. -/
theorem impactOfAngle_deflectionAngle {m k E L2 : ℝ} (hm : 0 < m) (hk : k ≠ 0) (hE : 0 < E)
    (hL : 0 < L2) :
    impactOfAngle k E (deflectionAngle (ecc m k E L2)) = impactParam m E L2 := by
  rw [impactOfAngle, rutherford_cot hm hk hE hL]
  have : 0 < |k| := abs_pos.mpr hk
  field_simp

end Rutherford

namespace KeplerMotion

variable (K : KeplerMotion)

/-- The eccentricity `e = |A| / (m |k|)` of a (possibly repulsive) Kepler orbit. -/
def hypEcc : ℝ := radius (K.A 0) / (K.m * |K.k|)

variable {K}

/-- **Hyperbolic orbits**: for `E > 0`, `L ≠ 0`, the LRL vector satisfies `|A|² > m² k²`. -/
theorem lrl_sq_gt (hL : K.L 0 ≠ 0) (hE : 0 < K.E 0) (t : ℝ) :
    (K.m * K.k) ^ 2 < K.A t ⬝ᵥ K.A t := by
  have hLL : 0 < K.L t ⬝ᵥ K.L t := by rw [K.angMom_const t 0]; exact dot_self_pos hL
  have hEt : 0 < K.E t := by rw [K.energy_const t 0]; exact hE
  rw [K.lrl_sq]
  have : 0 < 2 * K.m * K.E t * (K.L t ⬝ᵥ K.L t) := by have := K.m_pos; positivity
  nlinarith

/-- The eccentricity squared is `e² = 1 + 2 E |L|² / (m k²)`. -/
theorem hypEcc_sq (hk : K.k ≠ 0) :
    K.hypEcc ^ 2 = 1 + 2 * K.E 0 * (K.L 0 ⬝ᵥ K.L 0) / (K.m * K.k ^ 2) := by
  have hm := K.m_pos.ne'
  rw [hypEcc, div_pow, radius_sq, K.lrl_sq, mul_pow, sq_abs]
  field_simp

/-- The eccentricity agrees with `Rutherford.ecc` evaluated at the conserved quantities. -/
theorem hypEcc_eq (hk : K.k ≠ 0) :
    K.hypEcc = Rutherford.ecc K.m K.k (K.E 0) (K.L 0 ⬝ᵥ K.L 0) := by
  have h0 : 0 ≤ K.hypEcc := by
    have := K.m_pos
    rw [hypEcc]; exact div_nonneg (sqrt_nonneg _) (by positivity)
  rw [Rutherford.ecc, ← hypEcc_sq hk, sqrt_sq h0]

/-- **Hyperbolic orbits**: for `E > 0`, `L ≠ 0` and `k ≠ 0`, the eccentricity exceeds `1`. -/
theorem one_lt_hypEcc (hk : K.k ≠ 0) (hL : K.L 0 ≠ 0) (hE : 0 < K.E 0) : 1 < K.hypEcc := by
  rw [hypEcc_eq hk]
  exact Rutherford.one_lt_ecc K.m_pos hk hE (dot_self_pos hL)

/-- Along a Kepler motion with `L ≠ 0`, `A · x > -m k r` (from the orbit equation). -/
theorem lrl_dot_gt (hL : K.L 0 ≠ 0) (t : ℝ) : -(K.m * K.k) * K.r t < K.A t ⬝ᵥ K.x t := by
  have hLL : 0 < K.L t ⬝ᵥ K.L t := by rw [K.angMom_const t 0]; exact dot_self_pos hL
  have := K.orbit_equation t
  linarith

/-- **The orbit lies in a cone around `A`**: the angle `θ` between `x` and `A ≠ 0` satisfies
`cos θ = A · x / (|A| r) > -m k / |A|`; i.e. `cos θ > -1/e` for `k > 0` and `cos θ > 1/e` for
`k < 0`. -/
theorem cos_angle_gt (hL : K.L 0 ≠ 0) (hA : K.A 0 ≠ 0) (t : ℝ) :
    -(K.m * K.k) / radius (K.A t) < K.A t ⬝ᵥ K.x t / (radius (K.A t) * K.r t) := by
  have hA' : K.A t ≠ 0 := by rw [K.lrl_const t 0]; exact hA
  have ha := radius_pos hA'
  have hr := K.r_pos t
  rw [div_lt_div_iff₀ ha (by positivity)]
  have := K.lrl_dot_gt hL t
  nlinarith

/-- **Rutherford's relation** for a Kepler motion with `E > 0`, `L ≠ 0`, `k ≠ 0`:
`tan (Θ/2) = |k| / (2 E b)` with `Θ` the deflection angle and `b = |L| / √(2 m E)`. -/
theorem rutherford_tan (hk : K.k ≠ 0) (hL : K.L 0 ≠ 0) (hE : 0 < K.E 0) :
    tan (Rutherford.deflectionAngle K.hypEcc / 2) =
      |K.k| / (2 * K.E 0 * Rutherford.impactParam K.m (K.E 0) (K.L 0 ⬝ᵥ K.L 0)) := by
  rw [hypEcc_eq hk]
  exact Rutherford.rutherford_tan K.m_pos hk hE (dot_self_pos hL)

end KeplerMotion

end ClassicalMechanics
