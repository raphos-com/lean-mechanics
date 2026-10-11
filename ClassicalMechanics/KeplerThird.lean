import ClassicalMechanics.Kepler
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Kepler's third law

For a bound Kepler orbit (`k > 0`, `L ≠ 0`, `E < 0`, see `ClassicalMechanics.Kepler`) we introduce
the orbital elements

* the **eccentricity** `e = |A| / (m k)` (`ecc`),
* the **semi-latus rectum** `p = |L|² / (m k)` (`semiLatus`),
* the **semi-major axis** `a = p / (1 - e²)` (`semiMajor`),
* the **semi-minor axis** `b = a √(1 - e²)` (`semiMinor`),

and prove:

* `e < 1` (`ecc_lt_one`) and `1 - e² = -2 E |L|² / (m k²)` (`one_sub_ecc_sq`);
* `a = -k / (2 E)`: the semi-major axis depends only on the energy (`semiMajor_eq`);
* `b² = a p` (`semiMinor_sq`);
* **periapsis and apoapsis**: along the whole motion `p / (1 + e) ≤ r ≤ p / (1 - e)`
  (`periapsis_le`, `le_apoapsis`), with equality exactly when `x` is parallel, resp.
  antiparallel, to the LRL vector (`r_eq_periapsis_iff`, `r_eq_apoapsis_iff`);
* the **areal speed** `|x × ẋ| / 2 = |L| / (2 m)` (`areal_speed`);
* **Kepler's third law** `T² = 4 π² m a³ / k` (`kepler_third`).

The last statement takes as a **hypothesis** the geometric fact that over one period `T` the radius
vector sweeps the area `π a b` of the elliptic orbit, i.e. `T · |L| / (2 m) = π a b` (by Kepler's
second law, the swept area is the period times the constant areal speed `areal_speed`). The
formalization of the swept area as an integral and of the area of the ellipse is not done here;
everything else, in particular `a = -k/(2E)`, `b² = a p` and `p = |L|²/(m k)`, is derived from the
equations of motion. The purely algebraic core is `kepler_third_of_area`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.7–3.8.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §8.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

/-- **Lagrange's identity** `|u|² |v|² = (u · v)² + |u × v|²`. -/
theorem lagrange_identity (u v : Vec) :
    (u ⬝ᵥ u) * (v ⬝ᵥ v) = (u ⬝ᵥ v) ^ 2 + (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
  rw [cross_dot_cross, dotProduct_comm v u]
  ring

/-- **Cauchy–Schwarz inequality** `|u · v| ≤ |u| |v|`. -/
theorem abs_dot_le (u v : Vec) : |u ⬝ᵥ v| ≤ radius u * radius v := by
  rw [radius, radius, ← Real.sqrt_mul (show 0 ≤ u ⬝ᵥ u from normSq_nonneg u)]
  refine Real.abs_le_sqrt ?_
  have := lagrange_identity u v
  have := normSq_nonneg (u ⨯₃ v)
  rw [normSq] at this
  linarith

/-- **Algebraic core of Kepler's third law.** If over one period `T` the area swept at the areal
speed `ℓ / (2 m)` equals the area `π a b` of an ellipse with `b² = a p` and semi-latus rectum
`p = ℓ² / (m k)`, then `T² = 4 π² m a³ / k`. -/
theorem kepler_third_of_area {m k T ℓ a b p : ℝ} (hm : 0 < m) (hk : 0 < k) (hℓ : ℓ ≠ 0)
    (harea : T * (ℓ / (2 * m)) = π * a * b) (hb : b ^ 2 = a * p) (hp : p = ℓ ^ 2 / (m * k)) :
    T ^ 2 = 4 * π ^ 2 * m * a ^ 3 / k := by
  have h2 : (T * (ℓ / (2 * m))) ^ 2 = π ^ 2 * a ^ 2 * b ^ 2 := by rw [harea]; ring
  rw [hb, hp] at h2
  have hℓ2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  field_simp at h2
  rw [eq_div_iff hk.ne']
  linear_combination h2

namespace KeplerMotion

variable (K : KeplerMotion)

/-- The **eccentricity** `e = |A| / (m k)`. -/
def ecc : ℝ := radius (K.A 0) / (K.m * K.k)

/-- The **semi-latus rectum** `p = |L|² / (m k)`. -/
def semiLatus : ℝ := (K.L 0 ⬝ᵥ K.L 0) / (K.m * K.k)

/-- The **semi-major axis** `a = p / (1 - e²)`. -/
def semiMajor : ℝ := K.semiLatus / (1 - K.ecc ^ 2)

/-- The **semi-minor axis** `b = a √(1 - e²)`. -/
def semiMinor : ℝ := K.semiMajor * √(1 - K.ecc ^ 2)

variable {K}

theorem ecc_nonneg (hk : 0 < K.k) : 0 ≤ K.ecc :=
  div_nonneg (Real.sqrt_nonneg _) (mul_pos K.m_pos hk).le

/-- `e m k = |A|`. -/
theorem ecc_mul (hk : 0 < K.k) : K.ecc * (K.m * K.k) = radius (K.A 0) :=
  div_mul_cancel₀ _ (mul_pos K.m_pos hk).ne'

/-- `e² = |A|² / (m k)²`. -/
theorem ecc_sq : K.ecc ^ 2 = (K.A 0 ⬝ᵥ K.A 0) / (K.m * K.k) ^ 2 := by
  rw [ecc, div_pow, radius_sq]

/-- `1 - e² = -2 E |L|² / (m k²)`. -/
theorem one_sub_ecc_sq (hk : 0 < K.k) :
    1 - K.ecc ^ 2 = -2 * K.E 0 * (K.L 0 ⬝ᵥ K.L 0) / (K.m * K.k ^ 2) := by
  have hm := K.m_pos.ne'
  have hk' := hk.ne'
  rw [ecc_sq, K.lrl_sq]
  field_simp
  ring

/-- A bound orbit (`E < 0`, `L ≠ 0`) has eccentricity `e < 1`. -/
theorem ecc_lt_one (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) : K.ecc < 1 := by
  have h := (K.ecc_lt_one_iff hL 0).2 hE
  have hsq : K.ecc ^ 2 < 1 := by
    rw [ecc_sq, div_lt_one (pow_pos (mul_pos K.m_pos hk) 2)]
    exact h
  nlinarith [ecc_nonneg hk]

theorem one_sub_ecc_sq_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    0 < 1 - K.ecc ^ 2 := by
  have := ecc_lt_one hk hL hE
  nlinarith [ecc_nonneg hk]

/-- The semi-major axis depends only on the energy: `a = -k / (2 E)`. -/
theorem semiMajor_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiMajor = -K.k / (2 * K.E 0) := by
  have hm := K.m_pos.ne'
  have hk' := hk.ne'
  have hE' := hE.ne
  have hLL := (dot_self_pos hL).ne'
  rw [semiMajor, one_sub_ecc_sq hk, semiLatus]
  field_simp

/-- The semi-major axis is positive. -/
theorem semiMajor_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) : 0 < K.semiMajor := by
  rw [semiMajor_eq hk hL hE]
  exact div_pos_of_neg_of_neg (by linarith) (by linarith)

/-- `b² = a p`. -/
theorem semiMinor_sq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiMinor ^ 2 = K.semiMajor * K.semiLatus := by
  have h := one_sub_ecc_sq_pos hk hL hE
  rw [semiMinor, mul_pow, Real.sq_sqrt h.le, semiMajor]
  field_simp

/-- The **areal speed** is `|x × ẋ| / 2 = |L| / (2 m)` at all times. -/
theorem areal_speed (t : ℝ) : radius (K.x t ⨯₃ K.v t) / 2 = radius (K.L 0) / (2 * K.m) := by
  have hm := K.m_pos
  rw [← K.angMom_const t 0, L, map_smul, radius, radius, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, Real.sqrt_mul (mul_self_nonneg _),
    Real.sqrt_mul_self hm.le]
  field_simp

/-- **Kepler's third law** `T² = 4 π² m a³ / k`, for a bound orbit (`k > 0`, `L ≠ 0`,
`E < 0`). The **hypothesis** `harea` states that during one period `T` the radius vector sweeps,
at the constant areal speed `|L| / (2 m)` (`areal_speed`), the area `π a b` of the ellipse. -/
theorem kepler_third (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ}
    (harea : T * (radius (K.L 0) / (2 * K.m)) = π * K.semiMajor * K.semiMinor) :
    T ^ 2 = 4 * π ^ 2 * K.m * K.semiMajor ^ 3 / K.k := by
  refine kepler_third_of_area K.m_pos hk (radius_pos hL).ne' harea (semiMinor_sq hk hL hE) ?_
  rw [semiLatus, radius_sq]

/-- **Kepler's third law** in terms of the energy: `T² = 4 π² m (-k / (2E))³ / k`. -/
theorem kepler_third_energy (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ}
    (harea : T * (radius (K.L 0) / (2 * K.m)) = π * K.semiMajor * K.semiMinor) :
    T ^ 2 = 4 * π ^ 2 * K.m * (-K.k / (2 * K.E 0)) ^ 3 / K.k := by
  rw [kepler_third hk hL hE harea, semiMajor_eq hk hL hE]

/-- The orbit equation with the conserved `A(0)`, `L(0)`: `A · x + m k r = |L|²`. -/
theorem orbit_equation_zero (t : ℝ) :
    K.A 0 ⬝ᵥ K.x t + K.m * K.k * K.r t = K.L 0 ⬝ᵥ K.L 0 := by
  rw [K.lrl_const 0 t, K.angMom_const 0 t]
  exact K.orbit_equation t

/-- `|A · x| ≤ e m k r`. -/
theorem abs_lrl_dot_le (hk : 0 < K.k) (t : ℝ) :
    |K.A 0 ⬝ᵥ K.x t| ≤ K.ecc * (K.m * K.k) * K.r t := by
  rw [ecc_mul hk]
  exact abs_dot_le _ _

/-- **Periapsis**: `p / (1 + e) ≤ r` along the whole motion. -/
theorem periapsis_le (hk : 0 < K.k) (t : ℝ) : K.semiLatus / (1 + K.ecc) ≤ K.r t := by
  have hmk := mul_pos K.m_pos hk
  have he := ecc_nonneg hk
  have h1 := orbit_equation_zero (K := K) t
  have h2 := (abs_le.1 (abs_lrl_dot_le hk t)).2
  rw [semiLatus, div_div, div_le_iff₀ (mul_pos hmk (by linarith))]
  nlinarith

/-- **Apoapsis**: `r ≤ p / (1 - e)` along the whole motion, for a bound orbit. -/
theorem le_apoapsis (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.r t ≤ K.semiLatus / (1 - K.ecc) := by
  have hmk := mul_pos K.m_pos hk
  have he := ecc_lt_one hk hL hE
  have h1 := orbit_equation_zero (K := K) t
  have h2 := (abs_le.1 (abs_lrl_dot_le hk t)).1
  rw [semiLatus, div_div, le_div_iff₀ (mul_pos hmk (by linarith))]
  nlinarith

/-- The periapsis distance is attained exactly where `A · x = |A| r`, i.e. where `x` points along
the LRL vector. -/
theorem r_eq_periapsis_iff (hk : 0 < K.k) (t : ℝ) :
    K.r t = K.semiLatus / (1 + K.ecc) ↔ K.A 0 ⬝ᵥ K.x t = radius (K.A 0) * K.r t := by
  have hmk := mul_pos K.m_pos hk
  have he := ecc_nonneg hk
  have h1 := orbit_equation_zero (K := K) t
  have hA := ecc_mul hk
  rw [semiLatus, div_div, eq_div_iff (mul_pos hmk (by linarith)).ne', ← hA]
  constructor <;> intro h <;> nlinarith

/-- The apoapsis distance is attained exactly where `A · x = -|A| r`, i.e. where `x` points
opposite to the LRL vector (bound orbit). -/
theorem r_eq_apoapsis_iff (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.r t = K.semiLatus / (1 - K.ecc) ↔ K.A 0 ⬝ᵥ K.x t = -(radius (K.A 0) * K.r t) := by
  have hmk := mul_pos K.m_pos hk
  have he := ecc_lt_one hk hL hE
  have h1 := orbit_equation_zero (K := K) t
  have hA := ecc_mul hk
  rw [semiLatus, div_div, eq_div_iff (mul_pos hmk (by linarith)).ne', ← hA]
  constructor <;> intro h <;> nlinarith

end KeplerMotion

end ClassicalMechanics
