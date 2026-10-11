import ClassicalMechanics.KeplerThird
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The period of a Kepler orbit

We prove **Kepler's third law** `T² = 4 π² m a³ / k` for a bound Kepler orbit (`k > 0`, `L ≠ 0`,
`E < 0`) with `T` the actual period of the motion, removing the swept-area hypothesis of
`ClassicalMechanics.KeplerMotion.kepler_third`.

The proof uses the **eccentric anomaly** `E` rather than the polar angle, which avoids computing
`∫₀^{2π} dθ / (1 + e cos θ)²`.

* **Orbital frame.** `ê₁` is the unit vector along the LRL vector `A` (or along `x(0)` for a
  circular orbit, `A = 0`), and `ê₂ = L̂ × ê₁` (`axis1`, `axis2`). Every vector orthogonal to `L`,
  in particular `x(t)` and `ẋ(t)`, is a combination of `ê₁` and `ê₂` (`eq_axis_decomp`).
* **Eccentric anomaly.** `cos E = x·ê₁ / a + e` and `sin E = x·ê₂ / b` (`cosAnom`, `sinAnom`)
  satisfy `cos² E + sin² E = 1` and `r = a (1 - e cos E)`. The velocity in the frame
  (`v_dot_axis1`, `v_dot_axis2`), computed from the LRL vector, gives
  `d/dt (cos E, sin E) = Ė (-sin E, cos E)` with `Ė = n a / r`, `n = √(k / (m a³))`
  (`hasDerivAt_cosAnom`, `hasDerivAt_sinAnom`).
* **A continuous angle.** `Φ(t) = ∫₀ᵗ n a / r` (`anomaly`) is a strictly increasing lift of `E`:
  `(cos E(t), sin E(t))` is `(cos E(0), sin E(0))` rotated by `Φ(t)` (`anom_rotation`).
* **Kepler's equation** `Φ(t) - e sin E(t) = n t - e sin E(0)` (`kepler_equation`).
* **The period.** If `x(t + T) = x(t)` with `T > 0`, then `Φ` advances by a positive multiple of
  `2π` and `n T = Φ(t + T) - Φ(t) ≥ 2π` (`two_pi_div_le`); conversely, the state `(x, ẋ)` is
  periodic with period `2π / n` (`periodic`). Hence the minimal period (`period_eq`), and also the
  first return time to the initial position (`first_return_eq`), is `T = 2π / n`, and
  `T² = 4 π² m a³ / k` (`kepler_third_period`, `kepler_third_first_return`).
* The swept-area hypothesis of `kepler_third` holds: `T |L| / (2 m) = π a b`
  (`period_mul_areal_speed`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.7–3.8.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §8.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

namespace KeplerMotion

variable (K : KeplerMotion)

/-- The first axis `ê₁` of the orbital frame: the unit vector along the LRL vector `A`, or, for a
circular orbit (`A = 0`), along the initial position `x(0)`. -/
def axis1 : Vec :=
  if K.A 0 = 0 then (K.r 0)⁻¹ • K.x 0 else (radius (K.A 0))⁻¹ • K.A 0

/-- The second axis `ê₂ = L̂ × ê₁` of the orbital frame. -/
def axis2 : Vec := (radius (K.L 0))⁻¹ • (K.L 0 ⨯₃ K.axis1)

/-- The **mean motion** `n = √(k / (m a³))`. -/
def meanMotion : ℝ := √(K.k / (K.m * K.semiMajor ^ 3))

/-- The cosine of the **eccentric anomaly**, `cos E = x·ê₁ / a + e`. -/
def cosAnom (t : ℝ) : ℝ := K.x t ⬝ᵥ K.axis1 / K.semiMajor + K.ecc

/-- The sine of the **eccentric anomaly**, `sin E = x·ê₂ / b`. -/
def sinAnom (t : ℝ) : ℝ := K.x t ⬝ᵥ K.axis2 / K.semiMinor

/-- The rate of change `Ė = n a / r` of the eccentric anomaly. -/
def anomRate (t : ℝ) : ℝ := K.meanMotion * K.semiMajor / K.r t

/-- The **eccentric anomaly** measured from time `0`, `E(t) - E(0) = ∫₀ᵗ n a / r`; a continuous
angle function. -/
def anomaly (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, K.anomRate s

variable {K}

/-! ### The orbital frame -/

/-- `ê₁` is a unit vector. -/
theorem axis1_dot_self : K.axis1 ⬝ᵥ K.axis1 = 1 := by
  unfold axis1
  split_ifs with h
  · have := (K.r_pos 0).ne'
    rw [smul_dotProduct, dotProduct_smul, ← K.r_sq, smul_eq_mul, smul_eq_mul]
    field_simp
  · have := (radius_pos h).ne'
    rw [smul_dotProduct, dotProduct_smul, ← radius_sq, smul_eq_mul, smul_eq_mul]
    field_simp

/-- `ê₁` lies in the plane of the orbit. -/
theorem axis1_dot_L : K.axis1 ⬝ᵥ K.L 0 = 0 := by
  unfold axis1
  split_ifs
  · rw [smul_dotProduct, K.planar, smul_zero]
  · rw [smul_dotProduct, K.lrl_dot_angMom, smul_zero]

/-- The LRL vector points along `ê₁`: `A = |A| ê₁`. -/
theorem A_eq_smul_axis1 : K.A 0 = radius (K.A 0) • K.axis1 := by
  unfold axis1
  split_ifs with h
  · simp [h, radius]
  · rw [smul_smul, mul_inv_cancel₀ (radius_pos h).ne', one_smul]

/-- `L × ê₁ = |L| ê₂`. -/
theorem L_cross_axis1 (hL : K.L 0 ≠ 0) : K.L 0 ⨯₃ K.axis1 = radius (K.L 0) • K.axis2 := by
  rw [axis2, smul_smul, mul_inv_cancel₀ (radius_pos hL).ne', one_smul]

/-- `ê₂` is a unit vector. -/
theorem axis2_dot_self (hL : K.L 0 ≠ 0) : K.axis2 ⬝ᵥ K.axis2 = 1 := by
  have h : (K.L 0 ⨯₃ K.axis1) ⬝ᵥ (K.L 0 ⨯₃ K.axis1) = K.L 0 ⬝ᵥ K.L 0 := by
    rw [cross_dot_cross, axis1_dot_self, dotProduct_comm (K.L 0) K.axis1, axis1_dot_L]
    ring
  have := (radius_pos hL).ne'
  rw [axis2, smul_dotProduct, dotProduct_smul, h, ← radius_sq, smul_eq_mul, smul_eq_mul]
  field_simp

/-- `ê₁ · ê₂ = 0`. -/
theorem axis1_dot_axis2 : K.axis1 ⬝ᵥ K.axis2 = 0 := by
  rw [axis2, dotProduct_smul, dot_cross_self, smul_zero]

/-- `ê₂` lies in the plane of the orbit. -/
theorem axis2_dot_L : K.axis2 ⬝ᵥ K.L 0 = 0 := by
  rw [axis2, smul_dotProduct, dotProduct_comm, dot_self_cross, smul_zero]

/-- Every vector `y` orthogonal to `L` decomposes as `y = (y·ê₁) ê₁ + (y·ê₂) ê₂`. -/
theorem eq_axis_decomp (hL : K.L 0 ≠ 0) {y : Vec} (hy : y ⬝ᵥ K.L 0 = 0) :
    y = (y ⬝ᵥ K.axis1) • K.axis1 + (y ⬝ᵥ K.axis2) • K.axis2 := by
  set z := y - ((y ⬝ᵥ K.axis1) • K.axis1 + (y ⬝ᵥ K.axis2) • K.axis2) with hz
  have h1 : z ⬝ᵥ K.axis1 = 0 := by
    rw [hz, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, axis1_dot_self,
      dotProduct_comm K.axis2, axis1_dot_axis2]
    simp
  have h2 : z ⬝ᵥ K.axis2 = 0 := by
    rw [hz, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, axis2_dot_self hL,
      axis1_dot_axis2]
    simp
  have h3 : z ⬝ᵥ K.L 0 = 0 := by
    rw [hz, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, axis1_dot_L,
      axis2_dot_L, hy]
    simp
  have hN : z ⬝ᵥ (K.L 0 ⨯₃ K.axis1) = 0 := by
    rw [L_cross_axis1 hL, dotProduct_smul, h2, smul_zero]
  have hC : z ⨯₃ (K.L 0 ⨯₃ K.axis1) = 0 := by
    rw [cross_cross_eq_smul_sub_smul', h1, dotProduct_comm, h3, zero_smul, zero_smul, sub_zero]
  have hNN : 0 < (K.L 0 ⨯₃ K.axis1) ⬝ᵥ (K.L 0 ⨯₃ K.axis1) := by
    rw [L_cross_axis1 hL, smul_dotProduct, dotProduct_smul, axis2_dot_self hL, smul_eq_mul,
      smul_eq_mul, mul_one]
    exact mul_pos (radius_pos hL) (radius_pos hL)
  have hlag := lagrange_identity z (K.L 0 ⨯₃ K.axis1)
  rw [hN, hC, zero_dotProduct] at hlag
  have hzz : z ⬝ᵥ z = 0 := by
    have h0 : (z ⬝ᵥ z) * ((K.L 0 ⨯₃ K.axis1) ⬝ᵥ (K.L 0 ⨯₃ K.axis1)) = 0 := by
      rw [hlag]; ring
    exact (mul_eq_zero.1 h0).resolve_right hNN.ne'
  exact (sub_eq_zero.1 (dotProduct_self_eq_zero.1 hzz))


/-! ### Orbital constants -/

/-- `p = a (1 - e²)`. -/
theorem semiLatus_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiLatus = K.semiMajor * (1 - K.ecc ^ 2) := by
  rw [semiMajor, div_mul_cancel₀ _ (one_sub_ecc_sq_pos hk hL hE).ne']

/-- The semi-minor axis is positive. -/
theorem semiMinor_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) : 0 < K.semiMinor :=
  mul_pos (semiMajor_pos hk hL hE) (Real.sqrt_pos.2 (one_sub_ecc_sq_pos hk hL hE))

/-- `n² = k / (m a³)`. -/
theorem meanMotion_sq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.meanMotion ^ 2 = K.k / (K.m * K.semiMajor ^ 3) :=
  Real.sq_sqrt (div_pos hk (mul_pos K.m_pos (pow_pos (semiMajor_pos hk hL hE) 3))).le

/-- The mean motion is positive. -/
theorem meanMotion_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) : 0 < K.meanMotion :=
  Real.sqrt_pos.2 (div_pos hk (mul_pos K.m_pos (pow_pos (semiMajor_pos hk hL hE) 3)))

/-- `k b = n a² |L|`. -/
theorem k_mul_semiMinor (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.k * K.semiMinor = K.meanMotion * K.semiMajor ^ 2 * radius (K.L 0) := by
  have ha := semiMajor_pos hk hL hE
  have hn := meanMotion_pos hk hL hE
  have hℓ := radius_pos hL
  have hm := K.m_pos
  rw [← pow_left_inj₀ (mul_pos hk (semiMinor_pos hk hL hE)).le (by positivity) two_ne_zero,
    mul_pow, semiMinor_sq hk hL hE, mul_pow, mul_pow, meanMotion_sq hk hL hE, semiLatus,
    ← radius_sq (K.L 0)]
  field_simp

/-- The orbit equation in the orbital frame: `r = p - e (x · ê₁)`. -/
theorem r_eq (hk : 0 < K.k) (t : ℝ) : K.r t = K.semiLatus - K.ecc * (K.x t ⬝ᵥ K.axis1) := by
  have h := orbit_equation_zero (K := K) t
  rw [A_eq_smul_axis1, smul_dotProduct, smul_eq_mul, ← ecc_mul hk,
    dotProduct_comm K.axis1] at h
  rw [semiLatus, eq_sub_iff_add_eq, eq_div_iff (mul_pos K.m_pos hk).ne']
  linear_combination h

/-! ### The velocity in the orbital frame -/

/-- `m ẋ × L = A + (m k / r) x`. -/
theorem smul_v_cross_L (t : ℝ) :
    (K.m • K.v t) ⨯₃ K.L 0 = K.A 0 + (K.m * K.k / K.r t) • K.x t := by
  rw [K.lrl_const 0 t, K.angMom_const 0 t, A, sub_add_cancel]

/-- `ẋ · ê₁ = -k (x · ê₂) / (r |L|)`. -/
theorem v_dot_axis1 (hL : K.L 0 ≠ 0) (t : ℝ) :
    K.v t ⬝ᵥ K.axis1 = -(K.k * (K.x t ⬝ᵥ K.axis2)) / (K.r t * radius (K.L 0)) := by
  have h := congrArg (· ⬝ᵥ (K.L 0 ⨯₃ K.axis1)) (smul_v_cross_L (K := K) t)
  rw [cross_dot_cross, dotProduct_comm (K.L 0) K.axis1, axis1_dot_L, add_dotProduct,
    A_eq_smul_axis1] at h
  simp only [smul_dotProduct, smul_eq_mul] at h
  rw [dot_cross_self, L_cross_axis1 hL, dotProduct_smul, ← radius_sq] at h
  simp only [smul_eq_mul] at h
  have := (K.r_pos t).ne'
  have hℓ := (radius_pos hL).ne'
  have hm := K.m_pos.ne'
  field_simp
  field_simp at h
  refine mul_left_cancel₀ (mul_ne_zero hm hℓ) ?_
  linear_combination -h

/-- `ẋ · ê₂ = (|A| + m k (x · ê₁) / r) / (m |L|)`. -/
theorem v_dot_axis2 (hL : K.L 0 ≠ 0) (t : ℝ) :
    K.v t ⬝ᵥ K.axis2 =
      (radius (K.A 0) + K.m * K.k * (K.x t ⬝ᵥ K.axis1) / K.r t) / (K.m * radius (K.L 0)) := by
  have h := congrArg (K.axis1 ⬝ᵥ ·) (smul_v_cross_L (K := K) t)
  rw [dotProduct_add, A_eq_smul_axis1, dotProduct_smul, axis1_dot_self, dotProduct_smul,
    dotProduct_comm K.axis1 (K.x t)] at h
  have htp : K.axis1 ⬝ᵥ (K.m • K.v t) ⨯₃ K.L 0 =
      K.m * radius (K.L 0) * (K.v t ⬝ᵥ K.axis2) := by
    rw [← triple_product_permutation, ← triple_product_permutation, L_cross_axis1 hL,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [htp] at h
  simp only [smul_eq_mul] at h
  have := (K.r_pos t).ne'
  have := (radius_pos hL).ne'
  have := K.m_pos.ne'
  field_simp
  field_simp at h
  linear_combination h


/-- `ẋ · L = 0`. -/
theorem v_dot_L (t : ℝ) : K.v t ⬝ᵥ K.L 0 = 0 := by
  rw [← K.angMom_const t 0, L, map_smul, dotProduct_smul, dot_cross_self, smul_zero]

/-- The velocity is a function of the position: `x(s) = x(t) → ẋ(s) = ẋ(t)`. -/
theorem v_eq_of_x_eq (hL : K.L 0 ≠ 0) {s t : ℝ} (h : K.x s = K.x t) : K.v s = K.v t := by
  rw [eq_axis_decomp hL (v_dot_L s), eq_axis_decomp hL (v_dot_L t), v_dot_axis1 hL,
    v_dot_axis1 hL, v_dot_axis2 hL, v_dot_axis2 hL]
  simp only [KeplerMotion.r, h]

/-! ### The eccentric anomaly -/

/-- `r = a (1 - e cos E)`. -/
theorem r_eq_cosAnom (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.r t = K.semiMajor * (1 - K.ecc * K.cosAnom t) := by
  have ha := (semiMajor_pos hk hL hE).ne'
  rw [r_eq hk, semiLatus_eq hk hL hE, cosAnom]
  field_simp
  ring

/-- `r² = (x · ê₁)² + (x · ê₂)²`. -/
theorem r_sq_eq (hL : K.L 0 ≠ 0) (t : ℝ) :
    K.r t ^ 2 = (K.x t ⬝ᵥ K.axis1) ^ 2 + (K.x t ⬝ᵥ K.axis2) ^ 2 := by
  have h := eq_axis_decomp hL (K.planar t)
  have h12 : K.axis2 ⬝ᵥ K.axis1 = 0 := by rw [dotProduct_comm, axis1_dot_axis2]
  rw [K.r_sq]
  conv_lhs => rw [h]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    axis1_dot_self, axis2_dot_self hL, axis1_dot_axis2, h12]
  ring

/-- `cos² E + sin² E = 1`. -/
theorem cosAnom_sq_add_sinAnom_sq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.cosAnom t ^ 2 + K.sinAnom t ^ 2 = 1 := by
  have ha := semiMajor_pos hk hL hE
  have hp := semiLatus_eq hk hL hE
  have hb2 := semiMinor_sq hk hL hE
  have hr := r_eq hk t
  have hw := r_sq_eq hL t
  have hp0 : 0 < K.semiLatus := by
    rw [hp]; exact mul_pos ha (one_sub_ecc_sq_pos hk hL hE)
  have key : (K.x t ⬝ᵥ K.axis1 + K.semiMajor * K.ecc) ^ 2 * K.semiLatus +
      K.semiMajor * (K.x t ⬝ᵥ K.axis2) ^ 2 = K.semiMajor ^ 2 * K.semiLatus := by
    rw [hr, hp] at hw
    rw [hp]
    linear_combination (-K.semiMajor) * hw
  rw [cosAnom, sinAnom, div_pow (K.x t ⬝ᵥ K.axis2), hb2]
  field_simp
  linear_combination key

/-- `d/dt cos E = -Ė sin E`. -/
theorem hasDerivAt_cosAnom (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    HasDerivAt K.cosAnom (-(K.anomRate t * K.sinAnom t)) t := by
  have h := ((hasDerivAt_dot (K.hasDerivAt_x t) (hasDerivAt_const t K.axis1)).div_const
    K.semiMajor).add_const K.ecc
  convert h using 1
  · rfl
  have hI := k_mul_semiMinor hk hL hE
  have := (semiMajor_pos hk hL hE).ne'
  have := (semiMinor_pos hk hL hE).ne'
  have := (radius_pos hL).ne'
  have := (K.r_pos t).ne'
  rw [dotProduct_zero, add_zero, v_dot_axis1 hL, anomRate, sinAnom]
  field_simp
  linear_combination (K.x t ⬝ᵥ K.axis2) * hI

/-- `d/dt sin E = Ė cos E`. -/
theorem hasDerivAt_sinAnom (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    HasDerivAt K.sinAnom (K.anomRate t * K.cosAnom t) t := by
  have h := (hasDerivAt_dot (K.hasDerivAt_x t) (hasDerivAt_const t K.axis2)).div_const
    K.semiMinor
  convert h using 1
  · rfl
  have hI := k_mul_semiMinor hk hL hE
  have hb2 := semiMinor_sq hk hL hE
  have hp := semiLatus_eq hk hL hE
  have hr := r_eq hk t
  have := (semiMajor_pos hk hL hE).ne'
  have hb := (semiMinor_pos hk hL hE).ne'
  have := (radius_pos hL).ne'
  have := (K.r_pos t).ne'
  have := K.m_pos.ne'
  have := hk.ne'
  set u := K.x t ⬝ᵥ K.axis1
  have hG : K.meanMotion * radius (K.L 0) * K.semiMinor * (u + K.semiMajor * K.ecc) =
      K.k * (u + K.ecc * K.r t) := by
    refine mul_left_cancel₀ hb ?_
    linear_combination K.meanMotion * radius (K.L 0) * (u + K.semiMajor * K.ecc) * hb2 -
      (u + K.ecc * K.r t) * hI + K.meanMotion * radius (K.L 0) * K.semiMajor * u * hp -
      K.meanMotion * radius (K.L 0) * K.semiMajor ^ 2 * K.ecc * hr
  rw [dotProduct_zero, add_zero, v_dot_axis2 hL, anomRate, cosAnom, ← ecc_mul hk]
  field_simp
  linear_combination hG


/-! ### The continuous eccentric anomaly and Kepler's equation -/

/-- The distance `r` is continuous. -/
theorem continuous_r : Continuous K.r :=
  continuous_iff_continuousAt.2 fun t => (K.hasDerivAt_r t).continuousAt

/-- The rate `Ė = n a / r` is continuous. -/
theorem continuous_anomRate : Continuous K.anomRate :=
  continuous_const.div continuous_r fun t => (K.r_pos t).ne'

/-- `Ė = n a / r` is the derivative of the eccentric anomaly. -/
theorem hasDerivAt_anomaly (t : ℝ) : HasDerivAt K.anomaly (K.anomRate t) t :=
  (continuous_anomRate.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The eccentric anomaly is continuous. -/
theorem continuous_anomaly : Continuous K.anomaly :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_anomaly t).continuousAt

/-- The eccentric anomaly is measured from time `0`. -/
theorem anomaly_zero : K.anomaly 0 = 0 := intervalIntegral.integral_same

/-- `Ė > 0`. -/
theorem anomRate_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    0 < K.anomRate t :=
  div_pos (mul_pos (meanMotion_pos hk hL hE) (semiMajor_pos hk hL hE)) (K.r_pos t)

/-- The eccentric anomaly is strictly increasing. -/
theorem anomaly_strictMono (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    StrictMono K.anomaly :=
  strictMono_of_deriv_pos fun t => by
    rw [(hasDerivAt_anomaly t).deriv]; exact anomRate_pos hk hL hE t

/-- **Kepler's equation** `E - e sin E = n t + const`: the mean anomaly increases uniformly. -/
theorem kepler_equation (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.anomaly t - K.ecc * K.sinAnom t = K.meanMotion * t - K.ecc * K.sinAnom 0 := by
  have hd : ∀ s, HasDerivAt (fun s => K.anomaly s - K.ecc * K.sinAnom s - K.meanMotion * s)
      0 s := by
    intro s
    have h := ((hasDerivAt_anomaly (K := K) s).sub ((hasDerivAt_sinAnom hk hL hE s).const_mul
      K.ecc)).sub ((hasDerivAt_id s).const_mul K.meanMotion)
    convert h using 1
    · rfl
    have hr := r_eq_cosAnom hk hL hE s
    have := (K.r_pos s).ne'
    rw [anomRate]
    field_simp
    linear_combination K.meanMotion * hr
  have h := eq_of_hasDerivAt_zero hd t 0
  simp only [anomaly_zero, mul_zero, sub_zero, zero_sub] at h
  linear_combination h

/-- The point `(cos E, sin E)` rotates by the angle `anomaly t`:
`cos E(t) = cos E(0) cos Φ - sin E(0) sin Φ`, `sin E(t) = sin E(0) cos Φ + cos E(0) sin Φ`. -/
theorem anom_rotation (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.cosAnom t = K.cosAnom 0 * cos (K.anomaly t) - K.sinAnom 0 * sin (K.anomaly t) ∧
      K.sinAnom t = K.sinAnom 0 * cos (K.anomaly t) + K.cosAnom 0 * sin (K.anomaly t) := by
  set c0 := K.cosAnom 0
  set s0 := K.sinAnom 0
  set P := fun t => K.cosAnom t - (c0 * cos (K.anomaly t) - s0 * sin (K.anomaly t)) with hP
  set Q := fun t => K.sinAnom t - (s0 * cos (K.anomaly t) + c0 * sin (K.anomaly t)) with hQ
  have hd : ∀ t, HasDerivAt (fun t => P t ^ 2 + Q t ^ 2) 0 t := by
    intro t
    have hc := hasDerivAt_cosAnom hk hL hE t
    have hs := hasDerivAt_sinAnom hk hL hE t
    have hΦ := hasDerivAt_anomaly (K := K) t
    have hP' := hc.sub ((hΦ.cos.const_mul c0).sub (hΦ.sin.const_mul s0))
    have hQ' := hs.sub ((hΦ.cos.const_mul s0).add (hΦ.sin.const_mul c0))
    convert (hP'.pow 2).add (hQ'.pow 2) using 1
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have h := eq_of_hasDerivAt_zero hd t 0
  have h0 : P 0 ^ 2 + Q 0 ^ 2 = 0 := by
    simp [hP, hQ, anomaly_zero, c0, s0]
  rw [h0] at h
  have hP0 : P t = 0 := by nlinarith [sq_nonneg (P t), sq_nonneg (Q t)]
  have hQ0 : Q t = 0 := by nlinarith [sq_nonneg (P t), sq_nonneg (Q t)]
  exact ⟨sub_eq_zero.1 hP0, sub_eq_zero.1 hQ0⟩

/-- `cos E(s) cos E(t) + sin E(s) sin E(t) = cos (Φ(t) - Φ(s))`. -/
theorem cos_anomaly_sub (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (s t : ℝ) :
    K.cosAnom s * K.cosAnom t + K.sinAnom s * K.sinAnom t =
      cos (K.anomaly t - K.anomaly s) := by
  obtain ⟨hcs, hss⟩ := anom_rotation hk hL hE s
  obtain ⟨hct, hst⟩ := anom_rotation hk hL hE t
  have h0 := cosAnom_sq_add_sinAnom_sq hk hL hE 0
  rw [hcs, hss, hct, hst, cos_sub]
  linear_combination (cos (K.anomaly t) * cos (K.anomaly s) +
    sin (K.anomaly t) * sin (K.anomaly s)) * h0

/-- The position is determined by the eccentric anomaly: equal `(cos E, sin E)` give equal `x`. -/
theorem x_eq_of_anom (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {s t : ℝ}
    (hc : K.cosAnom s = K.cosAnom t) (hs : K.sinAnom s = K.sinAnom t) : K.x s = K.x t := by
  rw [cosAnom, cosAnom, add_left_inj, div_left_inj' (semiMajor_pos hk hL hE).ne'] at hc
  rw [sinAnom, sinAnom, div_left_inj' (semiMinor_pos hk hL hE).ne'] at hs
  rw [eq_axis_decomp hL (K.planar s), eq_axis_decomp hL (K.planar t), hc, hs]


/-! ### The period -/

/-- `|sin E| ≤ 1`. -/
theorem abs_sinAnom_le (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    |K.sinAnom t| ≤ 1 := by
  have h := cosAnom_sq_add_sinAnom_sq hk hL hE t
  have h2 : K.sinAnom t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (K.cosAnom t)]
  exact (sq_le_one_iff_abs_le_one _).1 h2

/-- **Lower bound for return times**: if `x(t + T) = x(t)` with `T > 0`, then `n T` is a positive
multiple of `2π`; in particular `T ≥ 2π / n`. -/
theorem two_pi_div_le (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {t T : ℝ} (hT : 0 < T)
    (hx : K.x (t + T) = K.x t) : 2 * π / K.meanMotion ≤ T := by
  have hn := meanMotion_pos hk hL hE
  have hc : K.cosAnom (t + T) = K.cosAnom t := by rw [cosAnom, cosAnom, hx]
  have hs : K.sinAnom (t + T) = K.sinAnom t := by rw [sinAnom, sinAnom, hx]
  have hcos := cos_anomaly_sub hk hL hE t (t + T)
  rw [hc, hs, ← pow_two, ← pow_two, cosAnom_sq_add_sinAnom_sq hk hL hE] at hcos
  obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos.symm
  have hmono := anomaly_strictMono hk hL hE (show t < t + T by linarith)
  have hk1 := kepler_equation hk hL hE t
  have hk2 := kepler_equation hk hL hE (t + T)
  rw [hs] at hk2
  have hdiff : K.anomaly (t + T) - K.anomaly t = K.meanMotion * T := by
    linear_combination hk2 - hk1
  have hj0 : (0 : ℝ) < j := by
    by_contra hneg
    have hneg' : (j : ℝ) ≤ 0 := not_lt.1 hneg
    nlinarith [Real.pi_pos]
  have hj1 : (1 : ℝ) ≤ j := by
    have : (0 : ℤ) < j := by exact_mod_cast hj0
    have : (1 : ℤ) ≤ j := by omega
    exact_mod_cast this
  rw [div_le_iff₀ hn]
  nlinarith [Real.pi_pos]

/-- **Periodicity**: the motion returns to its state after the time `2π / n`:
`x(t + 2π/n) = x(t)` and `ẋ(t + 2π/n) = ẋ(t)` for all `t`. -/
theorem periodic (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.x (t + 2 * π / K.meanMotion) = K.x t ∧ K.v (t + 2 * π / K.meanMotion) = K.v t := by
  have hn := meanMotion_pos hk hL hE
  have he0 := ecc_nonneg hk
  have he1 := ecc_lt_one hk hL hE
  set M := (2 * π + 2) / K.meanMotion with hM
  have hM0 : 0 ≤ M := div_nonneg (by linarith [Real.pi_pos]) hn.le
  have hk1 := kepler_equation hk hL hE t
  have hk2 := kepler_equation hk hL hE (t + M)
  have hs1 := abs_le.1 (abs_sinAnom_le hk hL hE t)
  have hs2 := abs_le.1 (abs_sinAnom_le hk hL hE (t + M))
  have hnM : K.meanMotion * M = 2 * π + 2 := by rw [hM]; field_simp
  have hbig : K.anomaly t + 2 * π ≤ K.anomaly (t + M) := by
    nlinarith
  obtain ⟨t', -, hΦ⟩ := intermediate_value_Icc (show t ≤ t + M by linarith)
    continuous_anomaly.continuousOn
    (show K.anomaly t + 2 * π ∈ Set.Icc (K.anomaly t) (K.anomaly (t + M)) from
      ⟨by linarith [Real.pi_pos], hbig⟩)
  obtain ⟨hct, hst⟩ := anom_rotation hk hL hE t
  obtain ⟨hct', hst'⟩ := anom_rotation hk hL hE t'
  rw [hΦ, cos_add_two_pi, sin_add_two_pi] at hct' hst'
  have hc : K.cosAnom t' = K.cosAnom t := by rw [hct', hct]
  have hs : K.sinAnom t' = K.sinAnom t := by rw [hst', hst]
  have hk3 := kepler_equation hk hL hE t'
  rw [hs, hΦ] at hk3
  have ht' : t' = t + 2 * π / K.meanMotion := by
    field_simp
    linear_combination hk1 - hk3
  have hx := x_eq_of_anom hk hL hE hc hs
  rw [← ht']
  exact ⟨hx, v_eq_of_x_eq hL hx⟩

/-- The period `2π / n` is positive. -/
theorem two_pi_div_pos (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    0 < 2 * π / K.meanMotion :=
  div_pos (by linarith [Real.pi_pos]) (meanMotion_pos hk hL hE)

/-- The **minimal period** of a bound Kepler orbit is `T = 2π / n`, `n = √(k / (m a³))`. -/
theorem period_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ} (hT : 0 < T)
    (hper : ∀ t, K.x (t + T) = K.x t)
    (hmin : ∀ T', 0 < T' → (∀ t, K.x (t + T') = K.x t) → T ≤ T') :
    T = 2 * π / K.meanMotion :=
  le_antisymm (hmin _ (two_pi_div_pos hk hL hE) fun t => (periodic hk hL hE t).1)
    (two_pi_div_le hk hL hE (t := 0) hT (hper 0))

/-- The **first return time** of a bound Kepler orbit to its initial position is `T = 2π / n`. -/
theorem first_return_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ} (hT : 0 < T)
    (hx : K.x T = K.x 0) (hfirst : ∀ s, 0 < s → s < T → K.x s ≠ K.x 0) :
    T = 2 * π / K.meanMotion := by
  refine le_antisymm (not_lt.1 fun h => hfirst _ (two_pi_div_pos hk hL hE) h ?_)
    (two_pi_div_le hk hL hE (t := 0) hT (by rw [zero_add, hx]))
  simpa using (periodic hk hL hE 0).1

/-- `(2π / n)² = 4 π² m a³ / k`. -/
theorem two_pi_div_sq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    (2 * π / K.meanMotion) ^ 2 = 4 * π ^ 2 * K.m * K.semiMajor ^ 3 / K.k := by
  have := (meanMotion_pos hk hL hE).ne'
  have := (semiMajor_pos hk hL hE).ne'
  have := K.m_pos.ne'
  have := hk.ne'
  rw [div_pow, meanMotion_sq hk hL hE]
  field_simp
  ring

/-- **Kepler's third law** `T² = 4 π² m a³ / k` for the minimal period `T` of a bound Kepler orbit
(`k > 0`, `L ≠ 0`, `E < 0`). -/
theorem kepler_third_period (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ}
    (hT : 0 < T) (hper : ∀ t, K.x (t + T) = K.x t)
    (hmin : ∀ T', 0 < T' → (∀ t, K.x (t + T') = K.x t) → T ≤ T') :
    T ^ 2 = 4 * π ^ 2 * K.m * K.semiMajor ^ 3 / K.k := by
  rw [period_eq hk hL hE hT hper hmin, two_pi_div_sq hk hL hE]

/-- **Kepler's third law** `T² = 4 π² m a³ / k` for the first return time `T` of a bound Kepler
orbit to its initial position. -/
theorem kepler_third_first_return (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {T : ℝ}
    (hT : 0 < T) (hx : K.x T = K.x 0) (hfirst : ∀ s, 0 < s → s < T → K.x s ≠ K.x 0) :
    T ^ 2 = 4 * π ^ 2 * K.m * K.semiMajor ^ 3 / K.k := by
  rw [first_return_eq hk hL hE hT hx hfirst, two_pi_div_sq hk hL hE]

/-- The **swept-area hypothesis** of `kepler_third` holds for the period `T = 2π / n`: the area
swept in one period at the areal speed `|L| / (2 m)` is the area `π a b` of the ellipse. -/
theorem period_mul_areal_speed (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    2 * π / K.meanMotion * (radius (K.L 0) / (2 * K.m)) =
      π * K.semiMajor * K.semiMinor := by
  have hI := k_mul_semiMinor hk hL hE
  have hn2 := meanMotion_sq hk hL hE
  have := (meanMotion_pos hk hL hE).ne'
  have := (semiMajor_pos hk hL hE).ne'
  have := K.m_pos.ne'
  have := hk.ne'
  field_simp at hn2
  have key : radius (K.L 0) = K.meanMotion * K.m * K.semiMajor * K.semiMinor := by
    refine mul_left_cancel₀ (mul_ne_zero ‹K.meanMotion ≠ 0› (pow_ne_zero 2 ‹K.semiMajor ≠ 0›)) ?_
    linear_combination -hI - K.semiMinor * hn2
  field_simp
  rw [key]

end KeplerMotion

end ClassicalMechanics
