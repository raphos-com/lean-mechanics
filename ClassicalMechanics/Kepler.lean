import ClassicalMechanics.Vector
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Kepler problem

A particle of mass `m > 0` moves under the attractive inverse-square central force

`m ẍ = -(k / r³) x`,  `r = |x| > 0`

(gravitation `k = G M m`, or Coulomb attraction) ([Goldstein2002], §§3.7–3.9; [Arnold1989], §8).

* **Angular momentum** `L = x × m ẋ` is conserved (`angMom_const`), so the motion is planar,
  `x · L = 0` (`planar`), and the areal velocity `½ x × ẋ` is constant: **Kepler's second law**
  (`areal_velocity_const`).
* **Energy** `E = ½ m |ẋ|² - k / r` is conserved (`energy_const`).
* The **Laplace–Runge–Lenz vector** `A = p × L - m k x / r` (`p = m ẋ`) is conserved (`lrl_const`)
  and lies in the plane of the orbit (`lrl_dot_angMom`).
* **Kepler's first law** (`orbit_equation`): `A · x + m k r = |L|²`, i.e.
  `r = |L|² / (m k) - ε · x` with the eccentricity vector `ε = A / (m k)`: the orbit is a **conic
  with a focus at the origin** and eccentricity `e = |ε|`.
* **Eccentricity and energy** (`lrl_sq`): `|A|² = m² k² + 2 m E |L|²`, i.e.
  `e² = 1 + 2 E |L|² / (m k²)`; so for `k > 0` and `L ≠ 0`, the orbit is an **ellipse** (`e < 1`)
  iff the energy is negative (`ecc_lt_one_iff`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.7–3.9.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §8.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- Euclidean length `|x| = √(x · x)`. -/
def radius (x : Vec) : ℝ := √(x ⬝ᵥ x)

theorem dot_self_pos {x : Vec} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (normSq_nonneg x) (fun h => hx (dotProduct_self_eq_zero.mp h.symm))

theorem radius_pos {x : Vec} (hx : x ≠ 0) : 0 < radius x := Real.sqrt_pos.mpr (dot_self_pos hx)

theorem radius_sq (x : Vec) : radius x ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (normSq_nonneg x)

/-- A **Kepler motion**: `m ẍ = -(k / r³) x` with `x ≠ 0`. -/
structure KeplerMotion where
  m : ℝ
  k : ℝ
  m_pos : 0 < m
  x : ℝ → Vec
  v : ℝ → Vec
  a : ℝ → Vec
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  ne_zero : ∀ t, x t ≠ 0
  newton : ∀ t, m • a t = -(k / radius (x t) ^ 3) • x t

namespace KeplerMotion

variable (K : KeplerMotion)

/-- The distance to the centre of force. -/
def r (t : ℝ) : ℝ := radius (K.x t)

/-- Angular momentum `L = x × m ẋ`. -/
def L (t : ℝ) : Vec := K.x t ⨯₃ (K.m • K.v t)

/-- Energy `E = ½ m |ẋ|² - k / r`. -/
def E (t : ℝ) : ℝ := K.m / 2 * (K.v t ⬝ᵥ K.v t) - K.k / K.r t

/-- The Laplace–Runge–Lenz vector `A = p × L - m k x / r`. -/
def A (t : ℝ) : Vec := (K.m • K.v t) ⨯₃ K.L t - (K.m * K.k / K.r t) • K.x t

theorem r_pos (t : ℝ) : 0 < K.r t := radius_pos (K.ne_zero t)

theorem r_sq (t : ℝ) : K.r t ^ 2 = K.x t ⬝ᵥ K.x t := radius_sq _

theorem hasDerivAt_r (t : ℝ) : HasDerivAt K.r (K.x t ⬝ᵥ K.v t / K.r t) t := by
  have h := (hasDerivAt_dot (K.hasDerivAt_x t) (K.hasDerivAt_x t)).sqrt
    (dot_self_pos (K.ne_zero t)).ne'
  have hr := (K.r_pos t).ne'
  convert h using 1
  · rfl
  rw [dotProduct_comm (K.v t)]
  change _ = _ / (2 * K.r t)
  field_simp
  ring

theorem hasDerivAt_inv_r (t : ℝ) :
    HasDerivAt (fun s => (K.r s)⁻¹) (-(K.x t ⬝ᵥ K.v t) / K.r t ^ 3) t := by
  have h := (K.hasDerivAt_r t).inv (K.r_pos t).ne'
  have hr := (K.r_pos t).ne'
  convert h using 1
  field_simp

/-- `L̇ = 0`. -/
theorem hasDerivAt_L (t : ℝ) : HasDerivAt K.L 0 t := by
  have h := hasDerivAt_cross (K.hasDerivAt_x t) ((K.hasDerivAt_v t).const_smul K.m)
  convert h using 1
  · rfl
  rw [Pi.smul_apply, K.newton, map_smul, map_smul, cross_self, cross_self, smul_zero, smul_zero,
    add_zero]

/-- **Conservation of angular momentum**. -/
theorem angMom_const (s t : ℝ) : K.L s = K.L t := eq_of_hasDerivAt_zero K.hasDerivAt_L s t

/-- The motion is **planar**: `x · L = 0`. -/
theorem planar (t : ℝ) : K.x t ⬝ᵥ K.L 0 = 0 := by
  rw [← K.angMom_const t 0, L, dot_self_cross]

/-- **Kepler's second law**: the areal velocity `½ x × ẋ` is constant. -/
theorem areal_velocity_const (s t : ℝ) :
    (1 / 2 : ℝ) • (K.x s ⨯₃ K.v s) = (1 / 2 : ℝ) • (K.x t ⨯₃ K.v t) := by
  have h := K.angMom_const s t
  simp only [L, map_smul] at h
  rw [smul_right_injective _ K.m_pos.ne' h]

/-- **Conservation of energy**. -/
theorem energy_const (s t : ℝ) : K.E s = K.E t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((hasDerivAt_dot (K.hasDerivAt_v t) (K.hasDerivAt_v t)).const_mul (K.m / 2)).sub
    ((K.hasDerivAt_inv_r t).const_mul K.k)
  have hr := (K.r_pos t).ne'
  have hma : K.m * (K.a t ⬝ᵥ K.v t) = -(K.k / K.r t ^ 3) * (K.x t ⬝ᵥ K.v t) := by
    rw [← smul_eq_mul, ← smul_dotProduct, K.newton, smul_dotProduct, smul_eq_mul]; rfl
  convert h using 1
  · funext s; simp [E, div_eq_mul_inv]
  · rw [dotProduct_comm (K.v t) (K.a t)]
    have : K.m / 2 * (K.a t ⬝ᵥ K.v t + K.a t ⬝ᵥ K.v t) = K.m * (K.a t ⬝ᵥ K.v t) := by ring
    rw [this, hma]
    field_simp
    ring

/-- **Conservation of the Laplace–Runge–Lenz vector**. -/
theorem lrl_const (s t : ℝ) : K.A s = K.A t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have hL : HasDerivAt K.L 0 t := K.hasDerivAt_L t
  have h1 := hasDerivAt_cross ((K.hasDerivAt_v t).const_smul K.m) hL
  have h2 := ((K.hasDerivAt_inv_r t).const_mul (K.m * K.k)).smul (K.hasDerivAt_x t)
  have h := h1.sub h2
  have hr := (K.r_pos t).ne'
  convert h using 1
  · funext s; simp [A, div_eq_mul_inv]
  · symm
    have hR : K.r t = radius (K.x t) := rfl
    rw [Pi.smul_apply, map_zero, add_zero, K.newton, L]
    simp only [map_smul, LinearMap.smul_apply, cross_cross_eq_smul_sub_smul', ← hR]
    rw [← K.r_sq]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    ring

/-- The LRL vector lies in the plane of the orbit: `A · L = 0`. -/
theorem lrl_dot_angMom (t : ℝ) : K.A t ⬝ᵥ K.L t = 0 := by
  have hp : K.x t ⬝ᵥ K.L t = 0 := by rw [L, dot_self_cross]
  rw [A, sub_dotProduct, smul_dotProduct, hp, smul_zero, dotProduct_comm, dot_cross_self,
    sub_zero]

/-- **Kepler's first law** (orbit equation): `A · x + m k r = |L|²`. With `ε = A / (m k)`, the
orbit `r = |L|²/(m k) - ε · x` is a conic with a focus at the origin and eccentricity `|ε|`. -/
theorem orbit_equation (t : ℝ) : K.A t ⬝ᵥ K.x t + K.m * K.k * K.r t = K.L t ⬝ᵥ K.L t := by
  have hr := (K.r_pos t).ne'
  have htp : (K.m • K.v t) ⨯₃ K.L t ⬝ᵥ K.x t = K.L t ⬝ᵥ K.L t := by
    rw [dotProduct_comm, triple_product_permutation, triple_product_permutation, L]
  rw [A, sub_dotProduct, htp, smul_dotProduct, ← K.r_sq, smul_eq_mul]
  field_simp
  ring

/-- **Eccentricity and energy**: `|A|² = m² k² + 2 m E |L|²`. -/
theorem lrl_sq (t : ℝ) :
    K.A t ⬝ᵥ K.A t = K.m ^ 2 * K.k ^ 2 + 2 * K.m * K.E t * (K.L t ⬝ᵥ K.L t) := by
  have hr := (K.r_pos t).ne'
  have hpL : (K.m • K.v t) ⬝ᵥ K.L t = 0 := by rw [L, dot_cross_self]
  have htp : (K.m • K.v t) ⨯₃ K.L t ⬝ᵥ K.x t = K.L t ⬝ᵥ K.L t := by
    rw [dotProduct_comm, triple_product_permutation, triple_product_permutation, L]
  have hcc : (K.m • K.v t) ⨯₃ K.L t ⬝ᵥ (K.m • K.v t) ⨯₃ K.L t =
      K.m ^ 2 * (K.v t ⬝ᵥ K.v t) * (K.L t ⬝ᵥ K.L t) := by
    rw [cross_dot_cross, hpL, dotProduct_comm (K.L t) (K.m • K.v t), hpL, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [A, sub_dotProduct, dotProduct_sub, dotProduct_sub, hcc, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, htp, dotProduct_comm (K.x t), htp, dotProduct_smul, ← K.r_sq, E]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- **Bound orbits**: for `L ≠ 0`, the eccentricity
`e = |A| / (m k)` is less than `1` (an ellipse) iff the energy is negative. -/
theorem ecc_lt_one_iff (hL : K.L 0 ≠ 0) (t : ℝ) :
    K.A t ⬝ᵥ K.A t < (K.m * K.k) ^ 2 ↔ K.E t < 0 := by
  have hLL : 0 < K.L t ⬝ᵥ K.L t := by rw [K.angMom_const t 0]; exact dot_self_pos hL
  rw [K.lrl_sq]
  constructor
  · intro h
    by_contra hE
    have : 0 ≤ 2 * K.m * K.E t * (K.L t ⬝ᵥ K.L t) :=
      mul_nonneg (mul_nonneg (by linarith [K.m_pos]) (not_lt.mp hE)) hLL.le
    nlinarith
  · intro hE
    have : 2 * K.m * K.E t * (K.L t ⬝ᵥ K.L t) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith [K.m_pos]) hE) hLL
    nlinarith

end KeplerMotion

end ClassicalMechanics
