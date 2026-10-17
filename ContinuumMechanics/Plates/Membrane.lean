import ContinuumMechanics.Beams.String
import ContinuumMechanics.Plates.Circular
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vibrating and statically loaded membranes

A membrane is a thin elastic sheet under uniform tension `T` (per unit length) with no bending
stiffness. Its small transverse deflection `u(t, x, y)` obeys the **two-dimensional wave
equation** `u_tt = c² Δu = c² (u_xx + u_yy)`, `c² = T/ρ` ([Strauss2008], §4.2;
[Courant1962], Ch. V §5; [Timoshenko1974], §§5.25–5.26). Fields are functions
`u : ℝ → ℝ → ℝ → ℝ` of time `t` and position `(x, y)`; `dt`, `dx`, `dy` are the partial
derivatives along the corresponding sections.

## Main results

* `isWave2_sep3`: a separated field `X(x) Y(y) T(t)` with harmonic factors of wavenumbers
  `k_x`, `k_y` and angular frequency `ω` solves the wave equation when `ω² = c² (k_x² + k_y²)`.
* **Rectangular membrane** `a × b` fixed on its boundary: the normal modes
  `sin(mπx/a) sin(nπy/b) (A cos ω_mn t + B sin ω_mn t)` with
  `ω_mn = c π √((m/a)² + (n/b)²)` solve the wave equation (`isWave2_rectMode`) and vanish on
  the four edges (`rectMode_boundary`).
* `integral_rectShape_mul`: **orthogonality** of the spatial modes on the rectangle,
  `∫∫ φ_mn φ_m'n' = (ab/4) δ_mm' δ_nn'` (Fubini on `(0, a] × (0, b]` and 1D orthogonality).
* `rectOmega_comm`, `rectOmega_square_one_one`: **degeneracy of the square membrane**
  `ω_mn = ω_nm`, fundamental frequency `ω₁₁ = √2 c π/a`; `rectOmega_lt_of_lt` (frequencies
  increase with `m`).
* **Static membrane on a disk** (radial formulation on `r > 0`): `u = p (a² - r²)/(4T)` solves
  `T Δ_r u = -p` (`disk_solves`) with `u(a) = 0` (`disk_edge`) and maximal (central) deflection
  `p a²/(4T)` (`disk_center`, `disk_le_center`); `lapR_log` shows `log r` is radially harmonic
  (the singular part of the general solution `A + B log r + u_p`).

## References

* [Strauss2008] W. A. Strauss, *Partial Differential Equations: An Introduction*, 2nd ed.,
  §4.2, §10.2.
* [Courant1962] R. Courant, D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Ch. V §5.
* [Timoshenko1974] S. P. Timoshenko, D. H. Young, W. Weaver, *Vibration Problems in
  Engineering*, 4th ed., §§5.25–5.26.
-/

open Set Real MeasureTheory Filter Topology

open ContinuumMechanics.Strings (harm deriv_harm differentiable_harm integral_sin_mul_sin)

noncomputable section

namespace ContinuumMechanics.Plates.Membrane

/-! ### The two-dimensional wave equation -/

/-- Time derivative `∂ₜu(t, x, y)`. -/
def dt (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun t x y => deriv (fun s => u s x y) t

/-- Space derivative `∂ₓu(t, x, y)`. -/
def dx (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun t x y => deriv (fun s => u t s y) x

/-- Space derivative `∂ᵧu(t, x, y)`. -/
def dy (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun t x y => deriv (fun s => u t x s) y

/-- The **two-dimensional wave equation** `u_tt = c² (u_xx + u_yy)` of a membrane. -/
def IsWave2 (c : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y, dt (dt u) t x y = c ^ 2 * (dx (dx u) t x y + dy (dy u) t x y)

/-! ### Separated standing waves -/

section Separated

/-- A separated standing wave `X(x) Y(y) T(t)` with harmonic factors
`X = harm k_x p q`, `Y = harm k_y p' q'`, `T = harm ω A B`. -/
def sep3 (kx ky ω p q p' q' A B t x y : ℝ) : ℝ :=
  harm kx p q x * harm ky p' q' y * harm ω A B t

variable (kx ky ω p q p' q' A B : ℝ)

/-- Time derivative of a separated standing wave. -/
theorem dt_sep3 :
    dt (sep3 kx ky ω p q p' q' A B) = sep3 kx ky ω p q p' q' (ω * B) (-(ω * A)) := by
  funext t x y
  have h := (differentiable_harm ω A B t).hasDerivAt.const_mul (harm kx p q x * harm ky p' q' y)
  simp only [dt, sep3]
  rw [h.deriv, deriv_harm]

/-- `x`-derivative of a separated standing wave. -/
theorem dx_sep3 :
    dx (sep3 kx ky ω p q p' q' A B) = sep3 kx ky ω (kx * q) (-(kx * p)) p' q' A B := by
  funext t x y
  have h := ((differentiable_harm kx p q x).hasDerivAt.mul_const (harm ky p' q' y)).mul_const
    (harm ω A B t)
  simp only [dx, sep3]
  rw [h.deriv, deriv_harm]

/-- `y`-derivative of a separated standing wave. -/
theorem dy_sep3 :
    dy (sep3 kx ky ω p q p' q' A B) = sep3 kx ky ω p q (ky * q') (-(ky * p')) A B := by
  funext t x y
  have h := (((differentiable_harm ky p' q' y).hasDerivAt.const_mul (harm kx p q x)).mul_const
    (harm ω A B t))
  simp only [dy, sep3]
  rw [h.deriv, deriv_harm]

/-- A separated standing wave solves the membrane wave equation under the dispersion relation
`ω² = c² (k_x² + k_y²)`. -/
theorem isWave2_sep3 {c : ℝ} (hω : ω ^ 2 = c ^ 2 * (kx ^ 2 + ky ^ 2)) :
    IsWave2 c (sep3 kx ky ω p q p' q' A B) := by
  intro t x y
  rw [dt_sep3, dt_sep3, dx_sep3, dx_sep3, dy_sep3, dy_sep3]
  simp only [sep3, harm]
  linear_combination (-(p * cos (kx * x) + q * sin (kx * x)) *
    (p' * cos (ky * y) + q' * sin (ky * y)) * (A * cos (ω * t) + B * sin (ω * t))) * hω

end Separated

/-! ### The rectangular membrane -/

section Rectangle

variable (a b c : ℝ)

/-- Natural angular frequency of the `(m, n)` mode of an `a × b` membrane:
`ω_mn = c π √((m/a)² + (n/b)²)`. -/
def rectOmega (m n : ℕ) : ℝ := c * π * √((m / a) ^ 2 + (n / b) ^ 2)

/-- Spatial mode shape `φ_mn(x, y) = sin(mπx/a) sin(nπy/b)`. -/
def rectShape (m n : ℕ) (x y : ℝ) : ℝ := sin (m * π / a * x) * sin (n * π / b * y)

/-- The `(m, n)` **normal mode** of the rectangular membrane fixed on its boundary:
`sin(mπx/a) sin(nπy/b) (A cos ω_mn t + B sin ω_mn t)`. -/
def rectMode (m n : ℕ) (A B t x y : ℝ) : ℝ :=
  rectShape a b m n x y * (A * cos (rectOmega a b c m n * t) + B * sin (rectOmega a b c m n * t))

/-- A rectangular mode is a separated standing wave. -/
theorem rectMode_eq_sep3 (m n : ℕ) (A B : ℝ) :
    rectMode a b c m n A B = sep3 (m * π / a) (n * π / b) (rectOmega a b c m n) 0 1 0 1 A B := by
  funext t x y
  simp [rectMode, rectShape, sep3, harm]

/-- Dispersion relation of the rectangular modes: `ω_mn² = c² ((mπ/a)² + (nπ/b)²)`. -/
theorem rectOmega_sq (m n : ℕ) :
    rectOmega a b c m n ^ 2 = c ^ 2 * ((m * π / a) ^ 2 + (n * π / b) ^ 2) := by
  rw [rectOmega, mul_pow, sq_sqrt (by positivity)]
  ring

/-- **The rectangular modes solve the membrane wave equation.** -/
theorem isWave2_rectMode (m n : ℕ) (A B : ℝ) : IsWave2 c (rectMode a b c m n A B) := by
  rw [rectMode_eq_sep3]
  exact isWave2_sep3 _ _ _ _ _ _ _ _ _ (rectOmega_sq a b c m n)

/-- **The rectangular modes vanish on the boundary** `x = 0`, `x = a`, `y = 0`, `y = b`. -/
theorem rectMode_boundary {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℕ) (A B t : ℝ) :
    (∀ y, rectMode a b c m n A B t 0 y = 0) ∧ (∀ y, rectMode a b c m n A B t a y = 0) ∧
      (∀ x, rectMode a b c m n A B t x 0 = 0) ∧ (∀ x, rectMode a b c m n A B t x b = 0) := by
  simp only [rectMode, rectShape, div_mul_cancel₀ _ ha, div_mul_cancel₀ _ hb, sin_nat_mul_pi]
  simp

/-- **Orthogonality of the rectangular mode shapes**:
`∫₀ᵃ∫₀ᵇ φ_mn φ_m'n' dy dx = (ab/4) δ_mm' δ_nn'` for `m', n' ≥ 1` (Fubini and the
one-dimensional orthogonality of sines). -/
theorem integral_rectShape_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n m' n' : ℕ}
    (hm' : m' ≠ 0) (hn' : n' ≠ 0) :
    ∫ z in Ioc 0 a ×ˢ Ioc 0 b, rectShape a b m n z.1 z.2 * rectShape a b m' n' z.1 z.2 =
      if m = m' ∧ n = n' then a * b / 4 else 0 := by
  have e : ∀ z : ℝ × ℝ, rectShape a b m n z.1 z.2 * rectShape a b m' n' z.1 z.2 =
      (sin (m * π / a * z.1) * sin (m' * π / a * z.1)) *
        (sin (n * π / b * z.2) * sin (n' * π / b * z.2)) := fun z => by
    simp only [rectShape]; ring
  simp_rw [e]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul
      (fun x => sin (m * π / a * x) * sin (m' * π / a * x))
      (fun y => sin (n * π / b * y) * sin (n' * π / b * y)),
    ← intervalIntegral.integral_of_le ha.le, ← intervalIntegral.integral_of_le hb.le,
    integral_sin_mul_sin ha.ne' hm', integral_sin_mul_sin hb.ne' hn']
  by_cases h1 : m = m' <;> by_cases h2 : n = n' <;> simp [h1, h2]
  ring

/-- **Degeneracy of the square membrane**: for `a = b`, `ω_mn = ω_nm`. -/
theorem rectOmega_comm (m n : ℕ) : rectOmega a a c m n = rectOmega a a c n m := by
  rw [rectOmega, rectOmega, add_comm]

/-- Fundamental frequency of the square membrane: `ω₁₁ = √2 c π/a` for `a > 0`. -/
theorem rectOmega_square_one_one {a : ℝ} (ha : 0 < a) :
    rectOmega a a c 1 1 = √2 * c * π / a := by
  have h : ((1 : ℕ) / a : ℝ) ^ 2 + ((1 : ℕ) / a) ^ 2 = 2 * (1 / a) ^ 2 := by push_cast; ring
  rw [rectOmega, h, sqrt_mul zero_le_two, sqrt_sq (by positivity)]
  field_simp

/-- Frequencies increase with the mode number: `ω_mn < ω_m'n` for `m < m'`, `c > 0`,
`a > 0`. -/
theorem rectOmega_lt_of_lt {a : ℝ} (ha : 0 < a) {c : ℝ} (hc : 0 < c) {m m' : ℕ} (h : m < m')
    (n : ℕ) : rectOmega a b c m n < rectOmega a b c m' n := by
  unfold rectOmega
  have hmm : (m : ℝ) / a < m' / a := div_lt_div_of_pos_right (by exact_mod_cast h) ha
  have h0 : (0 : ℝ) ≤ m / a := by positivity
  have hsq : ((m : ℝ) / a) ^ 2 < (m' / a) ^ 2 := pow_lt_pow_left₀ hmm h0 two_ne_zero
  exact mul_lt_mul_of_pos_left (sqrt_lt_sqrt (by positivity) (by linarith)) (by positivity)

end Rectangle

/-! ### Static membrane under uniform pressure on a disk -/

section Disk

open ContinuumMechanics.Plates.Circular (lapR lapR_eq)

variable (p T a : ℝ)

/-- Deflection of a circular membrane of radius `a`, tension `T`, under uniform pressure `p`:
`u = p (a² - r²)/(4T)`. -/
def disk (r : ℝ) : ℝ := p * (a ^ 2 - r ^ 2) / (4 * T)

/-- `u' = -p r/(2T)`. -/
theorem hasDerivAt_disk (r : ℝ) : HasDerivAt (disk p T a) (-(p * r) / (2 * T)) r := by
  have h := (((hasDerivAt_pow 2 r).const_sub (a ^ 2)).const_mul p).div_const (4 * T)
  exact h.congr_deriv (by field_simp; ring)

/-- `u'' = -p/(2T)`. -/
theorem hasDerivAt_disk_deriv (r : ℝ) :
    HasDerivAt (fun s => -(p * s) / (2 * T)) (-p / (2 * T)) r := by
  have h := (((hasDerivAt_id' r).const_mul p).neg).div_const (2 * T)
  convert h using 1
  ring

/-- **Poisson equation of the membrane**: `T Δ_r u = -p` on `r > 0` (for `T ≠ 0`). -/
theorem disk_solves (hT : T ≠ 0) {r : ℝ} (hr : 0 < r) : T * lapR (disk p T a) r = -p := by
  rw [lapR_eq (fun s _ => hasDerivAt_disk p T a s) (fun s _ => hasDerivAt_disk_deriv p T s) hr]
  field_simp
  ring

/-- Fixed rim: `u(a) = 0`. -/
theorem disk_edge : disk p T a a = 0 := by simp [disk]

/-- Central deflection `u(0) = p a²/(4T)`. -/
theorem disk_center : disk p T a 0 = p * a ^ 2 / (4 * T) := by simp [disk]

/-- The central deflection is maximal: `0 ≤ u(r) ≤ u(0)` for `0 ≤ r ≤ a`, `p ≥ 0`, `T > 0`. -/
theorem disk_le_center (hp : 0 ≤ p) (hT : 0 < T) {r : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) :
    0 ≤ disk p T a r ∧ disk p T a r ≤ disk p T a 0 := by
  simp only [disk]
  have h1 : 0 ≤ a ^ 2 - r ^ 2 := by nlinarith
  have h2 : a ^ 2 - r ^ 2 ≤ a ^ 2 - 0 ^ 2 := by nlinarith
  exact ⟨by positivity, div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hp)
    (by positivity)⟩

/-- `log r` is radially harmonic on `r > 0`: `Δ_r log = 0`. Hence `u + A + B log r` also solves
`T Δ_r u = -p`, and regularity at the centre singles out `B = 0`. -/
theorem lapR_log {r : ℝ} (hr : 0 < r) : lapR log r = 0 := by
  have h₂ : ∀ s > (0 : ℝ), HasDerivAt (fun s : ℝ => s⁻¹) (-(s ^ 2)⁻¹) s :=
    fun s hs => hasDerivAt_inv hs.ne'
  rw [lapR_eq (fun s hs => hasDerivAt_log (ne_of_gt hs)) h₂ hr]
  field_simp
  ring

end Disk

end ContinuumMechanics.Plates.Membrane
