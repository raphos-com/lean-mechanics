import ContinuumMechanics.Plates.Navier

/-!
# Vibration and buckling of simply supported rectangular plates

A simply supported Kirchhoff–Love plate `[0, a] × [0, b]` (`Plates/KirchhoffLove`) with flexural
rigidity `D = E h³ / (12(1 - ν²)) > 0` and mass per unit area `ρh > 0`.

* **Free vibration** `ρh w_tt + D Δ²w = 0`. The spatial modes
  `φ_mn = sin(mπx/a) sin(nπy/b)` satisfy `Δ²φ_mn = π⁴((m/a)² + (n/b)²)² φ_mn` and the simply
  supported conditions `w = w_xx = 0` on `x = 0, a`, `w = w_yy = 0` on `y = 0, b`; the
  standing waves `φ_mn(x, y)(A cos ωt + B sin ωt)` with
  `ω_mn = π²((m/a)² + (n/b)²) √(D/(ρh))` solve the equation of motion.
* **Buckling under uniaxial compression** `N_x`: `D Δ²w + N_x w_xx = 0`. The mode
  `sin(mπx/a) sin(nπy/b)` is a solution iff `N_x = D π² (a/m)² ((m/a)² + (n/b)²)²`; the load is
  smallest for `n = 1`, where `N_x = k π² D / b²` with buckling coefficient
  `k = (m b/a + a/(m b))² ≥ 4`, with equality iff `a/b = m`.
* **Biaxial compression** `N_x, N_y`: the mode condition
  `D π² ((m/a)² + (n/b)²)² = N_x (m/a)² + N_y (n/b)²`.

## Main results

* `Plates.biharm_phi`: `Δ²φ_mn = π⁴((m/a)² + (n/b)²)² φ_mn`.
* `Plates.Plate.phi_simplySupported`: `φ_mn` satisfies the simply supported conditions.
* `Plates.VibPlate.vibMode_solves`: the standing waves solve `ρh w_tt + D Δ²w = 0`.
* `Plates.VibPlate.freq_one_one_le`, `freq_square`, `freq_square_symm`: fundamental frequency,
  square plates and the degeneracy `ω_mn = ω_nm`.
* `Plates.Plate.buckling_iff`, `bucklingLoad_one_le`, `bucklingLoad_eq_coeff`,
  `four_le_bucklingCoeff`, `bucklingCoeff_eq_four_iff`, `critical_load`: uniaxial buckling.
* `Plates.Plate.biaxial_iff`: biaxial buckling condition.

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, §28.
* [TimoshenkoGere1961] S. P. Timoshenko, J. M. Gere, *Theory of Elastic Stability*, §§9.2–9.5.
* [Leissa1969] A. W. Leissa, *Vibration of Plates*, NASA SP-160, Ch. 4.
-/

open Set Real
open scoped Real

namespace ContinuumMechanics.Plates

/-! ### Spatial modes -/

/-- The simply supported spatial mode `φ_mn(x, y) = sin(mπx/a) sin(nπy/b)`. -/
noncomputable def phi (a b : ℝ) (m n : ℕ) : ℝ → ℝ → ℝ := mode 1 (m * π / a) (n * π / b)

/-- `φ_mn(x, y) = sin(mπx/a) sin(nπy/b)`. -/
theorem phi_apply (a b : ℝ) (m n : ℕ) (x y : ℝ) :
    phi a b m n x y = sin (m * π / a * x) * sin (n * π / b * y) := by
  simp [phi, mode_apply]

/-- **Plate eigenvalue of a mode**: `Δ²φ_mn = π⁴((m/a)² + (n/b)²)² φ_mn`. -/
theorem biharm_phi (a b : ℝ) (m n : ℕ) (x y : ℝ) :
    biharm (phi a b m n) x y = π ^ 4 * ((m / a) ^ 2 + (n / b) ^ 2) ^ 2 * phi a b m n x y := by
  rw [phi, biharm_mode]
  ring

/-- The **simply supported conditions** in their geometric form: `w = w_xx = 0` on `x = 0, a`
and `w = w_yy = 0` on `y = 0, b`. -/
def Plate.SimplySupportedW (p : Plate) (w : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, w 0 y = 0 ∧ w p.a y = 0 ∧ dx (dx w) 0 y = 0 ∧ dx (dx w) p.a y = 0) ∧
    ∀ x, w x 0 = 0 ∧ w x p.b = 0 ∧ dy (dy w) x 0 = 0 ∧ dy (dy w) x p.b = 0

/-- If `w` vanishes along the line `x = x₀`, so does `w_yy`. -/
theorem dy_dy_eq_zero_of_line {w : ℝ → ℝ → ℝ} {x₀ : ℝ} (h : ∀ y, w x₀ y = 0) (y : ℝ) :
    dy (dy w) x₀ y = 0 := by
  have h1 : (fun t => dy w x₀ t) = fun _ => 0 := by
    funext t
    simp only [dy]
    rw [show (fun t => w x₀ t) = fun _ => 0 from funext h]
    simp
  simp only [dy] at h1 ⊢
  rw [h1]
  simp

/-- If `w` vanishes along the line `y = y₀`, so does `w_xx`. -/
theorem dx_dx_eq_zero_of_line {w : ℝ → ℝ → ℝ} {y₀ : ℝ} (h : ∀ x, w x y₀ = 0) (x : ℝ) :
    dx (dx w) x y₀ = 0 := by
  have h1 : (fun s => dx w s y₀) = fun _ => 0 := by
    funext s
    simp only [dx]
    rw [show (fun s => w s y₀) = fun _ => 0 from funext h]
    simp
  simp only [dx] at h1 ⊢
  rw [h1]
  simp

namespace Plate

variable (p : Plate)

/-- The geometric simply supported conditions imply the moment form
`Plate.SimplySupported` (`w = 0`, `M_n = 0`), for every Poisson ratio. -/
theorem SimplySupportedW.simplySupported {w : ℝ → ℝ → ℝ} (h : p.SimplySupportedW w) :
    p.SimplySupported w := by
  obtain ⟨hx, hy⟩ := h
  refine ⟨fun y => ⟨(hx y).1, (hx y).2.1, ?_, ?_⟩, fun x => ⟨(hy x).1, (hy x).2.1, ?_, ?_⟩⟩
  · simp [momentX, (hx y).2.2.1, dy_dy_eq_zero_of_line (fun t => (hx t).1) y]
  · simp [momentX, (hx y).2.2.2, dy_dy_eq_zero_of_line (fun t => (hx t).2.1) y]
  · simp [momentY, (hy x).2.2.1, dx_dx_eq_zero_of_line (fun s => (hy s).1) x]
  · simp [momentY, (hy x).2.2.2, dx_dx_eq_zero_of_line (fun s => (hy s).2.1) x]

/-- Every separable mode `A sin(mπx/a) sin(nπy/b)` satisfies the simply supported conditions. -/
theorem mode_simplySupportedW (A : ℝ) (m n : ℕ) :
    p.SimplySupportedW (mode A (m * π / p.a) (n * π / p.b)) := by
  refine ⟨fun y => ?_, fun x => ?_⟩
  · simp only [dx_dx_mode, mode_zero_left, p.mode_nat_right, mul_zero, and_self]
  · simp only [dy_dy_mode, mode_zero_bottom, p.mode_nat_top, mul_zero, and_self]

/-- `φ_mn` satisfies the simply supported conditions. -/
theorem phi_simplySupported (m n : ℕ) : p.SimplySupportedW (phi p.a p.b m n) :=
  p.mode_simplySupportedW 1 m n

/-- A mode with `m, n ≥ 1` takes the value `A` at `(a/(2m), b/(2n))`. -/
theorem mode_peak (A : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    mode A (m * π / p.a) (n * π / p.b) (p.a / (2 * m)) (p.b / (2 * n)) = A := by
  have ha := p.a_pos.ne'
  have hb := p.b_pos.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [mode_apply, show m * π / p.a * (p.a / (2 * m)) = π / 2 by field_simp,
    show n * π / p.b * (p.b / (2 * n)) = π / 2 by field_simp, sin_pi_div_two]
  ring

/-- **Mode condition** for the general operator `c₁ Δ²w + c₂ w_xx + c₃ w_yy`: a nonzero mode
`A sin(αx) sin(βy)`, `α = mπ/a`, `β = nπ/b`, `m, n ≥ 1`, is annihilated iff
`c₁ (α² + β²)² = c₂ α² + c₃ β²`. -/
theorem mode_operator_iff (c₁ c₂ c₃ : ℝ) {A : ℝ} (hA : A ≠ 0) {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) :
    (∀ x y, c₁ * biharm (mode A (m * π / p.a) (n * π / p.b)) x y +
        c₂ * dx (dx (mode A (m * π / p.a) (n * π / p.b))) x y +
        c₃ * dy (dy (mode A (m * π / p.a) (n * π / p.b))) x y = 0) ↔
      c₁ * ((m * π / p.a) ^ 2 + (n * π / p.b) ^ 2) ^ 2 =
        c₂ * (m * π / p.a) ^ 2 + c₃ * (n * π / p.b) ^ 2 := by
  simp only [biharm_mode, dx_dx_mode, dy_dy_mode]
  constructor
  · intro h
    have := h (p.a / (2 * m)) (p.b / (2 * n))
    rw [p.mode_peak A hm hn] at this
    have h2 : (c₁ * ((m * π / p.a) ^ 2 + (n * π / p.b) ^ 2) ^ 2 -
        (c₂ * (m * π / p.a) ^ 2 + c₃ * (n * π / p.b) ^ 2)) * A = 0 := by
      linear_combination this
    linear_combination (mul_eq_zero.mp h2).resolve_right hA
  · intro h x y
    linear_combination mode A (m * π / p.a) (n * π / p.b) x y * h

end Plate

/-! ### Free vibration -/

/-- A rectangular Kirchhoff–Love plate with mass per unit area `ρh > 0`. -/
structure VibPlate extends Plate where
  /-- Mass per unit area `ρh`. -/
  rhoH : ℝ
  rhoH_pos : 0 < rhoH

/-- Time derivative `∂/∂t` of a time-dependent deflection `w(t, x, y)`. -/
noncomputable def dt (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun t x y =>
  deriv (fun s => w s x y) t

namespace VibPlate

variable (p : VibPlate)

/-- The **free vibration equation** `ρh w_tt + D Δ²w = 0` (for all times, on the rectangle).
[TimoshenkoWoinowsky1959], §28; [Leissa1969], Ch. 4. -/
def FreeVibration (w : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t, ∀ x ∈ Icc 0 p.a, ∀ y ∈ Icc 0 p.b, p.rhoH * dt (dt w) t x y + p.D * biharm (w t) x y = 0

/-- The natural frequency `ω_mn = π²((m/a)² + (n/b)²) √(D/(ρh))`. -/
noncomputable def freq (m n : ℕ) : ℝ :=
  π ^ 2 * ((m / p.a) ^ 2 + (n / p.b) ^ 2) * √(p.D / p.rhoH)

/-- The standing wave `w_mn(t, x, y) = φ_mn(x, y)(A cos ωt + B sin ωt)`, `ω = ω_mn`. -/
noncomputable def vibMode (A B : ℝ) (m n : ℕ) (t : ℝ) : ℝ → ℝ → ℝ :=
  mode (A * cos (p.freq m n * t) + B * sin (p.freq m n * t)) (m * π / p.a) (n * π / p.b)

/-- `w_mn(t, x, y) = φ_mn(x, y)(A cos ω_mn t + B sin ω_mn t)`. -/
theorem vibMode_apply (A B : ℝ) (m n : ℕ) (t x y : ℝ) :
    p.vibMode A B m n t x y =
      phi p.a p.b m n x y * (A * cos (p.freq m n * t) + B * sin (p.freq m n * t)) := by
  rw [vibMode, mode_apply, phi_apply]; ring

/-- `ω_mn² ρh = D π⁴ ((m/a)² + (n/b)²)²`: the dispersion relation. -/
theorem freq_sq (m n : ℕ) :
    p.rhoH * p.freq m n ^ 2 = p.D * (π ^ 4 * ((m / p.a) ^ 2 + (n / p.b) ^ 2) ^ 2) := by
  have hr := p.rhoH_pos
  have hs : √(p.D / p.rhoH) ^ 2 = p.D / p.rhoH := sq_sqrt (div_pos p.D_pos hr).le
  rw [freq, mul_pow, hs]
  field_simp

/-- `d/dt (A cos ωt + B sin ωt) = ω (B cos ωt - A sin ωt)`. -/
theorem hasDerivAt_timeFactor (A B ω t : ℝ) :
    HasDerivAt (fun s => A * cos (ω * s) + B * sin (ω * s))
      (ω * (B * cos (ω * t) - A * sin (ω * t))) t := by
  have h1 := ((hasDerivAt_id' t).const_mul ω).cos.const_mul A
  have h2 := ((hasDerivAt_id' t).const_mul ω).sin.const_mul B
  convert h1.add h2 using 1
  ring

/-- `d/dt (ω (B cos ωt - A sin ωt)) = -ω² (A cos ωt + B sin ωt)`. -/
theorem hasDerivAt_timeFactor' (A B ω t : ℝ) :
    HasDerivAt (fun s => ω * (B * cos (ω * s) - A * sin (ω * s)))
      (-ω ^ 2 * (A * cos (ω * t) + B * sin (ω * t))) t := by
  have h1 := ((hasDerivAt_id' t).const_mul ω).cos.const_mul B
  have h2 := ((hasDerivAt_id' t).const_mul ω).sin.const_mul A
  convert (h1.sub h2).const_mul ω using 1
  ring

/-- Second time derivative of a standing wave: `∂²w_mn/∂t² = -ω_mn² w_mn`. -/
theorem dt_dt_vibMode (A B : ℝ) (m n : ℕ) (t x y : ℝ) :
    dt (dt (p.vibMode A B m n)) t x y = -p.freq m n ^ 2 * p.vibMode A B m n t x y := by
  set ω := p.freq m n
  have e : ∀ s, p.vibMode A B m n s x y =
      (A * cos (ω * s) + B * sin (ω * s)) * phi p.a p.b m n x y := fun s => by
    rw [vibMode_apply]; ring
  have h1 : (fun s => dt (p.vibMode A B m n) s x y) =
      fun s => ω * (B * cos (ω * s) - A * sin (ω * s)) * phi p.a p.b m n x y := by
    funext s
    simp only [dt, e]
    exact ((hasDerivAt_timeFactor A B ω s).mul_const _).deriv
  simp only [dt] at h1 ⊢
  rw [h1, ((hasDerivAt_timeFactor' A B ω t).mul_const _).deriv, e]
  ring

/-- **Free vibration modes**: the standing waves
`w_mn = sin(mπx/a) sin(nπy/b)(A cos ω_mn t + B sin ω_mn t)` solve `ρh w_tt + D Δ²w = 0` and
satisfy the simply supported conditions at every time. [TimoshenkoWoinowsky1959], §28;
[Leissa1969], §4.1. -/
theorem vibMode_solves (A B : ℝ) (m n : ℕ) :
    p.FreeVibration (p.vibMode A B m n) ∧
      ∀ t, p.SimplySupportedW (p.vibMode A B m n t) := by
  refine ⟨fun t x _ y _ => ?_, fun t => p.mode_simplySupportedW _ m n⟩
  have hb : biharm (p.vibMode A B m n t) x y =
      π ^ 4 * ((m / p.a) ^ 2 + (n / p.b) ^ 2) ^ 2 * p.vibMode A B m n t x y := by
    rw [vibMode, biharm_mode]; ring
  rw [dt_dt_vibMode, hb]
  linear_combination (-p.vibMode A B m n t x y) * p.freq_sq m n

/-- The frequencies are positive for `m ≥ 1` or `n ≥ 1`. -/
theorem freq_pos {m n : ℕ} (h : 0 < m ∨ 0 < n) : 0 < p.freq m n := by
  have hs : 0 < √(p.D / p.rhoH) := sqrt_pos.mpr (div_pos p.D_pos p.rhoH_pos)
  have hq : 0 < (m / p.a) ^ 2 + (n / p.b) ^ 2 := by
    rcases h with h | h
    · have : 0 < (m / p.a) ^ 2 := pow_pos (div_pos (Nat.cast_pos.mpr h) p.a_pos) 2
      positivity
    · have : 0 < (n / p.b) ^ 2 := pow_pos (div_pos (Nat.cast_pos.mpr h) p.b_pos) 2
      positivity
  unfold freq
  positivity

/-- The **fundamental frequency** `ω₁₁ = π²(1/a² + 1/b²) √(D/(ρh))`. -/
theorem freq_one_one : p.freq 1 1 = π ^ 2 * (1 / p.a ^ 2 + 1 / p.b ^ 2) * √(p.D / p.rhoH) := by
  simp [freq]

/-- `ω₁₁` is the lowest frequency: `ω₁₁ ≤ ω_mn` for all `m, n ≥ 1`. -/
theorem freq_one_one_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : p.freq 1 1 ≤ p.freq m n := by
  have hs : 0 ≤ √(p.D / p.rhoH) := sqrt_nonneg _
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((1 : ℕ) / p.a) ^ 2 ≤ (m / p.a) ^ 2 := by
    rw [div_pow, div_pow]
    gcongr
  have h2 : ((1 : ℕ) / p.b) ^ 2 ≤ (n / p.b) ^ 2 := by
    rw [div_pow, div_pow]
    gcongr
  unfold freq
  gcongr

/-- **Square plate** (`a = b`): `ω_mn = (π²/a²)(m² + n²) √(D/(ρh))`. -/
theorem freq_square (hab : p.a = p.b) (m n : ℕ) :
    p.freq m n = π ^ 2 / p.a ^ 2 * (m ^ 2 + n ^ 2) * √(p.D / p.rhoH) := by
  rw [freq, ← hab]
  field_simp

/-- **Degenerate frequencies** on a square plate: `ω_mn = ω_nm`, so the distinct modes
`φ_mn` and `φ_nm` (`m ≠ n`) share a frequency. -/
theorem freq_square_symm (hab : p.a = p.b) (m n : ℕ) : p.freq m n = p.freq n m := by
  rw [p.freq_square hab, p.freq_square hab]; ring

/-- On a square plate the modes `φ_mn` and `φ_nm` differ for `m ≠ n` (with `m, n ≥ 1`), so
`ω_mn` is a repeated eigenvalue. -/
theorem phi_ne_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    phi p.a p.b m n ≠ phi p.a p.b n m := by
  intro h
  have hpk := p.mode_peak 1 hm hn
  have e := congrFun (congrFun h (p.a / (2 * m))) (p.b / (2 * n))
  rw [phi, phi, hpk, mode_apply] at e
  -- `sin(nπ/(2m)) sin(mπ/(2n)) = 1` forces both factors to be `±1`
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha := p.a_pos.ne'
  have hb := p.b_pos.ne'
  rw [show n * π / p.a * (p.a / (2 * m)) = n / m * (π / 2) by field_simp,
    show m * π / p.b * (p.b / (2 * n)) = m / n * (π / 2) by field_simp] at e
  -- wlog-free argument: the factor with ratio `< 1` has `|sin| < 1`
  have key : ∀ {r : ℝ}, 0 < r → r < 1 → |sin (r * (π / 2))| < 1 := by
    intro r hr0 hr1
    have h0 : 0 < r * (π / 2) := by positivity
    have h1 : r * (π / 2) < π / 2 := by nlinarith [pi_pos]
    rw [abs_of_pos (sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos]))]
    calc sin (r * (π / 2)) < sin (π / 2) :=
          sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) le_rfl h1
      _ = 1 := sin_pi_div_two
  have habs : |sin (n / m * (π / 2))| * |sin (m / n * (π / 2))| = 1 := by
    rw [← abs_mul, show sin (n / m * (π / 2)) * sin (m / n * (π / 2)) = 1 by linarith,
      abs_one]
  have hle1 := abs_sin_le_one (n / m * (π / 2))
  have hle2 := abs_sin_le_one (m / n * (π / 2))
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
  · have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
    have := key (div_pos hm' hn') ((div_lt_one hn').mpr hlt')
    nlinarith [abs_nonneg (sin (n / m * (π / 2))), abs_nonneg (sin (m / n * (π / 2)))]
  · have hlt' : (n : ℝ) < m := by exact_mod_cast hlt
    have := key (div_pos hn' hm') ((div_lt_one hm').mpr hlt')
    nlinarith [abs_nonneg (sin (n / m * (π / 2))), abs_nonneg (sin (m / n * (π / 2)))]

end VibPlate

/-! ### Buckling -/

namespace Plate

variable (p : Plate)

/-- The **uniaxial buckling equation** `D Δ²w + N_x w_xx = 0` (compression `N_x > 0` per unit
length). [TimoshenkoGere1961], §9.2. -/
def Buckling (Nx : ℝ) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, p.D * biharm w x y + Nx * dx (dx w) x y = 0

/-- The buckling load of the mode `(m, n)`: `N_x = D π² (a/m)² ((m/a)² + (n/b)²)²`. -/
noncomputable def bucklingLoad (m n : ℕ) : ℝ :=
  p.D * π ^ 2 * (p.a / m) ^ 2 * ((m / p.a) ^ 2 + (n / p.b) ^ 2) ^ 2

/-- **Uniaxial buckling**: for `A ≠ 0` and `m, n ≥ 1` the mode `A sin(mπx/a) sin(nπy/b)` solves
`D Δ²w + N_x w_xx = 0` iff `N_x = D π² (a/m)² ((m/a)² + (n/b)²)²`. [TimoshenkoGere1961],
§9.2. -/
theorem buckling_iff (Nx : ℝ) {A : ℝ} (hA : A ≠ 0) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    p.Buckling Nx (mode A (m * π / p.a) (n * π / p.b)) ↔ Nx = p.bucklingLoad m n := by
  have h := p.mode_operator_iff p.D Nx 0 hA hm hn
  simp only [zero_mul, add_zero] at h
  rw [Buckling, h, bucklingLoad]
  have ha := p.a_pos.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpi := pi_pos.ne'
  constructor
  · intro e
    field_simp at e ⊢
    linear_combination -e
  · intro e
    rw [e]
    field_simp

/-- For fixed `m` the buckling load is smallest for one half-wave across: `N(m, 1) ≤ N(m, n)`
for `n ≥ 1`. -/
theorem bucklingLoad_one_le (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.bucklingLoad m 1 ≤ p.bucklingLoad m n := by
  have hD := p.D_pos.le
  have h : ((1 : ℕ) / p.b) ^ 2 ≤ (n / p.b) ^ 2 := by
    rw [div_pow, div_pow]
    gcongr
  unfold bucklingLoad
  gcongr

/-- The **buckling coefficient** `k(m, r) = (m/r + r/m)²` for the aspect ratio `r = a/b`. -/
noncomputable def bucklingCoeff (m : ℕ) (r : ℝ) : ℝ := (m / r + r / m) ^ 2

/-- `N(m, 1) = k(m, a/b) π² D / b²`, i.e. `k = (m b/a + a/(m b))²`. [TimoshenkoGere1961],
§9.2. -/
theorem bucklingLoad_eq_coeff {m : ℕ} (hm : 0 < m) :
    p.bucklingLoad m 1 = bucklingCoeff m (p.a / p.b) * π ^ 2 * p.D / p.b ^ 2 := by
  have ha := p.a_pos.ne'
  have hb := p.b_pos.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [bucklingLoad, bucklingCoeff]
  field_simp
  ring

/-- `k(m, r) - 4 = (m/r - r/m)²`. -/
theorem bucklingCoeff_sub_four {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    bucklingCoeff m r - 4 = (m / r - r / m) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [bucklingCoeff]
  field_simp
  ring

/-- **AM–GM bound** `k(m, r) ≥ 4` for every `m ≥ 1` and aspect ratio `r > 0`. -/
theorem four_le_bucklingCoeff {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    4 ≤ bucklingCoeff m r := by
  have := bucklingCoeff_sub_four hm hr
  nlinarith [sq_nonneg ((m : ℝ) / r - r / m)]

/-- `k(m, r) = 4` iff `r = m`: the minimum is reached when the plate buckles into square
half-waves. -/
theorem bucklingCoeff_eq_four_iff {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    bucklingCoeff m r = 4 ↔ r = m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [← sub_eq_zero, bucklingCoeff_sub_four hm hr, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  constructor
  · intro h
    field_simp at h
    nlinarith
  · rintro rfl
    rfl

/-- **Critical load**: every simply supported buckling mode needs `N_x ≥ 4π²D/b²`, and this
value is attained (with `m` half-waves along `x`, one across) when `a = m b`; in particular it
is the critical load of a long plate. [TimoshenkoGere1961], §9.2. -/
theorem critical_load {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    4 * π ^ 2 * p.D / p.b ^ 2 ≤ p.bucklingLoad m n ∧
      (p.a = m * p.b → p.bucklingLoad m 1 = 4 * π ^ 2 * p.D / p.b ^ 2) := by
  have hb := p.b_pos
  have hr : 0 < p.a / p.b := div_pos p.a_pos hb
  refine ⟨?_, fun h => ?_⟩
  · refine le_trans ?_ (p.bucklingLoad_one_le m hn)
    rw [p.bucklingLoad_eq_coeff hm]
    have := four_le_bucklingCoeff hm hr
    have hD := p.D_pos
    rw [div_le_div_iff_of_pos_right (by positivity)]
    gcongr
  · rw [p.bucklingLoad_eq_coeff hm,
      (bucklingCoeff_eq_four_iff hm hr).mpr (by rw [h, mul_div_cancel_right₀ _ hb.ne'])]

/-- The **biaxial buckling equation** `D Δ²w + N_x w_xx + N_y w_yy = 0`. [TimoshenkoGere1961],
§9.5. -/
def BiaxialBuckling (Nx Ny : ℝ) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, p.D * biharm w x y + Nx * dx (dx w) x y + Ny * dy (dy w) x y = 0

/-- **Biaxial buckling**: for `A ≠ 0`, `m, n ≥ 1` the mode `A sin(mπx/a) sin(nπy/b)` solves
`D Δ²w + N_x w_xx + N_y w_yy = 0` iff
`D π² ((m/a)² + (n/b)²)² = N_x (m/a)² + N_y (n/b)²`. [TimoshenkoGere1961], §9.5. -/
theorem biaxial_iff (Nx Ny : ℝ) {A : ℝ} (hA : A ≠ 0) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    p.BiaxialBuckling Nx Ny (mode A (m * π / p.a) (n * π / p.b)) ↔
      p.D * π ^ 2 * ((m / p.a) ^ 2 + (n / p.b) ^ 2) ^ 2 =
        Nx * (m / p.a) ^ 2 + Ny * (n / p.b) ^ 2 := by
  rw [BiaxialBuckling, p.mode_operator_iff p.D Nx Ny hA hm hn]
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 pi_pos.ne'
  constructor
  · intro e
    apply mul_left_cancel₀ hpi
    linear_combination e
  · intro e
    linear_combination π ^ 2 * e

end Plate

end ContinuumMechanics.Plates
