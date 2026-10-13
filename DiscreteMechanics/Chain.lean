import DiscreteMechanics.LongWave
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Lattice dynamics of mass–spring chains

The **Born–von Kármán** model of a one-dimensional crystal: point masses at the sites `n ∈ ℤ` of
a lattice of spacing `a`, nearest neighbours joined by springs of stiffness `k`.

* **Monatomic chain.** With masses `m` the equations of motion are
  `m üₙ = k (uₙ₊₁ - 2 uₙ + uₙ₋₁)`. A plane wave `uₙ(t) = cos(q n a - ω t)` (`isMotion_wave_iff`)
  or `uₙ(t) = e^{i(q n a - ω t)}` (`isMotionC_waveC_iff`) is a motion **iff** the
  **dispersion relation** `ω² = (4k/m) sin²(qa/2)` holds.
* **Brillouin zone.** `ω(q)` is `2π/a`-periodic (`omega_add_period`), and so is the wave itself
  on the lattice (`wave_add_period`); the frequency band is `[0, 2√(k/m)]` (`omega_le`), the top
  `ω_max = 2√(k/m)` being reached at the zone boundary `q = π/a` (`omega_zoneBoundary`).
* **Long waves.** `ω(q)/|q| → a√(k/m)` as `q → 0` (`tendsto_omega_div_abs`, proved from the
  long-wave expansion of the discrete Laplacian in `DiscreteMechanics.LongWave`), which is the
  speed of sound `√(E/ρ)` of the continuum rod with Young modulus `E = k a` and density
  `ρ = m/a` (`tendsto_omega_div_soundSpeed`).
* **Finite chain with fixed ends.** For `N` masses with `u₀ = u_{N+1} = 0`, the normal modes are
  `uₙ = sin(n j π/(N+1)) cos(φ - ω_j t)` with `ω_j² = (4k/m) sin²(jπ/(2(N+1)))`
  (`isFixedMotion_mode`); these frequencies sample the dispersion relation of the infinite chain
  at `q_j = jπ/((N+1)a)` (`fixedOmegaSq_eq_omegaSq`).
* **Diatomic chain.** Alternating masses `m₁, m₂` in a unit cell of length `a`; the Bloch
  dynamical matrix `D(q)` and mass matrix `M` satisfy
  `det(D(q) - ω² M) = m₁ m₂ ω⁴ - 2k(m₁+m₂) ω² + 4k² sin²(qa/2)` (`det_dynMatrix_sub`), so
  `det(D - ω²M) = 0 ⇔ ω² ∈ {ω²₋, ω²₊}` (`det_dynMatrix_sub_eq_zero_iff`) with
  `ω²_± = k(1/m₁ + 1/m₂) ± k√((1/m₁ + 1/m₂)² - 4 sin²(qa/2)/(m₁m₂))`. For `m₁ > m₂` there is a
  **band gap**: `ω²₋(q) ≤ 2k/m₁ < 2k/m₂ ≤ ω²₊(q)` for all `q` (`band_gap`), with both bounds
  attained at the zone boundary (`omegaSqMinus_zoneBoundary`, `omegaSqPlus_zoneBoundary`).

## Main results

* `isMotion_wave_iff`, `isMotionC_waveC_iff`: plane waves solve the chain iff dispersion holds.
* `omegaSq_add_period`, `omega_le`, `omega_zoneBoundary`: Brillouin zone and band top.
* `tendsto_omega_div_abs`, `tendsto_omega_div_soundSpeed`: the speed of sound.
* `isFixedMotion_mode`: normal modes of the finite chain with fixed ends.
* `isDiatomicMotion_wave_iff`, `det_dynMatrix_sub_eq_zero_iff`, `exists_mode_iff`, `band_gap`,
  `frequency_gap`: the diatomic chain.

## References

* [BornHuang1954] M. Born, K. Huang, *Dynamical Theory of Crystal Lattices*, Oxford (1954),
  Ch. II.
* [AshcroftMermin1976] N. W. Ashcroft, N. D. Mermin, *Solid State Physics*, Ch. 22.
* [Kittel2005] C. Kittel, *Introduction to Solid State Physics*, 8th ed., Ch. 4.
-/

open Filter Topology Matrix Real

noncomputable section

namespace DiscreteMechanics

namespace Chain

/-! ### Trigonometric and calculus lemmas -/

/-- `4 sin²(h/2) = 2 - 2 cos h`. -/
theorem four_sin_sq_half (h : ℝ) : 4 * sin (h / 2) ^ 2 = 2 - 2 * cos h := by
  have hc := cos_two_mul (h / 2)
  rw [show 2 * (h / 2) = h by ring] at hc
  linear_combination 4 * sin_sq_add_cos_sq (h / 2) + 2 * hc

/-- Second difference of the cosine: `cos(x+h) - 2 cos x + cos(x-h) = -4 sin²(h/2) cos x`. -/
theorem cos_lap (x h : ℝ) :
    cos (x + h) - 2 * cos x + cos (x - h) = -(4 * sin (h / 2) ^ 2) * cos x := by
  rw [cos_add, cos_sub, four_sin_sq_half]
  ring

/-- Second difference of the sine, from `sin(x+h) + sin(x-h) = 2 sin x cos h`:
`sin(x+h) - 2 sin x + sin(x-h) = -4 sin²(h/2) sin x`. -/
theorem sin_lap (x h : ℝ) :
    sin (x + h) - 2 * sin x + sin (x - h) = -(4 * sin (h / 2) ^ 2) * sin x := by
  rw [sin_add, sin_sub, four_sin_sq_half]
  ring

/-- Derivative of a harmonic signal `C cos(c - ω t)`. -/
theorem hasDerivAt_cos_wave (C c ω t : ℝ) :
    HasDerivAt (fun s => C * cos (c - ω * s)) (C * (ω * sin (c - ω * t))) t := by
  have := (((hasDerivAt_id' t).const_mul ω).const_sub c |>.cos).const_mul C
  convert this using 1
  ring

/-- Second derivative of a harmonic signal: `d²/dt² (C cos(c - ω t)) = -ω² C cos(c - ω t)`. -/
theorem deriv_deriv_cos_wave (C c ω t : ℝ) :
    deriv (deriv fun s => C * cos (c - ω * s)) t = -ω ^ 2 * (C * cos (c - ω * t)) := by
  have h1 : deriv (fun s => C * cos (c - ω * s)) = fun s => C * (ω * sin (c - ω * s)) :=
    funext fun s => (hasDerivAt_cos_wave C c ω s).deriv
  rw [h1]
  have := ((((hasDerivAt_id' t).const_mul ω).const_sub c |>.sin).const_mul ω).const_mul C
  convert this.deriv using 1
  ring

/-- Derivative of the complex harmonic signal `C e^{i(c - ω t)}`. -/
theorem hasDerivAt_cexp_wave (C : ℂ) (c ω t : ℝ) :
    HasDerivAt (fun s : ℝ => C * Complex.exp (((c - ω * s : ℝ) : ℂ) * Complex.I))
      (-(ω : ℂ) * Complex.I * (C * Complex.exp (((c - ω * t : ℝ) : ℂ) * Complex.I))) t := by
  have h := ((((hasDerivAt_id' t).const_mul ω).const_sub c).ofReal_comp.mul_const
    Complex.I |>.cexp).const_mul C
  convert h using 1
  push_cast
  ring

/-- Second derivative of the complex harmonic signal:
`d²/dt² (C e^{i(c - ω t)}) = -ω² C e^{i(c - ω t)}`. -/
theorem deriv_deriv_cexp_wave (C : ℂ) (c ω t : ℝ) :
    deriv (deriv fun s : ℝ => C * Complex.exp (((c - ω * s : ℝ) : ℂ) * Complex.I)) t =
      -(ω : ℂ) ^ 2 * (C * Complex.exp (((c - ω * t : ℝ) : ℂ) * Complex.I)) := by
  have h1 : deriv (fun s : ℝ => C * Complex.exp (((c - ω * s : ℝ) : ℂ) * Complex.I)) =
      fun s => (-(ω : ℂ) * Complex.I * C) * Complex.exp (((c - ω * s : ℝ) : ℂ) * Complex.I) :=
    funext fun s => by rw [(hasDerivAt_cexp_wave C c ω s).deriv]; ring
  rw [h1, (hasDerivAt_cexp_wave _ c ω t).deriv]
  linear_combination ((ω : ℂ) ^ 2 * (C * Complex.exp (((c - ω * t : ℝ) : ℂ) * Complex.I))) *
    Complex.I_sq

/-! ### The monatomic chain -/

/-- The **discrete Laplacian** (second difference) `uₙ₊₁ - 2 uₙ + uₙ₋₁` on the lattice `ℤ`. -/
def lap {R : Type*} [Ring R] (u : ℤ → R) (n : ℤ) : R := u (n + 1) - 2 * u n + u (n - 1)

/-- `u : ℝ → ℤ → ℝ` (time, site) is a **motion of the monatomic chain** with masses `m` and
springs `k`: `m üₙ = k (uₙ₊₁ - 2 uₙ + uₙ₋₁)`. -/
def IsMotion (m k : ℝ) (u : ℝ → ℤ → ℝ) : Prop :=
  ∀ n t, m * deriv (deriv fun s => u s n) t = k * lap (u t) n

/-- Complex displacements `u : ℝ → ℤ → ℂ` form a **motion of the monatomic chain**. -/
def IsMotionC (m k : ℝ) (u : ℝ → ℤ → ℂ) : Prop :=
  ∀ n t, (m : ℂ) * deriv (deriv fun s => u s n) t = k * lap (u t) n

/-- The **dispersion relation** of the monatomic chain: `ω²(q) = (4k/m) sin²(qa/2)`. -/
def omegaSq (m k a q : ℝ) : ℝ := 4 * k / m * sin (q * a / 2) ^ 2

/-- The frequency `ω(q) = √((4k/m) sin²(qa/2))` of the acoustic branch. -/
def omega (m k a q : ℝ) : ℝ := √(omegaSq m k a q)

/-- The real plane wave `uₙ(t) = cos(q n a - ω t)`. -/
def wave (q a ω t : ℝ) (n : ℤ) : ℝ := cos (q * n * a - ω * t)

/-- The complex plane wave `uₙ(t) = e^{i(q n a - ω t)}`. -/
def waveC (q a ω t : ℝ) (n : ℤ) : ℂ := Complex.exp (((q * n * a - ω * t : ℝ) : ℂ) * Complex.I)

/-- Rewriting the dispersion relation without division. -/
theorem sq_eq_omegaSq_iff {m k a q ω : ℝ} (hm : m ≠ 0) :
    ω ^ 2 = omegaSq m k a q ↔ m * ω ^ 2 = 4 * k * sin (q * a / 2) ^ 2 := by
  rw [omegaSq, div_mul_eq_mul_div, eq_div_iff hm]
  constructor <;> intro h <;> linarith

/-- The phase at site `n + 1` is the phase at site `n` shifted by `qa`. -/
theorem cast_shift_add (q a ω t : ℝ) (n : ℤ) :
    q * ((n + 1 : ℤ) : ℝ) * a - ω * t = (q * n * a - ω * t) + q * a := by
  push_cast; ring

/-- The phase at site `n - 1` is the phase at site `n` shifted by `-qa`. -/
theorem cast_shift_sub (q a ω t : ℝ) (n : ℤ) :
    q * ((n - 1 : ℤ) : ℝ) * a - ω * t = (q * n * a - ω * t) - q * a := by
  push_cast; ring

/-- The lattice Laplacian of a plane wave: `Δ wave = -4 sin²(qa/2) wave`. -/
theorem lap_wave (q a ω t : ℝ) (n : ℤ) :
    lap (wave q a ω t) n = -(4 * sin (q * a / 2) ^ 2) * wave q a ω t n := by
  simp only [lap, wave]
  rw [cast_shift_add, cast_shift_sub, cos_lap]

/-- The lattice Laplacian of a complex plane wave: `Δ waveC = -4 sin²(qa/2) waveC`. -/
theorem lap_waveC (q a ω t : ℝ) (n : ℤ) :
    lap (waveC q a ω t) n = ((-(4 * sin (q * a / 2) ^ 2) : ℝ) : ℂ) * waveC q a ω t n := by
  simp only [lap, waveC]
  rw [cast_shift_add, cast_shift_sub]
  set x := q * n * a - ω * t
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (cos_lap x (q * a))
  have hs := congrArg (fun r : ℝ => (r : ℂ)) (sin_lap x (q * a))
  simp only [Complex.exp_mul_I]
  push_cast at hc hs ⊢
  linear_combination hc + hs * Complex.I

/-- Time dependence of a plane wave at a fixed site: `üₙ = -ω² uₙ`. -/
theorem deriv_deriv_wave (q a ω t : ℝ) (n : ℤ) :
    deriv (deriv fun s => wave q a ω s n) t = -ω ^ 2 * wave q a ω t n := by
  simpa [wave] using deriv_deriv_cos_wave 1 (q * n * a) ω t

/-- Time dependence of a complex plane wave at a fixed site: `üₙ = -ω² uₙ`. -/
theorem deriv_deriv_waveC (q a ω t : ℝ) (n : ℤ) :
    deriv (deriv fun s => waveC q a ω s n) t = -(ω : ℂ) ^ 2 * waveC q a ω t n := by
  simpa [waveC] using deriv_deriv_cexp_wave 1 (q * n * a) ω t

/-- **Dispersion relation of the monatomic chain (real form).** The plane wave
`uₙ(t) = cos(q n a - ω t)` is a motion iff `ω² = (4k/m) sin²(qa/2)`. -/
theorem isMotion_wave_iff {m k : ℝ} (hm : m ≠ 0) (q a ω : ℝ) :
    IsMotion m k (wave q a ω) ↔ ω ^ 2 = omegaSq m k a q := by
  rw [sq_eq_omegaSq_iff hm]
  constructor
  · intro h
    have h0 := h 0 0
    rw [deriv_deriv_wave, lap_wave] at h0
    simp only [wave, Int.cast_zero, mul_zero, zero_mul, sub_zero, cos_zero] at h0
    linarith
  · intro h n t
    rw [deriv_deriv_wave, lap_wave]
    linear_combination (-wave q a ω t n) * h

/-- **Dispersion relation of the monatomic chain (complex form).** The plane wave
`uₙ(t) = e^{i(q n a - ω t)}` is a motion iff `ω² = (4k/m) sin²(qa/2)`. -/
theorem isMotionC_waveC_iff {m k : ℝ} (hm : m ≠ 0) (q a ω : ℝ) :
    IsMotionC m k (waveC q a ω) ↔ ω ^ 2 = omegaSq m k a q := by
  rw [sq_eq_omegaSq_iff hm]
  constructor
  · intro h
    have h0 := h 0 0
    rw [deriv_deriv_waveC, lap_waveC] at h0
    have hE : waveC q a ω 0 0 = 1 := by simp [waveC]
    rw [hE] at h0
    have : ((m * ω ^ 2 : ℝ) : ℂ) = ((4 * k * sin (q * a / 2) ^ 2 : ℝ) : ℂ) := by
      push_cast at h0 ⊢
      linear_combination -h0
    exact_mod_cast this
  · intro h n t
    rw [deriv_deriv_waveC, lap_waveC]
    have hc : ((m * ω ^ 2 : ℝ) : ℂ) = ((4 * k * sin (q * a / 2) ^ 2 : ℝ) : ℂ) := by rw [h]
    push_cast at hc ⊢
    linear_combination (-waveC q a ω t n) * hc

/-! ### Brillouin zone, band top and speed of sound -/

/-- `ω²(q)` is periodic with the period `2π/a` of the reciprocal lattice. -/
theorem omegaSq_add_period (m k : ℝ) {a : ℝ} (ha : a ≠ 0) (q : ℝ) :
    omegaSq m k a (q + 2 * π / a) = omegaSq m k a q := by
  rw [omegaSq, omegaSq, show (q + 2 * π / a) * a / 2 = q * a / 2 + π by field_simp,
    sin_add_pi, neg_sq]

/-- `ω(q)` is periodic with the period `2π/a` (Brillouin zone). -/
theorem omega_add_period (m k : ℝ) {a : ℝ} (ha : a ≠ 0) (q : ℝ) :
    omega m k a (q + 2 * π / a) = omega m k a q := by
  rw [omega, omega, omegaSq_add_period m k ha]

/-- Wave vectors differing by `2π/a` describe the *same* lattice wave. -/
theorem wave_add_period {a : ℝ} (ha : a ≠ 0) (q ω t : ℝ) (n : ℤ) :
    wave (q + 2 * π / a) a ω t n = wave q a ω t n := by
  rw [wave, wave, show (q + 2 * π / a) * n * a - ω * t = (q * n * a - ω * t) + n * (2 * π) by
    field_simp; ring, cos_add_int_mul_two_pi]

/-- `ω²(q) ≤ 4k/m`. -/
theorem omegaSq_le {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (a q : ℝ) :
    omegaSq m k a q ≤ 4 * k / m :=
  mul_le_of_le_one_right (by positivity) (sin_sq_le_one _)

/-- `ω²(q) ≥ 0`. -/
theorem omegaSq_nonneg {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (a q : ℝ) : 0 ≤ omegaSq m k a q := by
  unfold omegaSq; positivity

/-- `√(4k/m) = 2√(k/m)`. -/
theorem sqrt_four_mul_div (k m : ℝ) : √(4 * k / m) = 2 * √(k / m) := by
  rw [show 4 * k / m = 2 ^ 2 * (k / m) by ring, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]

/-- The frequency band of the monatomic chain is bounded by `ω_max = 2√(k/m)`. -/
theorem omega_le {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (a q : ℝ) :
    omega m k a q ≤ 2 * √(k / m) := by
  rw [omega, ← sqrt_four_mul_div]
  exact sqrt_le_sqrt (omegaSq_le hm hk a q)

/-- At the zone boundary `q = π/a`, `ω² = 4k/m`. -/
theorem omegaSq_zoneBoundary (m k : ℝ) {a : ℝ} (ha : a ≠ 0) :
    omegaSq m k a (π / a) = 4 * k / m := by
  rw [omegaSq, show π / a * a / 2 = π / 2 by field_simp, sin_pi_div_two]
  ring

/-- The maximal frequency `ω_max = 2√(k/m)` is reached at the zone boundary `q = π/a`. -/
theorem omega_zoneBoundary (m k : ℝ) {a : ℝ} (ha : a ≠ 0) :
    omega m k a (π / a) = 2 * √(k / m) := by
  rw [omega, omegaSq_zoneBoundary m k ha, sqrt_four_mul_div]

/-- **Long-wave limit of the dispersion relation**: `ω²(q)/q² → (k/m) a²` as `q → 0`. This is
the one-dimensional case of `tendsto_discreteLaplacian_isotropic`. -/
theorem tendsto_omegaSq_div_sq (m k a : ℝ) :
    Tendsto (fun q => omegaSq m k a q / q ^ 2) (𝓝[≠] 0) (𝓝 (k / m * a ^ 2)) := by
  have h := tendsto_discreteLaplacian_isotropic (E := ℝ) (fun _ : Fin 1 => a) (c := a ^ 2)
    (fun q => by simp [Real.norm_eq_abs, sq_abs]; ring)
  have h2 := h.const_mul (-(k / m))
  rw [show -(k / m) * -a ^ 2 = k / m * a ^ 2 by ring] at h2
  refine h2.congr fun q => ?_
  have hi : inner ℝ q a = q * a := by simp; ring
  simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, omegaSq, hi]
  rw [show 4 * k / m * sin (q * a / 2) ^ 2 = k / m * (4 * sin (q * a / 2) ^ 2) by ring,
    four_sin_sq_half]
  ring

/-- **Speed of sound**: `ω(q)/|q| → a√(k/m)` as `q → 0` (for `a ≥ 0`). -/
theorem tendsto_omega_div_abs (m k : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun q => omega m k a q / |q|) (𝓝[≠] 0) (𝓝 (a * √(k / m))) := by
  have h := ((continuous_sqrt.tendsto _).comp (tendsto_omegaSq_div_sq m k a))
  rw [sqrt_mul' _ (sq_nonneg a), sqrt_sq ha, mul_comm] at h
  refine h.congr fun q => ?_
  simp only [Function.comp, omega]
  rw [sqrt_div' _ (sq_nonneg q), sqrt_sq_eq_abs]

/-- **Phase velocity of long waves**: `ω(q)/q → a√(k/m)` as `q → 0⁺`. -/
theorem tendsto_omega_div (m k : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun q => omega m k a q / q) (𝓝[>] 0) (𝓝 (a * √(k / m))) := by
  refine ((tendsto_omega_div_abs m k ha).mono_left
    (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.1 hx).ne')).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [abs_of_pos hq]

/-- The lattice sound speed `a√(k/m)` equals the continuum value `√(E/ρ)` of a rod with Young
modulus `E = k a` and linear density `ρ = m/a`. -/
theorem soundSpeed_eq_sqrt_young_div_density {m k a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    a * √(k / m) = √((k * a) / (m / a)) := by
  rw [show k * a / (m / a) = k / m * a ^ 2 by field_simp, sqrt_mul' _ (sq_nonneg a),
    sqrt_sq ha.le, mul_comm]

/-- **Continuum limit**: long lattice waves travel at the speed of sound `√(E/ρ)` of the
continuum rod with `E = k a`, `ρ = m/a`. -/
theorem tendsto_omega_div_soundSpeed {m k a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    Tendsto (fun q => omega m k a q / q) (𝓝[>] 0) (𝓝 (√((k * a) / (m / a)))) := by
  rw [← soundSpeed_eq_sqrt_young_div_density hm ha]
  exact tendsto_omega_div m k ha.le

/-! ### The finite chain with fixed ends -/

/-- `u : ℝ → ℤ → ℝ` is a **motion of the chain of `N` masses with fixed ends**: `u₀ = u_{N+1} = 0`
and `m üₙ = k (uₙ₊₁ - 2 uₙ + uₙ₋₁)` for `1 ≤ n ≤ N`. -/
def IsFixedMotion (m k : ℝ) (N : ℕ) (u : ℝ → ℤ → ℝ) : Prop :=
  (∀ t, u t 0 = 0 ∧ u t (N + 1) = 0) ∧
    ∀ n : ℤ, 1 ≤ n → n ≤ N → ∀ t, m * deriv (deriv fun s => u s n) t = k * lap (u t) n

/-- The shape of the `j`-th normal mode: `uₙ = sin(n j π/(N+1))`. -/
def modeShape (N j : ℕ) (n : ℤ) : ℝ := sin (n * j * π / (N + 1))

/-- The squared frequency of the `j`-th normal mode: `ω_j² = (4k/m) sin²(jπ/(2(N+1)))`. -/
def fixedOmegaSq (m k : ℝ) (N j : ℕ) : ℝ := 4 * k / m * sin (j * π / (2 * (N + 1))) ^ 2

/-- The mode shapes vanish at both fixed ends: `u₀ = u_{N+1} = 0`. -/
theorem modeShape_boundary (N j : ℕ) : modeShape N j 0 = 0 ∧ modeShape N j (N + 1) = 0 := by
  refine ⟨by simp [modeShape], ?_⟩
  rw [modeShape, show (((N : ℤ) + 1 : ℤ) : ℝ) * j * π / (N + 1) = j * π by
    push_cast; field_simp, sin_nat_mul_pi]

/-- The mode shape is an eigenvector of the lattice Laplacian. -/
theorem lap_modeShape (N j : ℕ) (n : ℤ) :
    lap (modeShape N j) n = -(4 * sin (j * π / (2 * (N + 1))) ^ 2) * modeShape N j n := by
  simp only [lap, modeShape]
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((n + 1 : ℤ) : ℝ) * j * π / (N + 1) = n * j * π / (N + 1) + j * π / (N + 1) by
      push_cast; ring,
    show ((n - 1 : ℤ) : ℝ) * j * π / (N + 1) = n * j * π / (N + 1) - j * π / (N + 1) by
      push_cast; ring,
    sin_lap, show j * π / (N + 1) / 2 = j * π / (2 * (N + 1)) by field_simp]

/-- **Normal modes of the fixed-end chain**: for every amplitude `A` and phase `φ`,
`uₙ(t) = A sin(n j π/(N+1)) cos(φ - ω t)` with `ω² = (4k/m) sin²(jπ/(2(N+1)))` is a motion of the
chain of `N` masses with fixed ends. -/
theorem isFixedMotion_mode {m k : ℝ} (hm : m ≠ 0) (N j : ℕ) {ω : ℝ}
    (hω : ω ^ 2 = fixedOmegaSq m k N j) (A φ : ℝ) :
    IsFixedMotion m k N (fun t n => A * modeShape N j n * cos (φ - ω * t)) := by
  have hω' : m * ω ^ 2 = 4 * k * sin (j * π / (2 * (N + 1))) ^ 2 := by
    rw [hω, fixedOmegaSq]; field_simp
  refine ⟨fun t => ?_, fun n _ _ t => ?_⟩
  · simp [(modeShape_boundary N j).1, (modeShape_boundary N j).2]
  · have hd := deriv_deriv_cos_wave (A * modeShape N j n) φ ω t
    rw [hd]
    have hl : lap (fun n => A * modeShape N j n * cos (φ - ω * t)) n =
        A * cos (φ - ω * t) * lap (modeShape N j) n := by
      simp only [lap]; ring
    rw [hl, lap_modeShape]
    linear_combination (-(A * modeShape N j n * cos (φ - ω * t))) * hω'

/-- For `1 ≤ j ≤ N` the `j`-th mode is nontrivial: its first displacement is positive. -/
theorem modeShape_one_pos {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) : 0 < modeShape N j 1 := by
  rw [modeShape]
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjN' : (j : ℝ) < N + 1 := by exact_mod_cast Nat.lt_succ_of_le hjN
  apply sin_pos_of_pos_of_lt_pi
  · push_cast; positivity
  · rw [Int.cast_one, one_mul, div_lt_iff₀ hN]
    nlinarith [pi_pos]

/-- The finite chain samples the dispersion relation of the infinite chain at the quantized wave
vectors `q_j = jπ/((N+1)a)`. -/
theorem fixedOmegaSq_eq_omegaSq (m k : ℝ) (N j : ℕ) {a : ℝ} (ha : a ≠ 0) :
    fixedOmegaSq m k N j = omegaSq m k a (j * π / ((N + 1) * a)) := by
  rw [fixedOmegaSq, omegaSq, show j * π / ((N + 1) * a) * a / 2 = j * π / (2 * (N + 1)) by
    field_simp]

/-! ### The diatomic chain -/

/-- The Bloch **dynamical (stiffness) matrix** of the diatomic chain with unit cell length `a`:
`D(q) = k [[2, -(1 + e^{-iqa})], [-(1 + e^{iqa}), 2]]`. -/
def dynMatrix (k a q : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2 * k, -k * (1 + Complex.exp (-((q * a : ℝ) : ℂ) * Complex.I));
    -k * (1 + Complex.exp (((q * a : ℝ) : ℂ) * Complex.I)), 2 * k]

/-- The **mass matrix** `M = diag(m₁, m₂)` of the diatomic unit cell. -/
def massMatrix (m₁ m₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(m₁ : ℂ), 0; 0, (m₂ : ℂ)]

/-- The characteristic polynomial `m₁ m₂ λ² - 2k(m₁+m₂) λ + 4k² sin²(qa/2)` in `λ = ω²`. -/
def charPoly (m₁ m₂ k a q l : ℝ) : ℝ :=
  m₁ * m₂ * l ^ 2 - 2 * k * (m₁ + m₂) * l + 4 * k ^ 2 * sin (q * a / 2) ^ 2

/-- The discriminant `(1/m₁ + 1/m₂)² - 4 sin²(qa/2)/(m₁ m₂)`. -/
def disc (m₁ m₂ a q : ℝ) : ℝ := (1 / m₁ + 1 / m₂) ^ 2 - 4 * sin (q * a / 2) ^ 2 / (m₁ * m₂)

/-- The **optical branch** `ω²₊ = k(1/m₁ + 1/m₂) + k√(disc)`. -/
def omegaSqPlus (m₁ m₂ k a q : ℝ) : ℝ := k * (1 / m₁ + 1 / m₂) + k * √(disc m₁ m₂ a q)

/-- The **acoustic branch** `ω²₋ = k(1/m₁ + 1/m₂) - k√(disc)`. -/
def omegaSqMinus (m₁ m₂ k a q : ℝ) : ℝ := k * (1 / m₁ + 1 / m₂) - k * √(disc m₁ m₂ a q)

/-- `(1 + e^{-iθ})(1 + e^{iθ}) = 4 - 4 sin²(θ/2)`. -/
theorem one_add_exp_mul (θ : ℝ) :
    (1 + Complex.exp (-(θ : ℂ) * Complex.I)) * (1 + Complex.exp ((θ : ℂ) * Complex.I)) =
      ((4 - 4 * sin (θ / 2) ^ 2 : ℝ) : ℂ) := by
  have hprod : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have hsum := Complex.two_cos (θ : ℂ)
  have hs := congrArg (fun r : ℝ => (r : ℂ)) (four_sin_sq_half θ)
  push_cast at hs ⊢
  linear_combination hprod - hsum + hs

/-- **Characteristic polynomial of the diatomic chain**:
`det(D(q) - ω² M) = m₁ m₂ ω⁴ - 2k(m₁+m₂) ω² + 4k² sin²(qa/2)`. -/
theorem det_dynMatrix_sub (m₁ m₂ k a q l : ℝ) :
    (dynMatrix k a q - (l : ℂ) • massMatrix m₁ m₂).det = (charPoly m₁ m₂ k a q l : ℂ) := by
  have hD : dynMatrix k a q - (l : ℂ) • massMatrix m₁ m₂ =
      !![2 * (k : ℂ) - l * m₁, -k * (1 + Complex.exp (-((q * a : ℝ) : ℂ) * Complex.I));
        -k * (1 + Complex.exp (((q * a : ℝ) : ℂ) * Complex.I)), 2 * (k : ℂ) - l * m₂] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [dynMatrix, massMatrix]
  rw [hD, det_fin_two_of]
  have h := one_add_exp_mul (q * a)
  simp only [charPoly]
  push_cast at h ⊢
  linear_combination (-(k : ℂ) ^ 2) * h

/-- The discriminant dominates `(1/m₂ - 1/m₁)²`; in particular it is nonnegative. -/
theorem sq_sub_le_disc {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (a q : ℝ) :
    (1 / m₂ - 1 / m₁) ^ 2 ≤ disc m₁ m₂ a q := by
  have h1 : 4 * sin (q * a / 2) ^ 2 / (m₁ * m₂) ≤ 4 / (m₁ * m₂) :=
    div_le_div_of_nonneg_right (by nlinarith [sin_sq_le_one (q * a / 2)]) (by positivity)
  have h2 : (1 / m₁ + 1 / m₂) ^ 2 - 4 / (m₁ * m₂) = (1 / m₂ - 1 / m₁) ^ 2 := by
    field_simp; ring
  rw [disc]
  linarith

/-- The discriminant is nonnegative, so both branches are real. -/
theorem disc_nonneg {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (a q : ℝ) :
    0 ≤ disc m₁ m₂ a q :=
  (sq_nonneg _).trans (sq_sub_le_disc hm₁ hm₂ a q)

/-- Factorization `charPoly = m₁ m₂ (λ - ω²₊)(λ - ω²₋)`. -/
theorem charPoly_eq {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (k a q l : ℝ) :
    charPoly m₁ m₂ k a q l =
      m₁ * m₂ * ((l - omegaSqPlus m₁ m₂ k a q) * (l - omegaSqMinus m₁ m₂ k a q)) := by
  have hr := sq_sqrt (disc_nonneg hm₁ hm₂ a q)
  have hS : m₁ * m₂ * (1 / m₁ + 1 / m₂) = m₁ + m₂ := by field_simp; ring
  have hP : m₁ * m₂ * (4 * sin (q * a / 2) ^ 2 / (m₁ * m₂)) = 4 * sin (q * a / 2) ^ 2 := by
    field_simp
  simp only [charPoly, omegaSqPlus, omegaSqMinus]
  rw [disc] at hr ⊢
  linear_combination 2 * k * l * hS - k ^ 2 * hP + m₁ * m₂ * k ^ 2 * hr

/-- **Dispersion relation of the diatomic chain**: `det(D(q) - ω² M) = 0` iff `ω²` is on the
acoustic or the optical branch. -/
theorem det_dynMatrix_sub_eq_zero_iff {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (k a q l : ℝ) :
    (dynMatrix k a q - (l : ℂ) • massMatrix m₁ m₂).det = 0 ↔
      l = omegaSqMinus m₁ m₂ k a q ∨ l = omegaSqPlus m₁ m₂ k a q := by
  have : m₁ * m₂ ≠ 0 := by positivity
  rw [det_dynMatrix_sub, Complex.ofReal_eq_zero, charPoly_eq hm₁ hm₂, mul_eq_zero,
    or_iff_right this, mul_eq_zero, sub_eq_zero, sub_eq_zero, or_comm]

/-- **Bloch modes of the diatomic chain**: there is a nonzero amplitude vector `v` with
`(D(q) - ω² M) v = 0` iff `ω²` lies on the acoustic or the optical branch. -/
theorem exists_mode_iff {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (k a q l : ℝ) :
    (∃ v ≠ 0, (dynMatrix k a q - (l : ℂ) • massMatrix m₁ m₂) *ᵥ v = 0) ↔
      l = omegaSqMinus m₁ m₂ k a q ∨ l = omegaSqPlus m₁ m₂ k a q := by
  rw [exists_mulVec_eq_zero_iff, det_dynMatrix_sub_eq_zero_iff hm₁ hm₂]

/-- `(u, v) : ℝ → ℤ → ℂ` is a **motion of the diatomic chain**: in cell `n` the mass `m₁` (at
`uₙ`) is joined to `vₙ` and `vₙ₋₁`, the mass `m₂` (at `vₙ`) to `uₙ` and `uₙ₊₁`, all by springs
`k`. -/
def IsDiatomicMotion (m₁ m₂ k : ℝ) (u v : ℝ → ℤ → ℂ) : Prop :=
  ∀ n t, (m₁ : ℂ) * deriv (deriv fun s => u s n) t = k * (v t n - 2 * u t n + v t (n - 1)) ∧
    (m₂ : ℂ) * deriv (deriv fun s => v s n) t = k * (u t (n + 1) - 2 * v t n + u t n)

/-- Shifting a complex plane wave by one cell multiplies it by `e^{iqa}`. -/
theorem waveC_add_one (q a ω t : ℝ) (n : ℤ) :
    waveC q a ω t (n + 1) = waveC q a ω t n * Complex.exp (((q * a : ℝ) : ℂ) * Complex.I) := by
  rw [waveC, waveC, cast_shift_add, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Shifting a complex plane wave back by one cell multiplies it by `e^{-iqa}`. -/
theorem waveC_sub_one (q a ω t : ℝ) (n : ℤ) :
    waveC q a ω t (n - 1) =
      waveC q a ω t n * Complex.exp (-((q * a : ℝ) : ℂ) * Complex.I) := by
  rw [waveC, waveC, cast_shift_sub, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **Bloch reduction of the diatomic chain**: the plane wave `uₙ = A e^{i(qna - ωt)}`,
`vₙ = B e^{i(qna - ωt)}` is a motion iff `(D(q) - ω² M) (A, B) = 0`. -/
theorem isDiatomicMotion_wave_iff (m₁ m₂ k q a ω : ℝ) (A B : ℂ) :
    IsDiatomicMotion m₁ m₂ k (fun t n => A * waveC q a ω t n) (fun t n => B * waveC q a ω t n) ↔
      (dynMatrix k a q - ((ω ^ 2 : ℝ) : ℂ) • massMatrix m₁ m₂) *ᵥ ![A, B] = 0 := by
  have hdd : ∀ (C : ℂ) n t, deriv (deriv fun s => C * waveC q a ω s n) t =
      -(ω : ℂ) ^ 2 * (C * waveC q a ω t n) := fun C n t => by
    simpa [waveC] using deriv_deriv_cexp_wave C (q * n * a) ω t
  have hrow : (dynMatrix k a q - ((ω ^ 2 : ℝ) : ℂ) • massMatrix m₁ m₂) *ᵥ ![A, B] =
      ![(2 * k - ω ^ 2 * m₁) * A - k * (1 + Complex.exp (-((q * a : ℝ) : ℂ) * Complex.I)) * B,
        -(k * (1 + Complex.exp (((q * a : ℝ) : ℂ) * Complex.I)) * A) +
          (2 * k - ω ^ 2 * m₂) * B] := by
    ext i
    fin_cases i
    · simp [mulVec, dotProduct, dynMatrix, massMatrix, Fin.sum_univ_two]
      ring
    · simp [mulVec, dotProduct, dynMatrix, massMatrix, Fin.sum_univ_two]
  rw [hrow]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h 0 0
    have hE : waveC q a ω 0 0 = 1 := by simp [waveC]
    simp only [hdd, waveC_add_one, waveC_sub_one, hE] at h1 h2
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply]
      linear_combination h1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.zero_apply]
      linear_combination h2
  · intro h n t
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    simp only [hdd, waveC_add_one, waveC_sub_one]
    exact ⟨by linear_combination waveC q a ω t n * h0,
      by linear_combination waveC q a ω t n * h1⟩

/-- `|1/m₂ - 1/m₁| ≤ √disc`. -/
theorem abs_sub_le_sqrt_disc {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (a q : ℝ) :
    |1 / m₂ - 1 / m₁| ≤ √(disc m₁ m₂ a q) :=
  abs_le_sqrt (sq_sub_le_disc hm₁ hm₂ a q)

/-- **Band gap of the diatomic chain**: for a heavy mass `m₁ > m₂` and `k > 0`,
`ω²₋(q) ≤ 2k/m₁ < 2k/m₂ ≤ ω²₊(q)` for all wave vectors `q`. -/
theorem band_gap {m₁ m₂ k : ℝ} (hm₂ : 0 < m₂) (hm : m₂ < m₁) (hk : 0 < k) (a q : ℝ) :
    omegaSqMinus m₁ m₂ k a q ≤ 2 * k / m₁ ∧ 2 * k / m₁ < 2 * k / m₂ ∧
      2 * k / m₂ ≤ omegaSqPlus m₁ m₂ k a q := by
  have hm₁ : 0 < m₁ := hm₂.trans hm
  have h := mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (abs_sub_le_sqrt_disc hm₁ hm₂ a q)) hk.le
  refine ⟨?_, div_lt_div_of_pos_left (by positivity) hm₂ hm, ?_⟩
  · rw [omegaSqMinus]
    have : 2 * k / m₁ = k * (1 / m₁ + 1 / m₂) - k * (1 / m₂ - 1 / m₁) := by ring
    linarith
  · rw [omegaSqPlus]
    have : 2 * k / m₂ = k * (1 / m₁ + 1 / m₂) + k * (1 / m₂ - 1 / m₁) := by ring
    linarith

/-- **Frequency gap**: `ω₋(q) ≤ √(2k/m₁) < √(2k/m₂) ≤ ω₊(q)` for `m₁ > m₂`, `k > 0`. -/
theorem frequency_gap {m₁ m₂ k : ℝ} (hm₂ : 0 < m₂) (hm : m₂ < m₁) (hk : 0 < k) (a q : ℝ) :
    √(omegaSqMinus m₁ m₂ k a q) ≤ √(2 * k / m₁) ∧ √(2 * k / m₁) < √(2 * k / m₂) ∧
      √(2 * k / m₂) ≤ √(omegaSqPlus m₁ m₂ k a q) := by
  obtain ⟨h1, h2, h3⟩ := band_gap hm₂ hm hk a q
  have hm₁ : 0 < m₁ := hm₂.trans hm
  exact ⟨sqrt_le_sqrt h1, sqrt_lt_sqrt (by positivity) h2, sqrt_le_sqrt h3⟩

/-- At the zone boundary the discriminant is `(1/m₂ - 1/m₁)²`. -/
theorem disc_zoneBoundary (m₁ m₂ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    disc m₁ m₂ a (π / a) = (1 / m₂ - 1 / m₁) ^ 2 := by
  rw [disc, show π / a * a / 2 = π / 2 by field_simp, sin_pi_div_two]
  ring

/-- The top of the acoustic branch, at the zone boundary, is `ω²₋(π/a) = 2k/m₁` (`m₁ ≥ m₂`). -/
theorem omegaSqMinus_zoneBoundary {m₁ m₂ : ℝ} (hm₂ : 0 < m₂) (hm : m₂ ≤ m₁) (k : ℝ) {a : ℝ}
    (ha : a ≠ 0) : omegaSqMinus m₁ m₂ k a (π / a) = 2 * k / m₁ := by
  rw [omegaSqMinus, disc_zoneBoundary m₁ m₂ ha,
    sqrt_sq (sub_nonneg.2 (one_div_le_one_div_of_le hm₂ hm))]
  ring

/-- The bottom of the optical branch, at the zone boundary, is `ω²₊(π/a) = 2k/m₂` (`m₁ ≥ m₂`). -/
theorem omegaSqPlus_zoneBoundary {m₁ m₂ : ℝ} (hm₂ : 0 < m₂) (hm : m₂ ≤ m₁) (k : ℝ) {a : ℝ}
    (ha : a ≠ 0) : omegaSqPlus m₁ m₂ k a (π / a) = 2 * k / m₂ := by
  rw [omegaSqPlus, disc_zoneBoundary m₁ m₂ ha,
    sqrt_sq (sub_nonneg.2 (one_div_le_one_div_of_le hm₂ hm))]
  ring

/-- At `q = 0` the acoustic branch vanishes (uniform translation). -/
theorem omegaSqMinus_zero {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (k a : ℝ) :
    omegaSqMinus m₁ m₂ k a 0 = 0 := by
  have hd : disc m₁ m₂ a 0 = (1 / m₁ + 1 / m₂) ^ 2 := by simp [disc]
  rw [omegaSqMinus, hd, sqrt_sq (by positivity), sub_self]

/-- At `q = 0` the optical branch is `ω²₊(0) = 2k(1/m₁ + 1/m₂)`. -/
theorem omegaSqPlus_zero {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (k a : ℝ) :
    omegaSqPlus m₁ m₂ k a 0 = 2 * k * (1 / m₁ + 1 / m₂) := by
  have hd : disc m₁ m₂ a 0 = (1 / m₁ + 1 / m₂) ^ 2 := by simp [disc]
  rw [omegaSqPlus, hd, sqrt_sq (by positivity)]
  ring

end Chain

end DiscreteMechanics
