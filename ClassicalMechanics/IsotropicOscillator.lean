import ClassicalMechanics.Oscillator
import ClassicalMechanics.EffectivePotential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The isotropic harmonic oscillator in space

A particle of mass `m > 0` moves in space under the linear restoring force of stiffness `k > 0`,

`m ẍ = -k x`,  `x : ℝ → ℝ³`,  `ω = √(k/m)`

([Goldstein2002], §3.6 and §6; [Arnold1989], §§5, 8; [Fradkin1965]). By **Bertrand's theorem**
this and the Kepler problem are the only central potentials all of whose bounded orbits are closed;
here this is visible directly from the explicit solution.

* **Explicit solution** (`ofInit`, `ofInit_x_zero`, `ofInit_v_zero`): the curve
  `x(t) = x₀ cos ωt + (v₀/ω) sin ωt` (`ellipse`) is a motion with `x(0) = x₀`, `ẋ(0) = v₀`.
* **Uniqueness** (`eq_ellipse`, `v_eq`): every motion is of this form; this reduces, coordinate by
  coordinate (`coord`), to the uniqueness theorem `Harmonic.eq_sol` for the one-dimensional
  oscillator.
* **All orbits are closed** (`periodic_x`, `periodic_v`): every motion is periodic with period
  `2π/ω`, and the orbit is symmetric about the centre, `x(t + π/ω) = -x(t)` (`x_add_half_period`).
* **Isochronism** (`period_eq`, `isochronous`): the period `2π/ω = 2π √(m/k)` does not depend on
  the initial data, hence neither on the amplitude nor on the energy, in contrast to Kepler's third
  law `T² = 4π² m a³ / k` (`KeplerMotion.kepler_third`).
* **Conserved quantities**: the energy `E = ½ m |ẋ|² + ½ k |x|²` (`energy_const`), the angular
  momentum `L = x × m ẋ` (`angMom_const`), whence the motion is planar (`planar`), and the
  **Fradkin tensor** `A_ij = p_i p_j / (2m) + (k/2) x_i x_j` (`fradkin`, `p = m ẋ`): it is
  symmetric (`fradkin_transpose`), constant along motions (`fradkin_const`), has trace `E`
  (`trace_fradkin`) and annihilates the angular momentum, `A L = 0` (`fradkin_mulVec_L`).
* **The orbit is an ellipse centred at the origin** (`conic`): with `a = x₀`, `b = v₀/ω`, the
  Gram determinant `D = |a|²|b|² - (a·b)²` and `u = x·a`, `w = x·b`, the coordinates
  `G⁻¹ (u, w) = ((|b|² u - (a·b) w)/D, (|a|² w - (a·b) u)/D)` of `x(t)` in the basis `(a, b)` are
  `(cos ωt, sin ωt)` (`coords_eq`), so that `(|b|² u - (a·b) w)² + (|a|² w - (a·b) u)² = D²`.
  The ellipse is non-degenerate exactly when `L ≠ 0`, since `|L|² = (m ω)² D` (`L_dot_L`,
  `gramDet_pos`).
* **Virial theorem over one period** (`virial`, `kinetic_integral`): the kinetic and potential
  energies have the same integral `E T / 2` over a period `T = 2π/ω`, i.e. `⟨T⟩ = ⟨U⟩ = E/2`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.4, 3.6, 6.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§5, 8.
* [Fradkin1965] D. M. Fradkin, *Three-dimensional isotropic harmonic oscillator and SU₃*,
  Amer. J. Phys. 33 (1965), 207–211.
-/

open Matrix Real
open scoped Real

noncomputable section

namespace ClassicalMechanics

/-- An **isotropic harmonic oscillator** in space: `m ẍ = -k x` with `m, k > 0`. -/
structure IsoOscillator where
  m : ℝ
  k : ℝ
  m_pos : 0 < m
  k_pos : 0 < k
  x : ℝ → Vec
  v : ℝ → Vec
  a : ℝ → Vec
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  newton : ∀ t, m • a t = -k • x t

namespace IsoOscillator

/-! ### The explicit solution -/

/-- The curve `t ↦ a cos ωt + b sin ωt`. -/
def ellipse (ω : ℝ) (a b : Vec) (t : ℝ) : Vec := cos (ω * t) • a + sin (ω * t) • b

/-- The derivative of `a cos ωt + b sin ωt` is `(ω b) cos ωt + (-ω a) sin ωt`. -/
theorem hasDerivAt_ellipse (ω : ℝ) (a b : Vec) (t : ℝ) :
    HasDerivAt (ellipse ω a b) (ellipse ω (ω • b) (-ω • a) t) t := by
  have h1 := ((hasDerivAt_id t).const_mul ω).cos.smul_const a
  have h2 := ((hasDerivAt_id t).const_mul ω).sin.smul_const b
  convert h1.add h2 using 1
  · funext s; simp [ellipse]
  · ext i; simp [ellipse]; ring

/-- `a cos ωt + b sin ωt` is `2π/ω`-periodic. -/
theorem ellipse_periodic {ω : ℝ} (hω : ω ≠ 0) (a b : Vec) :
    Function.Periodic (ellipse ω a b) (2 * π / ω) := fun t => by
  rw [ellipse, ellipse, show ω * (t + 2 * π / ω) = ω * t + 2 * π by field_simp, cos_add_two_pi,
    sin_add_two_pi]

/-- `a cos ωt + b sin ωt` is centrally symmetric after half a period. -/
theorem ellipse_add_half {ω : ℝ} (hω : ω ≠ 0) (a b : Vec) (t : ℝ) :
    ellipse ω a b (t + π / ω) = -ellipse ω a b t := by
  rw [ellipse, ellipse, show ω * (t + π / ω) = ω * t + π by field_simp, cos_add_pi, sin_add_pi,
    neg_smul, neg_smul, neg_add]

/-- The angular frequency `ω = √(k/m)`. -/
def freq (m k : ℝ) : ℝ := √(k / m)

theorem freq_pos {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : 0 < freq m k :=
  sqrt_pos.mpr (div_pos hk hm)

theorem freq_sq {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : freq m k ^ 2 = k / m :=
  sq_sqrt (div_pos hk hm).le

/-- `m ω² = k`. -/
theorem mul_freq_sq {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : m * freq m k ^ 2 = k := by
  rw [freq_sq hm hk]; field_simp

/-- The **explicit motion** `x(t) = x₀ cos ωt + (v₀/ω) sin ωt` with initial data `x₀`, `v₀`. -/
def ofInit (m k : ℝ) (hm : 0 < m) (hk : 0 < k) (x₀ v₀ : Vec) : IsoOscillator where
  m := m
  k := k
  m_pos := hm
  k_pos := hk
  x := ellipse (freq m k) x₀ ((freq m k)⁻¹ • v₀)
  v := ellipse (freq m k) (freq m k • (freq m k)⁻¹ • v₀) (-freq m k • x₀)
  a := ellipse (freq m k) (freq m k • -freq m k • x₀)
    (-freq m k • freq m k • (freq m k)⁻¹ • v₀)
  hasDerivAt_x := hasDerivAt_ellipse _ _ _
  hasDerivAt_v := hasDerivAt_ellipse _ _ _
  newton := fun t => by
    have h := mul_freq_sq hm hk
    ext i
    simp only [ellipse, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (-(cos (freq m k * t) * x₀ i + sin (freq m k * t) *
      ((freq m k)⁻¹ * v₀ i))) * h

theorem ofInit_x_zero {m k : ℝ} (hm : 0 < m) (hk : 0 < k) (x₀ v₀ : Vec) :
    (ofInit m k hm hk x₀ v₀).x 0 = x₀ := by
  simp [ofInit, ellipse]

theorem ofInit_v_zero {m k : ℝ} (hm : 0 < m) (hk : 0 < k) (x₀ v₀ : Vec) :
    (ofInit m k hm hk x₀ v₀).v 0 = v₀ := by
  simp [ofInit, ellipse, smul_smul, mul_inv_cancel₀ (freq_pos hm hk).ne']

variable (O : IsoOscillator)

/-- The angular frequency `ω = √(k/m)` of the oscillator. -/
def ω : ℝ := freq O.m O.k

theorem ω_pos : 0 < O.ω := freq_pos O.m_pos O.k_pos

/-- `m ω² = k`. -/
theorem m_mul_ω_sq : O.m * O.ω ^ 2 = O.k := mul_freq_sq O.m_pos O.k_pos

/-! ### Uniqueness and periodicity -/

/-- The `i`-th coordinate of an isotropic oscillator is a one-dimensional harmonic oscillator. -/
def coord (i : Fin 3) : Harmonic where
  m := O.m
  c := 0
  k := O.k
  m_pos := O.m_pos
  c_nonneg := le_rfl
  k_pos := O.k_pos
  x := fun t => O.x t i
  v := fun t => O.v t i
  a := fun t => O.a t i
  hasDerivAt_x := fun t => hasDerivAt_pi.1 (O.hasDerivAt_x t) i
  hasDerivAt_v := fun t => hasDerivAt_pi.1 (O.hasDerivAt_v t) i
  eq := fun t => by
    have h := congrFun (O.newton t) i
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul] at h
    linarith
  c_eq := rfl

/-- **Uniqueness**: every motion is `x(t) = x(0) cos ωt + (ẋ(0)/ω) sin ωt`. -/
theorem eq_ellipse (t : ℝ) : O.x t = ellipse O.ω (O.x 0) (O.ω⁻¹ • O.v 0) t := by
  ext i
  have hω : (O.coord i).ω = O.ω := rfl
  have h := (O.coord i).eq_sol t
  simp only [Harmonic.sol, hω] at h
  refine h.trans ?_
  simp only [ellipse, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change O.x 0 i * _ + O.v 0 i / O.ω * _ = _
  ring

/-- The velocity of every motion is `ẋ(t) = ẋ(0) cos ωt - ω x(0) sin ωt`. -/
theorem v_eq (t : ℝ) :
    O.v t = ellipse O.ω (O.ω • O.ω⁻¹ • O.v 0) (-O.ω • O.x 0) t := by
  have h : O.x = ellipse O.ω (O.x 0) (O.ω⁻¹ • O.v 0) := funext O.eq_ellipse
  have hx := O.hasDerivAt_x t
  rw [h] at hx
  exact hx.unique (hasDerivAt_ellipse _ _ _ t)

/-- **All orbits are closed**: every motion is periodic with period `2π/ω`. -/
theorem periodic_x : Function.Periodic O.x (2 * π / O.ω) := by
  have h : O.x = ellipse O.ω (O.x 0) (O.ω⁻¹ • O.v 0) := funext O.eq_ellipse
  rw [h]
  exact ellipse_periodic O.ω_pos.ne' _ _

/-- The velocity is periodic with period `2π/ω`. -/
theorem periodic_v : Function.Periodic O.v (2 * π / O.ω) := by
  have h : O.v = ellipse O.ω (O.ω • O.ω⁻¹ • O.v 0) (-O.ω • O.x 0) := funext O.v_eq
  rw [h]
  exact ellipse_periodic O.ω_pos.ne' _ _

/-- After half a period the particle is at the antipodal point: `x(t + π/ω) = -x(t)`. -/
theorem x_add_half_period (t : ℝ) : O.x (t + π / O.ω) = -O.x t := by
  rw [O.eq_ellipse, O.eq_ellipse t, ellipse_add_half O.ω_pos.ne']

/-- The period `2π/ω` equals `2π √(m/k)`. -/
theorem period_eq : 2 * π / O.ω = 2 * π * √(O.m / O.k) := by
  rw [ω, freq, div_eq_mul_inv, ← sqrt_inv, inv_div]

/-- **Isochronism**: every motion has period `2π √(m/k)`, independent of the initial data, hence
of the amplitude and of the energy (unlike Kepler's third law `T² ∝ a³`). -/
theorem isochronous {m k : ℝ} (hm : 0 < m) (hk : 0 < k) (x₀ v₀ : Vec) :
    Function.Periodic (ofInit m k hm hk x₀ v₀).x (2 * π * √(m / k)) := by
  have h := (ofInit m k hm hk x₀ v₀).periodic_x
  rwa [period_eq] at h

/-! ### Conserved quantities -/

/-- The momentum `p = m ẋ`. -/
def p (t : ℝ) : Vec := O.m • O.v t

/-- The energy `E = ½ m |ẋ|² + ½ k |x|²`. -/
def E (t : ℝ) : ℝ := O.m / 2 * (O.v t ⬝ᵥ O.v t) + O.k / 2 * (O.x t ⬝ᵥ O.x t)

/-- The angular momentum `L = x × m ẋ`. -/
def L (t : ℝ) : Vec := O.x t ⨯₃ (O.m • O.v t)

/-- **Conservation of energy**. -/
theorem energy_const (s t : ℝ) : O.E s = O.E t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((hasDerivAt_dot (O.hasDerivAt_v t) (O.hasDerivAt_v t)).const_mul (O.m / 2)).add
    ((hasDerivAt_dot (O.hasDerivAt_x t) (O.hasDerivAt_x t)).const_mul (O.k / 2))
  have hma : O.m * (O.a t ⬝ᵥ O.v t) = -O.k * (O.x t ⬝ᵥ O.v t) := by
    rw [← smul_eq_mul, ← smul_dotProduct, O.newton, smul_dotProduct, smul_eq_mul]
  convert h using 1
  · rfl
  rw [dotProduct_comm (O.v t) (O.a t), dotProduct_comm (O.v t) (O.x t)]
  linear_combination -hma

/-- `L̇ = 0`. -/
theorem hasDerivAt_L (t : ℝ) : HasDerivAt O.L 0 t := by
  have h := hasDerivAt_cross (O.hasDerivAt_x t) ((O.hasDerivAt_v t).const_smul O.m)
  convert h using 1
  · rfl
  rw [Pi.smul_apply, O.newton, map_smul, map_smul, cross_self, cross_self, smul_zero, smul_zero,
    add_zero]

/-- **Conservation of angular momentum**. -/
theorem angMom_const (s t : ℝ) : O.L s = O.L t := eq_of_hasDerivAt_zero O.hasDerivAt_L s t

/-- The motion is **planar**: `x · L = 0`. -/
theorem planar (t : ℝ) : O.x t ⬝ᵥ O.L 0 = 0 := by
  rw [← O.angMom_const t 0, L, dot_self_cross]

/-- The **Fradkin tensor** `A_ij = p_i p_j / (2m) + (k/2) x_i x_j`. -/
def fradkin (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => O.p t i * O.p t j / (2 * O.m) + O.k / 2 * (O.x t i * O.x t j)

/-- In terms of the velocity, `A_ij = (m/2) ẋ_i ẋ_j + (k/2) x_i x_j`. -/
theorem fradkin_apply (t : ℝ) (i j : Fin 3) :
    O.fradkin t i j = O.m / 2 * (O.v t i * O.v t j) + O.k / 2 * (O.x t i * O.x t j) := by
  have hm := O.m_pos.ne'
  simp only [fradkin, p, of_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The Fradkin tensor is **symmetric**. -/
theorem fradkin_transpose (t : ℝ) : (O.fradkin t)ᵀ = O.fradkin t := by
  ext i j
  rw [transpose_apply, fradkin_apply, fradkin_apply]
  ring

/-- The trace of the Fradkin tensor is the energy: `tr A = E`. -/
theorem trace_fradkin (t : ℝ) : (O.fradkin t).trace = O.E t := by
  simp only [trace, diag, fradkin_apply, E, dotProduct, Fin.sum_univ_three]
  ring

/-- **Conservation of the Fradkin tensor**. -/
theorem fradkin_const (s t : ℝ) : O.fradkin s = O.fradkin t := by
  ext i j
  refine eq_of_hasDerivAt_zero (F := fun t => O.fradkin t i j) (fun t => ?_) s t
  have hx := hasDerivAt_pi.1 (O.hasDerivAt_x t)
  have hv := hasDerivAt_pi.1 (O.hasDerivAt_v t)
  have hn : ∀ l, O.m * O.a t l + O.k * O.x t l = 0 := fun l => by
    have h := congrFun (O.newton t) l
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul] at h
    linarith
  have h := (((hv i).mul (hv j)).const_mul (O.m / 2)).add
    (((hx i).mul (hx j)).const_mul (O.k / 2))
  convert h using 1
  · funext s; exact O.fradkin_apply s i j
  · linear_combination (-(O.v t j) / 2) * hn i + (-(O.v t i) / 2) * hn j

/-- The Fradkin tensor annihilates the angular momentum: `A L = 0`. -/
theorem fradkin_mulVec_L (t : ℝ) : O.fradkin t *ᵥ O.L t = 0 := by
  have hx : O.x t ⬝ᵥ O.L t = 0 := by rw [L, dot_self_cross]
  have hp : O.p t ⬝ᵥ O.L t = 0 := by rw [L, p, dot_cross_self]
  simp only [dotProduct, Fin.sum_univ_three] at hx hp
  ext i
  simp only [mulVec, dotProduct, fradkin, of_apply, Fin.sum_univ_three, Pi.zero_apply]
  linear_combination (O.p t i / (2 * O.m)) * hp + (O.k / 2 * O.x t i) * hx

/-! ### The orbit is an ellipse centred at the origin -/

/-- **The conic equation of `a cos ωt + b sin ωt`**: with `u = x · a`, `w = x · b` and the
Gram determinant `D = |a|²|b|² - (a·b)²`,
`(|b|² u - (a·b) w)² + (|a|² w - (a·b) u)² = D²`. -/
theorem ellipse_conic (ω : ℝ) (a b : Vec) (t : ℝ) :
    let x := ellipse ω a b t
    ((b ⬝ᵥ b) * (x ⬝ᵥ a) - (a ⬝ᵥ b) * (x ⬝ᵥ b)) ^ 2 +
        ((a ⬝ᵥ a) * (x ⬝ᵥ b) - (a ⬝ᵥ b) * (x ⬝ᵥ a)) ^ 2 =
      ((a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2) ^ 2 := by
  intro x
  have hu : x ⬝ᵥ a = cos (ω * t) * (a ⬝ᵥ a) + sin (ω * t) * (a ⬝ᵥ b) := by
    simp only [x, ellipse, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm b a]
  have hw : x ⬝ᵥ b = cos (ω * t) * (a ⬝ᵥ b) + sin (ω * t) * (b ⬝ᵥ b) := by
    simp only [x, ellipse, add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hu, hw]
  linear_combination ((a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2) ^ 2 * sin_sq_add_cos_sq (ω * t)

/-- The first axis vector of the orbital ellipse, `a = x(0)`. -/
def axisA : Vec := O.x 0

/-- The second axis vector of the orbital ellipse, `b = ẋ(0) / ω`. -/
def axisB : Vec := O.ω⁻¹ • O.v 0

/-- The Gram determinant `D = |a|²|b|² - (a·b)²` of `(a, b)`. -/
def gramDet : ℝ :=
  (O.axisA ⬝ᵥ O.axisA) * (O.axisB ⬝ᵥ O.axisB) - (O.axisA ⬝ᵥ O.axisB) ^ 2

/-- `x(t) = a cos ωt + b sin ωt`. -/
theorem x_eq (t : ℝ) : O.x t = ellipse O.ω O.axisA O.axisB t := O.eq_ellipse t

/-- **The orbit is an ellipse centred at the origin**: with `u = x(t) · a`, `w = x(t) · b`,
`(|b|² u - (a·b) w)² + (|a|² w - (a·b) u)² = D²`. -/
theorem conic (t : ℝ) :
    ((O.axisB ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisA) - (O.axisA ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisB)) ^ 2 +
      ((O.axisA ⬝ᵥ O.axisA) * (O.x t ⬝ᵥ O.axisB) -
        (O.axisA ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisA)) ^ 2 = O.gramDet ^ 2 := by
  rw [O.x_eq]
  exact ellipse_conic _ _ _ t

/-- **Coordinates in the basis `(a, b)`**: if `D ≠ 0`, then
`G⁻¹ (x · a, x · b) = (cos ωt, sin ωt)`. -/
theorem coords_eq (hD : O.gramDet ≠ 0) (t : ℝ) :
    ((O.axisB ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisA) - (O.axisA ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisB)) /
        O.gramDet = cos (O.ω * t) ∧
      ((O.axisA ⬝ᵥ O.axisA) * (O.x t ⬝ᵥ O.axisB) -
        (O.axisA ⬝ᵥ O.axisB) * (O.x t ⬝ᵥ O.axisA)) / O.gramDet = sin (O.ω * t) := by
  have hu : O.x t ⬝ᵥ O.axisA =
      cos (O.ω * t) * (O.axisA ⬝ᵥ O.axisA) + sin (O.ω * t) * (O.axisA ⬝ᵥ O.axisB) := by
    simp only [O.x_eq, ellipse, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_comm O.axisB O.axisA]
  have hw : O.x t ⬝ᵥ O.axisB =
      cos (O.ω * t) * (O.axisA ⬝ᵥ O.axisB) + sin (O.ω * t) * (O.axisB ⬝ᵥ O.axisB) := by
    simp only [O.x_eq, ellipse, add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hu, hw, div_eq_iff hD, div_eq_iff hD, gramDet]
  constructor <;> ring

/-- `|L|² = (m ω)² D`: the angular momentum measures the Gram determinant of the axes. -/
theorem L_dot_L : O.L 0 ⬝ᵥ O.L 0 = (O.m * O.ω) ^ 2 * O.gramDet := by
  have hv : O.v 0 = O.ω • O.axisB := by
    rw [axisB, smul_smul, mul_inv_cancel₀ O.ω_pos.ne', one_smul]
  rw [L, hv, smul_smul, map_smul, ← axisA, gramDet, dot_mul_dot_eq, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- If `L ≠ 0`, the Gram determinant is positive: the orbit is a non-degenerate ellipse. -/
theorem gramDet_pos (hL : O.L 0 ≠ 0) : 0 < O.gramDet := by
  have h := dot_self_pos hL
  rw [O.L_dot_L] at h
  exact pos_of_mul_pos_right h (sq_nonneg _)

/-! ### The virial theorem over one period -/

theorem continuous_x : Continuous O.x :=
  continuous_iff_continuousAt.2 fun t => (O.hasDerivAt_x t).continuousAt

theorem continuous_v : Continuous O.v :=
  continuous_iff_continuousAt.2 fun t => (O.hasDerivAt_v t).continuousAt

/-- **Virial theorem**: over one period `T = 2π/ω`, the kinetic energy `½ m |ẋ|²` and the
potential energy `½ k |x|²` have equal integrals, i.e. `⟨T⟩ = ⟨U⟩`. -/
theorem virial :
    ∫ t in (0 : ℝ)..2 * π / O.ω, O.m / 2 * (O.v t ⬝ᵥ O.v t) =
      ∫ t in (0 : ℝ)..2 * π / O.ω, O.k / 2 * (O.x t ⬝ᵥ O.x t) := by
  have hcv : Continuous fun t => O.m / 2 * (O.v t ⬝ᵥ O.v t) :=
    continuous_const.mul (O.continuous_v.dotProduct O.continuous_v)
  have hcx : Continuous fun t => O.k / 2 * (O.x t ⬝ᵥ O.x t) :=
    continuous_const.mul (O.continuous_x.dotProduct O.continuous_x)
  -- `d/dt (m x · ẋ / 2) = ½ m |ẋ|² - ½ k |x|²`
  have hG : ∀ t, HasDerivAt (fun s => O.m / 2 * (O.x s ⬝ᵥ O.v s))
      (O.m / 2 * (O.v t ⬝ᵥ O.v t) - O.k / 2 * (O.x t ⬝ᵥ O.x t)) t := fun t => by
    have h := (hasDerivAt_dot (O.hasDerivAt_x t) (O.hasDerivAt_v t)).const_mul (O.m / 2)
    have hma : O.m * (O.x t ⬝ᵥ O.a t) = -O.k * (O.x t ⬝ᵥ O.x t) := by
      rw [← smul_eq_mul, ← dotProduct_smul, O.newton, dotProduct_smul, smul_eq_mul]
    convert h using 1
    linear_combination (-1 / 2 : ℝ) * hma
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π / O.ω)
    (fun t _ => hG t) ((hcv.sub hcx).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (hcv.intervalIntegrable _ _) (hcx.intervalIntegrable _ _)]
    at hint
  have hper : O.m / 2 * (O.x (2 * π / O.ω) ⬝ᵥ O.v (2 * π / O.ω)) =
      O.m / 2 * (O.x 0 ⬝ᵥ O.v 0) := by
    have h1 := O.periodic_x 0
    have h2 := O.periodic_v 0
    rw [zero_add] at h1 h2
    rw [h1, h2]
  rw [hper, sub_self] at hint
  linarith

/-- Over one period, the kinetic energy integrates to `E T / 2`: `⟨T⟩ = ⟨U⟩ = E / 2`. -/
theorem kinetic_integral :
    ∫ t in (0 : ℝ)..2 * π / O.ω, O.m / 2 * (O.v t ⬝ᵥ O.v t) = O.E 0 * (2 * π / O.ω) / 2 := by
  have hcv : Continuous fun t => O.m / 2 * (O.v t ⬝ᵥ O.v t) :=
    continuous_const.mul (O.continuous_v.dotProduct O.continuous_v)
  have hcx : Continuous fun t => O.k / 2 * (O.x t ⬝ᵥ O.x t) :=
    continuous_const.mul (O.continuous_x.dotProduct O.continuous_x)
  have hsum : ∫ t in (0 : ℝ)..2 * π / O.ω, (O.m / 2 * (O.v t ⬝ᵥ O.v t) +
      O.k / 2 * (O.x t ⬝ᵥ O.x t)) = O.E 0 * (2 * π / O.ω) := by
    have : ∀ t, O.m / 2 * (O.v t ⬝ᵥ O.v t) + O.k / 2 * (O.x t ⬝ᵥ O.x t) = O.E 0 :=
      fun t => O.energy_const t 0
    simp only [this, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_add (hcv.intervalIntegrable _ _) (hcx.intervalIntegrable _ _),
    ← O.virial] at hsum
  linarith

end IsoOscillator

end ClassicalMechanics
