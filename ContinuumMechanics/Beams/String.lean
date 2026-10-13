import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The vibrating string and the one-dimensional wave equation

Small transverse vibrations `u(t, x)` of a taut string with tension `T` and linear density `ρ`
obey `ρ u_tt = T u_xx`, i.e. the **wave equation** `u_tt = c² u_xx` with wave speed
`c = √(T / ρ)` ([Strauss2008], §1.3, §2.1; [Courant1962], Ch. V). Fields are functions
`u : ℝ → ℝ → ℝ` of time `t` and position `x`; `dt u` and `dx u` are the partial derivatives.

## Main definitions

* `Strings.IsWave c u`: the wave equation `∂ₜ²u = c² ∂ₓ²u`.
* `Strings.dAlembert c φ ψ`: d'Alembert's formula.
* `Strings.mode L c n a b`: the `n`-th normal mode `sin(nπx/L)(a cos ωₙt + b sin ωₙt)`,
  `ωₙ = nπc/L`.
* `Strings.energy c L u`: the energy `½ ∫₀ᴸ (u_t² + c² u_x²) dx`.
* `Strings.VibratingString`: a string with length, tension and density; its wave speed and
  harmonic frequencies.

## Main results

* `isWave_travel`: `f(x - ct) + g(x + ct)` solves the wave equation for `C²` profiles.
* `dAlembert_solves`: d'Alembert's formula solves the Cauchy problem `u(0) = φ`, `u_t(0) = ψ`
  (`φ ∈ C²`, `ψ ∈ C¹`).
* `isWave_mode`, `mode_boundary`, `isWave_modeSum`, `modeSum_boundary`: normal modes and their
  finite superpositions solve the fixed–fixed string problem; `isWave_sum` (superposition).
* `integral_sin_mul_sin`: orthogonality `∫₀ᴸ sin(nπx/L) sin(mπx/L) dx = (L/2) δₙₘ`.
* `hasDerivAt_energy`, `energy_const`: **conservation of energy** for `C²` solutions with fixed
  ends (differentiation under the integral, Schwarz's theorem and integration by parts).
* `eq_zero_of_zero_data`, `unique`: **uniqueness** for the initial–boundary value problem.
* `VibratingString.isWave_iff`: `u_tt = c² u_xx` with `c² = T / ρ` iff `ρ u_tt = T u_xx`;
  `VibratingString.frequency_one` (fundamental frequency `f₁ = (1/2L)√(T/ρ)`) and
  `fundamental_length`, `fundamental_tension`, `fundamental_density` (**Mersenne's laws**).

## References

* [Strauss2008] W. A. Strauss, *Partial Differential Equations: An Introduction*, 2nd ed.,
  §1.3, §2.1, §2.2, §4.1.
* [Courant1962] R. Courant, D. Hilbert, *Methods of Mathematical Physics*, Vol. II, Ch. V.
* [Evans2010] L. C. Evans, *Partial Differential Equations*, §2.4.1, §2.4.3.
-/

open Set Real MeasureTheory

noncomputable section

namespace ContinuumMechanics.Strings

/-- Time derivative `∂ₜu(t, x)` of a field `u : ℝ → ℝ → ℝ` (arguments `t`, then `x`). -/
def dt (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t x => deriv (fun s => u s x) t

/-- Space derivative `∂ₓu(t, x)` of a field `u : ℝ → ℝ → ℝ`. -/
def dx (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t x => deriv (u t) x

/-- The **one-dimensional wave equation** `∂ₜ²u = c² ∂ₓ²u`, at every time and position. -/
def IsWave (c : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt (dt u) t x = c ^ 2 * dx (dx u) t x

/-! ### d'Alembert's solution -/

section dAlembert

variable {c : ℝ} {f g : ℝ → ℝ}

/-- Time derivative of a pair of travelling waves `α f(x - ct) + β g(x + ct)`. -/
theorem dt_travel (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (α β : ℝ) :
    dt (fun t x => α * f (x - c * t) + β * g (x + c * t)) =
      fun t x => (-c * α) * deriv f (x - c * t) + (c * β) * deriv g (x + c * t) := by
  funext t x
  have h1 := ((hf (x - c * t)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul c).const_sub x)).const_mul α
  have h2 := ((hg (x + c * t)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul c).const_add x)).const_mul β
  simp only [dt]
  refine ((h1.add h2).deriv).trans ?_
  ring

/-- Space derivative of a pair of travelling waves `α f(x - ct) + β g(x + ct)`. -/
theorem dx_travel (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (α β : ℝ) :
    dx (fun t x => α * f (x - c * t) + β * g (x + c * t)) =
      fun t x => α * deriv f (x - c * t) + β * deriv g (x + c * t) := by
  funext t x
  have h1 := ((hf (x - c * t)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const (c * t))).const_mul α
  have h2 := ((hg (x + c * t)).hasDerivAt.comp x ((hasDerivAt_id x).add_const (c * t))).const_mul β
  simp only [dx]
  refine ((h1.add h2).deriv).trans ?_
  ring

/-- A `C²` function is differentiable with differentiable derivative. -/
theorem differentiable_and_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ f ∧ Differentiable ℝ (deriv f) :=
  ⟨hf.differentiable (by norm_num),
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable one_ne_zero⟩

/-- **Travelling waves** (d'Alembert): for `C²` profiles `f, g`, the superposition
`u(t, x) = f(x - ct) + g(x + ct)` of a right- and a left-moving wave solves `u_tt = c² u_xx`. -/
theorem isWave_travel (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    IsWave c (fun t x => f (x - c * t) + g (x + c * t)) := by
  obtain ⟨f1, f2⟩ := differentiable_and_deriv hf
  obtain ⟨g1, g2⟩ := differentiable_and_deriv hg
  have e : (fun t x => f (x - c * t) + g (x + c * t)) =
      fun t x => 1 * f (x - c * t) + 1 * g (x + c * t) := by simp
  intro t x
  rw [e, dt_travel f1 g1, dt_travel f2 g2, dx_travel f1 g1, dx_travel f2 g2]
  ring

variable {ψ φ : ℝ → ℝ}

/-- The primitive `Ψ(y) = ∫₀ʸ ψ`. -/
def primitive (ψ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in (0 : ℝ)..y, ψ z

/-- Fundamental theorem of calculus: `Ψ' = ψ` for continuous `ψ`. -/
theorem hasDerivAt_primitive (hψ : Continuous ψ) (y : ℝ) :
    HasDerivAt (primitive ψ) (ψ y) y :=
  (hψ.integral_hasStrictDerivAt 0 y).hasDerivAt

/-- The primitive of a `C¹` function is `C²`. -/
theorem contDiff_primitive (hψ : ContDiff ℝ 1 ψ) : ContDiff ℝ 2 (primitive ψ) := by
  have hd : deriv (primitive ψ) = ψ :=
    funext fun y => (hasDerivAt_primitive hψ.continuous y).deriv
  refine (contDiff_succ_iff_deriv (n := 1)).mpr
    ⟨fun y => (hasDerivAt_primitive hψ.continuous y).differentiableAt, by simp, ?_⟩
  rwa [hd]

/-- **d'Alembert's formula**
`u(t, x) = ½ (φ(x - ct) + φ(x + ct)) + (1 / 2c) ∫_{x-ct}^{x+ct} ψ`. -/
def dAlembert (c : ℝ) (φ ψ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (φ (x - c * t) + φ (x + c * t)) / 2 + 1 / (2 * c) * ∫ y in (x - c * t)..(x + c * t), ψ y

/-- Right-moving profile `F = φ / 2 - Ψ / 2c` of d'Alembert's solution. -/
def dAlembertRight (c : ℝ) (φ ψ : ℝ → ℝ) (y : ℝ) : ℝ := φ y / 2 - primitive ψ y / (2 * c)

/-- Left-moving profile `G = φ / 2 + Ψ / 2c` of d'Alembert's solution. -/
def dAlembertLeft (c : ℝ) (φ ψ : ℝ → ℝ) (y : ℝ) : ℝ := φ y / 2 + primitive ψ y / (2 * c)

/-- d'Alembert's solution is the travelling-wave pair `F(x - ct) + G(x + ct)`. -/
theorem dAlembert_eq (hψ : Continuous ψ) :
    dAlembert c φ ψ =
      fun t x => dAlembertRight c φ ψ (x - c * t) + dAlembertLeft c φ ψ (x + c * t) := by
  funext t x
  simp only [dAlembert, dAlembertRight, dAlembertLeft, primitive]
  rw [← intervalIntegral.integral_interval_sub_left (hψ.intervalIntegrable _ _)
    (hψ.intervalIntegrable _ _)]
  ring

/-- **d'Alembert's formula solves the wave equation** for `φ ∈ C²`, `ψ ∈ C¹`. -/
theorem isWave_dAlembert (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ) :
    IsWave c (dAlembert c φ ψ) := by
  rw [dAlembert_eq hψ.continuous]
  exact isWave_travel ((hφ.div_const 2).sub ((contDiff_primitive hψ).div_const _))
    ((hφ.div_const 2).add ((contDiff_primitive hψ).div_const _))

/-- **Initial displacement**: d'Alembert's solution satisfies `u(0, x) = φ(x)`. -/
theorem dAlembert_zero (x : ℝ) : dAlembert c φ ψ 0 x = φ x := by
  simp only [dAlembert, mul_zero, sub_zero, add_zero, intervalIntegral.integral_same]
  ring

/-- **Initial velocity**: d'Alembert's solution satisfies `u_t(0, x) = ψ(x)` (`c ≠ 0`). -/
theorem dt_dAlembert_zero (hc : c ≠ 0) (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ) (x : ℝ) :
    dt (dAlembert c φ ψ) 0 x = ψ x := by
  have hφ1 := (differentiable_and_deriv hφ).1
  have hP := hasDerivAt_primitive hψ.continuous
  have hR : ∀ y, HasDerivAt (dAlembertRight c φ ψ) (deriv φ y / 2 - ψ y / (2 * c)) y :=
    fun y => ((hφ1 y).hasDerivAt.div_const 2).sub ((hP y).div_const _)
  have hL : ∀ y, HasDerivAt (dAlembertLeft c φ ψ) (deriv φ y / 2 + ψ y / (2 * c)) y :=
    fun y => ((hφ1 y).hasDerivAt.div_const 2).add ((hP y).div_const _)
  have e : (fun t x => dAlembertRight c φ ψ (x - c * t) + dAlembertLeft c φ ψ (x + c * t)) =
      fun t x => 1 * dAlembertRight c φ ψ (x - c * t) + 1 * dAlembertLeft c φ ψ (x + c * t) := by
    simp
  rw [dAlembert_eq hψ.continuous, e, dt_travel (fun y => (hR y).differentiableAt)
    (fun y => (hL y).differentiableAt)]
  simp only [mul_zero, sub_zero, add_zero, (hR x).deriv, (hL x).deriv]
  field_simp
  ring

/-- **The Cauchy problem** for the infinite string: d'Alembert's formula solves `u_tt = c² u_xx`
with `u(0, ·) = φ` and `u_t(0, ·) = ψ`. -/
theorem dAlembert_solves (hc : c ≠ 0) (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ) :
    IsWave c (dAlembert c φ ψ) ∧ (∀ x, dAlembert c φ ψ 0 x = φ x) ∧
      ∀ x, dt (dAlembert c φ ψ) 0 x = ψ x :=
  ⟨isWave_dAlembert hφ hψ, dAlembert_zero, dt_dAlembert_zero hc hφ hψ⟩

end dAlembert

/-! ### Superposition -/

section Superposition

variable {ι : Type*}

/-- Time derivative of a finite sum of fields. -/
theorem dt_sum (s : Finset ι) (u : ι → ℝ → ℝ → ℝ)
    (h : ∀ i t x, DifferentiableAt ℝ (fun s => u i s x) t) :
    dt (fun t x => ∑ i ∈ s, u i t x) = fun t x => ∑ i ∈ s, dt (u i) t x :=
  funext fun t => funext fun x => (HasDerivAt.fun_sum fun i _ => (h i t x).hasDerivAt).deriv

/-- Space derivative of a finite sum of fields. -/
theorem dx_sum (s : Finset ι) (u : ι → ℝ → ℝ → ℝ)
    (h : ∀ i t x, DifferentiableAt ℝ (u i t) x) :
    dx (fun t x => ∑ i ∈ s, u i t x) = fun t x => ∑ i ∈ s, dx (u i) t x :=
  funext fun t => funext fun x => (HasDerivAt.fun_sum fun i _ => (h i t x).hasDerivAt).deriv

/-- **Superposition principle**: a finite sum of (twice differentiable) solutions of the wave
equation is a solution. -/
theorem isWave_sum {c : ℝ} (s : Finset ι) (u : ι → ℝ → ℝ → ℝ)
    (ht : ∀ i t x, DifferentiableAt ℝ (fun s => u i s x) t)
    (htt : ∀ i t x, DifferentiableAt ℝ (fun s => dt (u i) s x) t)
    (hx : ∀ i t x, DifferentiableAt ℝ (u i t) x) (hxx : ∀ i t x, DifferentiableAt ℝ (dx (u i) t) x)
    (hw : ∀ i ∈ s, IsWave c (u i)) : IsWave c (fun t x => ∑ i ∈ s, u i t x) := by
  intro t x
  rw [dt_sum s u ht, dt_sum s (fun i => dt (u i)) htt, dx_sum s u hx,
    dx_sum s (fun i => dx (u i)) hxx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => hw i hi t x

end Superposition

/-! ### Standing waves and normal modes -/

section Modes

/-- A harmonic oscillation `s ↦ a cos(ωs) + b sin(ωs)`. -/
def harm (ω a b s : ℝ) : ℝ := a * cos (ω * s) + b * sin (ω * s)

/-- The derivative of a harmonic oscillation is again harmonic. -/
theorem deriv_harm (ω a b : ℝ) : deriv (harm ω a b) = harm ω (ω * b) (-(ω * a)) := by
  funext s
  have h := (((hasDerivAt_id s).const_mul ω).cos.const_mul a).add
    (((hasDerivAt_id s).const_mul ω).sin.const_mul b)
  refine h.deriv.trans ?_
  simp only [harm, id]
  ring

/-- Harmonic oscillations are differentiable. -/
theorem differentiable_harm (ω a b : ℝ) : Differentiable ℝ (harm ω a b) := by
  unfold harm
  fun_prop

/-- A separated standing wave `X(x) T(t)` with harmonic `X` (wavenumber `k`) and harmonic `T`
(angular frequency `ω`). -/
def sep (k ω p q a b t x : ℝ) : ℝ := harm k p q x * harm ω a b t

/-- Time derivative of a separated standing wave. -/
theorem dt_sep (k ω p q a b : ℝ) : dt (sep k ω p q a b) = sep k ω p q (ω * b) (-(ω * a)) := by
  funext t x
  simp only [dt, sep]
  rw [deriv_const_mul _ (differentiable_harm ω a b t), deriv_harm]

/-- Space derivative of a separated standing wave. -/
theorem dx_sep (k ω p q a b : ℝ) : dx (sep k ω p q a b) = sep k ω (k * q) (-(k * p)) a b := by
  funext t x
  change deriv (fun y => harm k p q y * harm ω a b t) x = _
  rw [deriv_mul_const (differentiable_harm k p q x), deriv_harm]
  rfl

/-- Separated standing waves are differentiable in time. -/
theorem differentiableAt_sep_t (k ω p q a b t x : ℝ) :
    DifferentiableAt ℝ (fun s => sep k ω p q a b s x) t :=
  ((differentiable_harm ω a b t).const_mul _)

/-- Separated standing waves are differentiable in space. -/
theorem differentiableAt_sep_x (k ω p q a b t x : ℝ) :
    DifferentiableAt ℝ (sep k ω p q a b t) x :=
  ((differentiable_harm k p q x).mul_const _)

/-- A separated standing wave solves the wave equation when the dispersion relation
`ω² = c² k²` holds. -/
theorem isWave_sep {c k ω : ℝ} (hω : ω ^ 2 = c ^ 2 * k ^ 2) (p q a b : ℝ) :
    IsWave c (sep k ω p q a b) := by
  intro t x
  rw [dt_sep, dt_sep, dx_sep, dx_sep]
  simp only [sep, harm]
  linear_combination (-(p * cos (k * x) + q * sin (k * x)) *
    (a * cos (ω * t) + b * sin (ω * t))) * hω

variable (L c : ℝ)

/-- Angular frequency of the `n`-th mode of a string of length `L`: `ωₙ = nπc / L`. -/
def omega (n : ℕ) : ℝ := n * π * c / L

/-- Wavenumber of the `n`-th mode of a string of length `L`: `kₙ = nπ / L`. -/
def wavenumber (n : ℕ) : ℝ := n * π / L

/-- The `n`-th **normal mode** (standing wave) of a string of length `L` fixed at both ends:
`uₙ(t, x) = sin(nπx / L) (a cos(ωₙ t) + b sin(ωₙ t))`. -/
def mode (n : ℕ) (a b t x : ℝ) : ℝ :=
  sin (n * π / L * x) * (a * cos (omega L c n * t) + b * sin (omega L c n * t))

/-- A normal mode is a separated standing wave. -/
theorem mode_eq_sep (n : ℕ) (a b : ℝ) :
    mode L c n a b = sep (wavenumber L n) (omega L c n) 0 1 a b := by
  funext t x
  simp [mode, sep, harm, wavenumber]

/-- Dispersion relation of the normal modes: `ωₙ² = c² kₙ²`. -/
theorem omega_sq (n : ℕ) : omega L c n ^ 2 = c ^ 2 * wavenumber L n ^ 2 := by
  simp only [omega, wavenumber]
  ring

/-- **Normal modes solve the wave equation.** -/
theorem isWave_mode (n : ℕ) (a b : ℝ) : IsWave c (mode L c n a b) := by
  rw [mode_eq_sep]
  exact isWave_sep (omega_sq L c n) _ _ _ _

/-- **Normal modes satisfy the fixed-end boundary conditions** `u(t, 0) = u(t, L) = 0`. -/
theorem mode_boundary {L : ℝ} (hL : L ≠ 0) (n : ℕ) (a b t : ℝ) :
    mode L c n a b t 0 = 0 ∧ mode L c n a b t L = 0 := by
  refine ⟨by simp [mode], ?_⟩
  simp only [mode]
  rw [div_mul_cancel₀ _ hL, sin_nat_mul_pi, zero_mul]

/-- A finite superposition of normal modes `∑ₙ uₙ` with amplitudes `aₙ, bₙ`. -/
def modeSum (s : Finset ℕ) (a b : ℕ → ℝ) (t x : ℝ) : ℝ := ∑ n ∈ s, mode L c n (a n) (b n) t x

/-- **Finite superpositions of normal modes solve the wave equation.** -/
theorem isWave_modeSum (s : Finset ℕ) (a b : ℕ → ℝ) : IsWave c (modeSum L c s a b) := by
  have e : ∀ n, mode L c n (a n) (b n) = sep (wavenumber L n) (omega L c n) 0 1 (a n) (b n) :=
    fun n => mode_eq_sep L c n _ _
  refine isWave_sum s (fun n => mode L c n (a n) (b n)) (fun n t x => ?_) (fun n t x => ?_)
    (fun n t x => ?_) (fun n t x => ?_) fun n _ => isWave_mode L c n _ _
  · simp only [e]; exact differentiableAt_sep_t ..
  · simp only [e, dt_sep]; exact differentiableAt_sep_t ..
  · simp only [e]; exact differentiableAt_sep_x ..
  · simp only [e, dx_sep]; exact differentiableAt_sep_x ..

/-- **Finite superpositions of normal modes satisfy the fixed-end boundary conditions.** -/
theorem modeSum_boundary {L : ℝ} (hL : L ≠ 0) (s : Finset ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    modeSum L c s a b t 0 = 0 ∧ modeSum L c s a b t L = 0 :=
  ⟨Finset.sum_eq_zero fun n _ => (mode_boundary c hL n _ _ t).1,
    Finset.sum_eq_zero fun n _ => (mode_boundary c hL n _ _ t).2⟩

/-- `∫₀ᴸ cos(kπx / L) dx = L δ_{k0}` for integer `k`. -/
theorem integral_cos_int {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    ∫ x in (0 : ℝ)..L, cos (k * π / L * x) = if k = 0 then L else 0 := by
  split_ifs with hk
  · simp [hk]
  have hc : (k : ℝ) * π / L ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast hk) pi_ne_zero) hL
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hc, integral_cos,
    div_mul_cancel₀ _ hL, sin_int_mul_pi]
  simp

/-- **Orthogonality of the normal modes** in `L²(0, L)`:
`∫₀ᴸ sin(nπx / L) sin(mπx / L) dx = (L / 2) δₙₘ` for `n ≥ 0`, `m ≥ 1`. -/
theorem integral_sin_mul_sin {L : ℝ} (hL : L ≠ 0) {n m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..L, sin (n * π / L * x) * sin (m * π / L * x) =
      if n = m then L / 2 else 0 := by
  have e : ∀ x : ℝ, sin (n * π / L * x) * sin (m * π / L * x) =
      (cos (((n - m : ℤ) : ℝ) * π / L * x) - cos (((n + m : ℤ) : ℝ) * π / L * x)) / 2 := by
    intro x
    have h1 : ((n - m : ℤ) : ℝ) * π / L * x = n * π / L * x - m * π / L * x := by
      push_cast; ring
    have h2 : ((n + m : ℤ) : ℝ) * π / L * x = n * π / L * x + m * π / L * x := by
      push_cast; ring
    rw [h1, h2, cos_sub, cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_cos_int hL, integral_cos_int hL]
  have hnm : ((n : ℤ) + m) ≠ 0 := by omega
  simp only [hnm, ite_false, sub_zero, sub_eq_zero, Nat.cast_inj]
  split_ifs <;> simp

end Modes

/-! ### Energy conservation and uniqueness for the string fixed at both ends -/

section Partials

variable {U : ℝ × ℝ → ℝ}

/-- The time partial derivative of a differentiable `U(t, x)` is `DU(t, x)(1, 0)`. -/
theorem hasDerivAt_fst_of_differentiable (hU : Differentiable ℝ U) (t x : ℝ) :
    HasDerivAt (fun s => U (s, x)) (fderiv ℝ U (t, x) (1, 0)) t :=
  (hU (t, x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))

/-- The space partial derivative of a differentiable `U(t, x)` is `DU(t, x)(0, 1)`. -/
theorem hasDerivAt_snd_of_differentiable (hU : Differentiable ℝ U) (t x : ℝ) :
    HasDerivAt (fun y => U (t, y)) (fderiv ℝ U (t, x) (0, 1)) x :=
  (hU (t, x)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id' x))

/-- The directional derivative field `p ↦ DU(p) v`. -/
def dirDeriv (U : ℝ × ℝ → ℝ) (v p : ℝ × ℝ) : ℝ := fderiv ℝ U p v

/-- Directional derivatives of a `C²` field are `C¹`. -/
theorem contDiff_dirDeriv (hU : ContDiff ℝ 2 U) (v : ℝ × ℝ) : ContDiff ℝ 1 (dirDeriv U v) :=
  (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Derivative of a directional derivative field: `D(DU · v)(p) w = D²U(p) w v`. -/
theorem fderiv_dirDeriv (hU : ContDiff ℝ 2 U) (v w p : ℝ × ℝ) :
    fderiv ℝ (dirDeriv U v) p w = fderiv ℝ (fderiv ℝ U) p w v := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ U) p :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p
  rw [show dirDeriv U v = fun p => fderiv ℝ U p v from rfl,
    fderiv_clm_apply h1 (differentiableAt_const v)]
  simp

/-- **Symmetry of mixed partials** (Schwarz) for `C²` fields. -/
theorem fderiv_dirDeriv_comm (hU : ContDiff ℝ 2 U) (v w p : ℝ × ℝ) :
    fderiv ℝ (dirDeriv U v) p w = fderiv ℝ (dirDeriv U w) p v := by
  rw [fderiv_dirDeriv hU, fderiv_dirDeriv hU]
  exact (hU.contDiffAt.isSymmSndFDerivAt (by simp)) w v

variable {u : ℝ → ℝ → ℝ}

/-- `u_t(t, x) = DU(t, x)(1, 0)` for `U = uncurry u` of class `C²`. -/
theorem dt_eq_dirDeriv (hU : ContDiff ℝ 2 (Function.uncurry u)) :
    dt u = fun t x => dirDeriv (Function.uncurry u) (1, 0) (t, x) :=
  funext fun t => funext fun x =>
    (hasDerivAt_fst_of_differentiable (hU.differentiable (by norm_num)) t x).deriv

/-- `u_x(t, x) = DU(t, x)(0, 1)` for `U = uncurry u` of class `C²`. -/
theorem dx_eq_dirDeriv (hU : ContDiff ℝ 2 (Function.uncurry u)) :
    dx u = fun t x => dirDeriv (Function.uncurry u) (0, 1) (t, x) :=
  funext fun t => funext fun x =>
    (hasDerivAt_snd_of_differentiable (hU.differentiable (by norm_num)) t x).deriv

/-- `u_tt(t, x)` in terms of the directional derivative field `u_t`. -/
theorem dt_dt_eq (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    dt (dt u) t x = fderiv ℝ (dirDeriv (Function.uncurry u) (1, 0)) (t, x) (1, 0) := by
  rw [dt_eq_dirDeriv hU]
  exact (hasDerivAt_fst_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).deriv

/-- `u_xx(t, x)` in terms of the directional derivative field `u_x`. -/
theorem dx_dx_eq (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    dx (dx u) t x = fderiv ℝ (dirDeriv (Function.uncurry u) (0, 1)) (t, x) (0, 1) := by
  rw [dx_eq_dirDeriv hU]
  exact (hasDerivAt_snd_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).deriv

/-- A `C²` field is differentiable in time. -/
theorem differentiableAt_t (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => u s x) t :=
  (hasDerivAt_fst_of_differentiable (hU.differentiable (by norm_num)) t x).differentiableAt

/-- A `C²` field is differentiable in space. -/
theorem differentiableAt_x (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (u t) x :=
  (hasDerivAt_snd_of_differentiable (hU.differentiable (by norm_num)) t x).differentiableAt

/-- The velocity of a `C²` field is differentiable in time. -/
theorem differentiableAt_dt_t (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => dt u s x) t := by
  rw [dt_eq_dirDeriv hU]
  exact (hasDerivAt_fst_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).differentiableAt

/-- The strain of a `C²` field is differentiable in space. -/
theorem differentiableAt_dx_x (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (dx u t) x := by
  rw [dx_eq_dirDeriv hU]
  exact (hasDerivAt_snd_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).differentiableAt

/-- Time derivative of a difference of `C²` fields. -/
theorem dt_sub {v : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v)) :
    dt (fun t x => u t x - v t x) = fun t x => dt u t x - dt v t x :=
  funext fun t => funext fun x => deriv_sub (differentiableAt_t hu t x) (differentiableAt_t hv t x)

/-- **Linearity**: the difference of two `C²` solutions of the wave equation is a solution. -/
theorem isWave_sub {c : ℝ} {v : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v)) (hwu : IsWave c u) (hwv : IsWave c v) :
    IsWave c (fun t x => u t x - v t x) := by
  have e2 : dt (fun t x => dt u t x - dt v t x) = fun t x => dt (dt u) t x - dt (dt v) t x :=
    funext fun t => funext fun x =>
      deriv_sub (differentiableAt_dt_t hu t x) (differentiableAt_dt_t hv t x)
  have f1 : dx (fun t x => u t x - v t x) = fun t x => dx u t x - dx v t x :=
    funext fun t => funext fun x =>
      deriv_sub (differentiableAt_x hu t x) (differentiableAt_x hv t x)
  have f2 : dx (fun t x => dx u t x - dx v t x) = fun t x => dx (dx u) t x - dx (dx v) t x :=
    funext fun t => funext fun x =>
      deriv_sub (differentiableAt_dx_x hu t x) (differentiableAt_dx_x hv t x)
  intro t x
  rw [dt_sub hu hv, e2, f1, f2]
  simp only [hwu t x, hwv t x]
  ring

end Partials

section Energy

variable {c L : ℝ} {u : ℝ → ℝ → ℝ}

/-- **Energy** of a string on `[0, L]` (per unit linear density):
`E(t) = ½ ∫₀ᴸ (u_t² + c² u_x²) dx`, kinetic plus elastic (strain) energy. -/
def energy (c L : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / 2 * ∫ x in (0 : ℝ)..L, (dt u t x ^ 2 + c ^ 2 * dx u t x ^ 2)

/-- **Energy balance**: for a `C²` solution of the wave equation on a string fixed at both ends,
`dE/dt = 0`. -/
theorem hasDerivAt_energy (hU : ContDiff ℝ 2 (Function.uncurry u)) (hw : IsWave c u)
    (h0 : ∀ t, u t 0 = 0) (hL : ∀ t, u t L = 0) (t : ℝ) :
    HasDerivAt (energy c L u) 0 t := by
  set A := dirDeriv (Function.uncurry u) (1, 0) with hAdef
  set B := dirDeriv (Function.uncurry u) (0, 1) with hBdef
  have hA : ContDiff ℝ 1 A := contDiff_dirDeriv hU _
  have hB : ContDiff ℝ 1 B := contDiff_dirDeriv hU _
  have dA := hA.differentiable one_ne_zero
  have dB := hB.differentiable one_ne_zero
  have cA : Continuous A := hA.continuous
  have cB : Continuous B := hB.continuous
  have cA1 : Continuous fun p => fderiv ℝ A p (1, 0) :=
    (hA.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cA2 : Continuous fun p => fderiv ℝ A p (0, 1) :=
    (hA.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cB1 : Continuous fun p => fderiv ℝ B p (1, 0) :=
    (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cB2 : Continuous fun p => fderiv ℝ B p (0, 1) :=
    (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set Fp : ℝ × ℝ → ℝ := fun p => A p ^ 2 + c ^ 2 * B p ^ 2 with hFp
  set Gp : ℝ × ℝ → ℝ := fun p =>
    2 * A p * fderiv ℝ A p (1, 0) + c ^ 2 * (2 * B p * fderiv ℝ B p (1, 0)) with hGp
  have cF : Continuous Fp := by fun_prop
  have cG : Continuous Gp := by fun_prop
  have hE : energy c L u = fun s => 1 / 2 * ∫ x in (0 : ℝ)..L, Fp (s, x) := by
    funext s
    simp only [energy, dt_eq_dirDeriv hU, dx_eq_dirDeriv hU, Fp, A, B]
  have hFd : ∀ s x, HasDerivAt (fun s => Fp (s, x)) (Gp (s, x)) s := by
    intro s x
    have h1 := hasDerivAt_fst_of_differentiable dA s x
    have h2 := hasDerivAt_fst_of_differentiable dB s x
    convert (h1.pow 2).add ((h2.pow 2).const_mul (c ^ 2)) using 1
    simp only [Gp]
    ring
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t 1).prod (isCompact_uIcc (a := (0 : ℝ)) (b := L))
    ).exists_bound_of_continuousOn cG.continuousOn
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := L) (F := fun s x => Fp (s, x)) (F' := fun s x => Gp (s, x))
    (x₀ := t) (bound := fun _ => M) (Metric.closedBall_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s =>
      (cF.comp (Continuous.prodMk_right s)).aestronglyMeasurable)
    ((cF.comp (Continuous.prodMk_right t)).intervalIntegrable 0 L)
    (cG.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x hx s hs =>
      hM (s, x) ⟨hs, Set.uIoc_subset_uIcc hx⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun x _ s _ => hFd s x)
  rw [hE]
  refine (hd.2.const_mul (1 / 2)).congr_deriv ?_
  -- the time derivative of the energy density is an exact `x`-derivative
  have hwave : ∀ x, fderiv ℝ A (t, x) (1, 0) = c ^ 2 * fderiv ℝ B (t, x) (0, 1) := fun x => by
    rw [← dt_dt_eq hU, ← dx_dx_eq hU]
    exact hw t x
  have hsym : ∀ x, fderiv ℝ B (t, x) (1, 0) = fderiv ℝ A (t, x) (0, 1) := fun x =>
    fderiv_dirDeriv_comm hU _ _ _
  have hflux : ∀ x, HasDerivAt (fun y => 2 * c ^ 2 * (A (t, y) * B (t, y))) (Gp (t, x)) x := by
    intro x
    convert ((hasDerivAt_snd_of_differentiable dA t x).mul
      (hasDerivAt_snd_of_differentiable dB t x)).const_mul (2 * c ^ 2) using 1
    simp only [Gp, hwave, hsym]
    ring
  have hA0 : ∀ y, A (t, y) = dt u t y := fun y => by rw [dt_eq_dirDeriv hU]
  have hA0' : A (t, 0) = 0 := by
    rw [hA0]
    simp only [dt, h0, deriv_const]
  have hAL : A (t, L) = 0 := by
    rw [hA0]
    simp only [dt, hL, deriv_const]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hflux x)
    ((cG.comp (Continuous.prodMk_right t)).intervalIntegrable 0 L), hA0', hAL]
  simp

/-- **Conservation of energy** for the string fixed at both ends: `E(t) = E(t')`. -/
theorem energy_const (hU : ContDiff ℝ 2 (Function.uncurry u)) (hw : IsWave c u)
    (h0 : ∀ t, u t 0 = 0) (hL : ∀ t, u t L = 0) (t t' : ℝ) :
    energy c L u t = energy c L u t' :=
  is_const_of_deriv_eq_zero (fun s => (hasDerivAt_energy hU hw h0 hL s).differentiableAt)
    (fun s => (hasDerivAt_energy hU hw h0 hL s).deriv) t t'

/-- **Zero data give the zero solution**: a `C²` solution of the wave equation on `[0, L]` with
fixed ends and vanishing initial displacement and velocity vanishes on `[0, L]` for all time.
The energy is conserved and initially zero, so `u_t ≡ 0` on `[0, L]`. -/
theorem eq_zero_of_zero_data (hLpos : 0 < L) (hU : ContDiff ℝ 2 (Function.uncurry u))
    (hw : IsWave c u) (h0 : ∀ t, u t 0 = 0) (hL : ∀ t, u t L = 0)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = 0) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = 0) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = 0 := by
  set A := dirDeriv (Function.uncurry u) (1, 0) with hAdef
  set B := dirDeriv (Function.uncurry u) (0, 1) with hBdef
  have cA : Continuous A := (contDiff_dirDeriv hU _).continuous
  have cB : Continuous B := (contDiff_dirDeriv hU _).continuous
  have eA : ∀ t y, dt u t y = A (t, y) := fun t y => by rw [dt_eq_dirDeriv hU]
  have eB : ∀ t y, dx u t y = B (t, y) := fun t y => by rw [dx_eq_dirDeriv hU]
  have cF : ∀ t, Continuous fun y => A (t, y) ^ 2 + c ^ 2 * B (t, y) ^ 2 := fun t =>
    ((cA.comp (Continuous.prodMk_right t)).pow 2).add
      (continuous_const.mul ((cB.comp (Continuous.prodMk_right t)).pow 2))
  -- the initial strain vanishes on `[0, L]`
  have hB0 : EqOn (fun y => B (0, y)) 0 (Icc 0 L) := by
    refine EqOn.of_subset_closure (s := Ioo 0 L) (fun y hy => ?_)
      (cB.comp (Continuous.prodMk_right 0)).continuousOn continuousOn_const Ioo_subset_Icc_self
      (closure_Ioo hLpos.ne).symm.subset
    have hev : u 0 =ᶠ[nhds y] fun _ => 0 :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hy.1 hy.2)
        fun z hz => hi z (Ioo_subset_Icc_self hz)
    simp only [Pi.zero_apply, ← eB, dx, hev.deriv_eq, deriv_const]
  -- the energy vanishes at all times
  have hE0 : ∫ x in (0 : ℝ)..L, (A (0, x) ^ 2 + c ^ 2 * B (0, x) ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
      rw [uIcc_of_le hLpos.le] at hx
      have hb := hB0 hx
      simp only [Pi.zero_apply] at hb
      simp only [← eA, hi' x hx, hb]
      ring)]
    simp
  have hE : ∀ t, ∫ x in (0 : ℝ)..L, (A (t, x) ^ 2 + c ^ 2 * B (t, x) ^ 2) = 0 := by
    intro t
    have h1 := energy_const hU hw h0 hL t 0
    simp only [energy, eA, eB, hE0] at h1
    linarith
  -- hence `u_t = 0` on `[0, L]`
  have hF0 : ∀ s, EqOn (fun y => A (s, y) ^ 2 + c ^ 2 * B (s, y) ^ 2) 0 (Icc 0 L) := by
    intro s
    have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => by positivity)
      ((cF s).intervalIntegrable 0 L)).1 (hE s)
    rw [Ioc_eq_empty (not_lt.2 hLpos.le), union_empty,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
    exact Measure.eqOn_Icc_of_ae_eq volume hLpos.ne hae (cF s).continuousOn continuousOn_const
  intro t x hx
  have hAt : ∀ s, dt u s x = 0 := by
    intro s
    have h := hF0 s hx
    simp only [Pi.zero_apply] at h
    rw [eA]
    nlinarith [sq_nonneg (A (s, x)), mul_nonneg (sq_nonneg c) (sq_nonneg (B (s, x)))]
  rw [is_const_of_deriv_eq_zero (f := fun s => u s x) (fun s => differentiableAt_t hU s x) hAt t 0]
  exact hi x hx

/-- **Uniqueness for the initial–boundary value problem** of the string fixed at both ends:
two `C²` solutions of `u_tt = c² u_xx` with `u(t, 0) = u(t, L) = 0` and the same initial
displacement and velocity on `[0, L]` coincide on `[0, L]` for all time. -/
theorem unique {v : ℝ → ℝ → ℝ} (hLpos : 0 < L) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v)) (hwu : IsWave c u) (hwv : IsWave c v)
    (hu0 : ∀ t, u t 0 = 0) (huL : ∀ t, u t L = 0) (hv0 : ∀ t, v t 0 = 0) (hvL : ∀ t, v t L = 0)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = dt v 0 x) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = v t x := by
  intro t x hx
  have hw : ContDiff ℝ 2 (Function.uncurry fun t x => u t x - v t x) := hu.sub hv
  have h := eq_zero_of_zero_data hLpos hw (isWave_sub hu hv hwu hwv)
    (fun t => by simp [hu0, hv0]) (fun t => by simp [huL, hvL])
    (fun x hx => sub_eq_zero.2 (hi x hx))
    (fun x hx => by rw [dt_sub hu hv]; exact sub_eq_zero.2 (hi' x hx)) t x hx
  exact sub_eq_zero.1 h

end Energy

/-! ### Physical constants: wave speed and Mersenne's laws -/

/-- A **vibrating string** of length `L`, tension `T` and linear density `ρ` (mass per unit
length), fixed at both ends. -/
structure VibratingString where
  /-- Length. -/
  L : ℝ
  /-- Tension. -/
  T : ℝ
  /-- Linear density (mass per unit length). -/
  ρ : ℝ
  L_pos : 0 < L
  T_pos : 0 < T
  ρ_pos : 0 < ρ

namespace VibratingString

variable (s : VibratingString)

/-- The **wave speed** `c = √(T / ρ)`. -/
def waveSpeed : ℝ := √(s.T / s.ρ)

/-- The wave speed is positive. -/
theorem waveSpeed_pos : 0 < s.waveSpeed :=
  sqrt_pos.2 (div_pos s.T_pos s.ρ_pos)

/-- `c² = T / ρ`. -/
theorem waveSpeed_sq : s.waveSpeed ^ 2 = s.T / s.ρ :=
  sq_sqrt (div_pos s.T_pos s.ρ_pos).le

/-- **Newton's equation for the string**: `u_tt = c² u_xx` with `c² = T / ρ` is equivalent to
`ρ u_tt = T u_xx` (mass times acceleration equals the net transverse tension force). -/
theorem isWave_iff (u : ℝ → ℝ → ℝ) :
    IsWave s.waveSpeed u ↔ ∀ t x, s.ρ * dt (dt u) t x = s.T * dx (dx u) t x := by
  have hρ := s.ρ_pos.ne'
  refine forall₂_congr fun t x => ?_
  rw [waveSpeed_sq]
  constructor <;> intro h
  · rw [h]; field_simp
  · rw [div_mul_eq_mul_div, eq_div_iff hρ, mul_comm, h]

/-- The frequency (in cycles per unit time) of the `n`-th harmonic: `fₙ = (n / 2L) √(T / ρ)`. -/
def frequency (n : ℕ) : ℝ := n / (2 * s.L) * √(s.T / s.ρ)

/-- The `n`-th harmonic frequency is `ωₙ / 2π` with `ωₙ = nπc / L` the angular frequency of the
`n`-th normal mode. -/
theorem frequency_eq_omega (n : ℕ) : s.frequency n = omega s.L s.waveSpeed n / (2 * π) := by
  have := s.L_pos.ne'
  simp only [frequency, omega, waveSpeed]
  field_simp

/-- **Fundamental frequency** (Mersenne's laws): `f₁ = (1 / 2L) √(T / ρ)`. -/
theorem frequency_one : s.frequency 1 = 1 / (2 * s.L) * √(s.T / s.ρ) := by
  simp [frequency]

/-- **Harmonic series**: `fₙ = n f₁`. -/
theorem frequency_eq_mul (n : ℕ) : s.frequency n = n * s.frequency 1 := by
  simp only [frequency]
  ring

/-- The `n`-th normal mode of the physical string solves `ρ u_tt = T u_xx` and is fixed at
both ends. -/
theorem mode_solves (n : ℕ) (a b : ℝ) :
    (∀ t x, s.ρ * dt (dt (mode s.L s.waveSpeed n a b)) t x =
      s.T * dx (dx (mode s.L s.waveSpeed n a b)) t x) ∧
    ∀ t, mode s.L s.waveSpeed n a b t 0 = 0 ∧ mode s.L s.waveSpeed n a b t s.L = 0 :=
  ⟨(s.isWave_iff _).1 (isWave_mode _ _ n a b),
    fun t => mode_boundary _ s.L_pos.ne' n a b t⟩

end VibratingString

/-- The fundamental frequency `f₁(L, T, ρ) = (1 / 2L) √(T / ρ)` as a function of the length,
tension and linear density. -/
def fundamental (L T ρ : ℝ) : ℝ := 1 / (2 * L) * √(T / ρ)

/-- **Mersenne's first law**: the fundamental frequency is inversely proportional to the
length. -/
theorem fundamental_length (L T ρ k : ℝ) :
    fundamental (k * L) T ρ = fundamental L T ρ / k := by
  simp only [fundamental]
  ring

/-- **Mersenne's second law**: the fundamental frequency is proportional to the square root of
the tension (multiplying `T` by `k²` multiplies `f₁` by `k ≥ 0`). -/
theorem fundamental_tension (L T ρ : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    fundamental L (k ^ 2 * T) ρ = k * fundamental L T ρ := by
  simp only [fundamental, mul_div_assoc, sqrt_mul (sq_nonneg k), sqrt_sq hk]
  ring

/-- **Mersenne's third law**: the fundamental frequency is inversely proportional to the square
root of the linear density (multiplying `ρ` by `k²` divides `f₁` by `k ≥ 0`). -/
theorem fundamental_density (L T ρ : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    fundamental L T (k ^ 2 * ρ) = fundamental L T ρ / k := by
  simp only [fundamental]
  rw [show T / (k ^ 2 * ρ) = (T / ρ) / k ^ 2 by ring, sqrt_div' _ (sq_nonneg k), sqrt_sq hk]
  ring

end ContinuumMechanics.Strings
