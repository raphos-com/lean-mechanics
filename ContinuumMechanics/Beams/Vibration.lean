import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import ContinuumMechanics.Beams.String
import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Free vibrations of Euler–Bernoulli beams

Small free transverse vibrations `w(t, x)` of a prismatic Euler–Bernoulli beam of length `L`,
mass per unit length `ρA > 0` and bending stiffness `EI > 0` obey
`ρA w_tt + EI w_xxxx = 0` on `[0, L]` ([Rao2007], Ch. 11; [Meirovitch1967], §5.10;
[TimoshenkoYoungWeaver1974], §5.9–5.11). Fields `w : ℝ → ℝ → ℝ` (time, then position) and the
partial derivatives `dt`, `dx` are those of `Beams/String.lean`; in the code `rA = ρA`.

## Main definitions

* `Vibration.IsBeamVib rA EI w`: the beam equation `ρA w_tt + EI w_xxxx = 0`.
* `Vibration.beamOmega L rA EI n`: `ωₙ = (nπ/L)² √(EI/ρA)`; `Vibration.beamMode`: the
  simply supported normal modes `sin(nπx/L)(a cos ωₙt + b sin ωₙt)`; `Vibration.beamModeSum`.
* `Vibration.energy rA EI L w t = ½ ∫₀ᴸ (ρA w_t² + EI w_xx²) dx` and the end power flux
  `Vibration.flux`.
* `Vibration.EndSupport`: pinned, clamped or free ends, with `EndSupport.Holds`.
* `Vibration.cantileverShape β σ`: `φ(x) = (cosh βx - cos βx) - σ (sinh βx - sin βx)`, with
  `Vibration.sigma β L = (cosh βL + cos βL) / (sinh βL + sin βL)`.

## Main results

* `isBeamVib_mode`, `beamMode_boundary`, `isBeamVib_modeSum`, `beamModeSum_boundary`: normal
  modes and their finite superpositions solve the simply supported problem; `isBeamVib_sum`
  (superposition); `beamOmega_eq_sq_mul`: `ωₙ = n² ω₁`; `integral_beamMode_mul_beamMode`:
  orthogonality of the modes in `L²(0, L)`.
* `hasDerivAt_energy`, `energy_const`, `energy_const_of_supports`: **conservation of energy**
  for `C⁴` solutions with pinned, clamped or free ends (two integrations by parts; the end
  power flux `EI (w_xx w_xt - w_t w_xxx)` vanishes).
* `eq_zero_of_zero_data`, `unique`, `unique_simplySupported`, `unique_clamped`,
  `unique_cantilever`: **uniqueness** for the initial–boundary value problem.
* `cantileverShape_clamped`, `cantileverShape_free`, `iteratedDeriv_four_cantileverShape`:
  under the **cantilever frequency equation** `cos βL cosh βL = -1`, `φ'''' = β⁴ φ`,
  `φ(0) = φ'(0) = 0`, `φ''(L) = φ'''(L) = 0` and `φ''(0) = 2β² ≠ 0`; `cantileverMode_solves`:
  `φ(x)(a cos ωt + b sin ωt)` with `ω = β² √(EI/ρA)` solves the clamped–free problem;
  `exists_root_frequency_equation`: the frequency equation has a root in `(π/2, π)`.
* `beamOmega_sq_eq_rayleigh`: **Rayleigh's quotient** `ωₙ² = EI ∫ φₙ''² / (ρA ∫ φₙ²)` for the
  simply supported mode shapes.

## References

* [Rao2007] S. S. Rao, *Vibration of Continuous Systems*, Ch. 11.
* [Meirovitch1967] L. Meirovitch, *Analytical Methods in Vibrations*, §5.10.
* [TimoshenkoYoungWeaver1974] S. Timoshenko, D. H. Young, W. Weaver, *Vibration Problems in
  Engineering*, 4th ed., §5.9–5.11.
-/

open Set Real MeasureTheory

noncomputable section

namespace ContinuumMechanics.Beams.Vibration

open ContinuumMechanics.Strings

/-- The **Euler–Bernoulli beam equation** for free vibrations, `ρA w_tt + EI w_xxxx = 0`, at
every time and position. Here `rA = ρA` is the mass per unit length. -/
def IsBeamVib (rA EI : ℝ) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, rA * dt (dt w) t x + EI * dx (dx (dx (dx w))) t x = 0

/-! ### Superposition -/

section Superposition

variable {ι : Type*}

/-- **Superposition principle**: a finite sum of (sufficiently differentiable) solutions of the
beam equation is a solution. -/
theorem isBeamVib_sum {rA EI : ℝ} (s : Finset ι) (u : ι → ℝ → ℝ → ℝ)
    (ht : ∀ i t x, DifferentiableAt ℝ (fun s => u i s x) t)
    (htt : ∀ i t x, DifferentiableAt ℝ (fun s => dt (u i) s x) t)
    (hx : ∀ i t x, DifferentiableAt ℝ (u i t) x) (hxx : ∀ i t x, DifferentiableAt ℝ (dx (u i) t) x)
    (hx3 : ∀ i t x, DifferentiableAt ℝ (dx (dx (u i)) t) x)
    (hx4 : ∀ i t x, DifferentiableAt ℝ (dx (dx (dx (u i))) t) x)
    (hw : ∀ i ∈ s, IsBeamVib rA EI (u i)) : IsBeamVib rA EI (fun t x => ∑ i ∈ s, u i t x) := by
  intro t x
  rw [dt_sum s u ht, dt_sum s (fun i => dt (u i)) htt, dx_sum s u hx,
    dx_sum s (fun i => dx (u i)) hxx, dx_sum s (fun i => dx (dx (u i))) hx3,
    dx_sum s (fun i => dx (dx (dx (u i)))) hx4, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i hi => hw i hi t x

end Superposition

/-! ### Simply supported beams: normal modes -/

section Modes

/-- A separated standing wave `X(x) T(t)` (harmonic `X` of wavenumber `k`, harmonic `T` of angular
frequency `ω`) solves the beam equation when the dispersion relation `ρA ω² = EI k⁴` holds. -/
theorem isBeamVib_sep {rA EI k ω : ℝ} (hω : rA * ω ^ 2 = EI * k ^ 4) (p q a b : ℝ) :
    IsBeamVib rA EI (sep k ω p q a b) := by
  intro t x
  rw [dt_sep, dt_sep, dx_sep, dx_sep, dx_sep, dx_sep]
  simp only [sep, harm]
  linear_combination (-(p * cos (k * x) + q * sin (k * x)) *
    (a * cos (ω * t) + b * sin (ω * t))) * hω

variable (L rA EI : ℝ)

/-- Angular frequency of the `n`-th mode of a simply supported beam:
`ωₙ = (nπ / L)² √(EI / ρA)`. -/
def beamOmega (n : ℕ) : ℝ := (n * π / L) ^ 2 * √(EI / rA)

/-- The `n`-th **normal mode** of a simply supported beam of length `L`:
`wₙ(t, x) = sin(nπx / L) (a cos(ωₙ t) + b sin(ωₙ t))`. -/
def beamMode (n : ℕ) (a b t x : ℝ) : ℝ :=
  sin (n * π / L * x) * (a * cos (beamOmega L rA EI n * t) + b * sin (beamOmega L rA EI n * t))

/-- A normal mode is a separated standing wave. -/
theorem beamMode_eq_sep (n : ℕ) (a b : ℝ) :
    beamMode L rA EI n a b = sep (wavenumber L n) (beamOmega L rA EI n) 0 1 a b := by
  funext t x
  simp [beamMode, sep, harm, wavenumber]

/-- **Frequencies scale as `n²`**: `ωₙ = n² ω₁`. -/
theorem beamOmega_eq_sq_mul (n : ℕ) : beamOmega L rA EI n = n ^ 2 * beamOmega L rA EI 1 := by
  simp only [beamOmega, Nat.cast_one]
  ring

variable {rA EI}

/-- Dispersion relation of the normal modes: `ρA ωₙ² = EI kₙ⁴` (`ρA > 0`, `EI ≥ 0`). -/
theorem beamOmega_sq (hrA : 0 < rA) (hEI : 0 ≤ EI) (n : ℕ) :
    rA * beamOmega L rA EI n ^ 2 = EI * wavenumber L n ^ 4 := by
  simp only [beamOmega, wavenumber, mul_pow, sq_sqrt (div_nonneg hEI hrA.le)]
  field_simp

/-- **Normal modes solve the beam equation.** -/
theorem isBeamVib_mode (hrA : 0 < rA) (hEI : 0 ≤ EI) (n : ℕ) (a b : ℝ) :
    IsBeamVib rA EI (beamMode L rA EI n a b) := by
  rw [beamMode_eq_sep]
  exact isBeamVib_sep (beamOmega_sq L hrA hEI n) _ _ _ _

variable (rA EI)

/-- `∂ₓ²` of a normal mode: `∂ₓ²wₙ = -kₙ² wₙ`. -/
theorem dx_dx_mode (n : ℕ) (a b : ℝ) :
    dx (dx (beamMode L rA EI n a b)) =
      fun t x => -wavenumber L n ^ 2 * beamMode L rA EI n a b t x := by
  rw [beamMode_eq_sep, dx_sep, dx_sep]
  funext t x
  simp only [sep, harm]
  ring

/-- **Normal modes satisfy the simply supported boundary conditions**
`w = w_xx = 0` at `x = 0` and `x = L`. -/
theorem beamMode_boundary {L : ℝ} (hL : L ≠ 0) (n : ℕ) (a b t : ℝ) :
    beamMode L rA EI n a b t 0 = 0 ∧ beamMode L rA EI n a b t L = 0 ∧
      dx (dx (beamMode L rA EI n a b)) t 0 = 0 ∧ dx (dx (beamMode L rA EI n a b)) t L = 0 := by
  have h0 : beamMode L rA EI n a b t 0 = 0 := by simp [beamMode]
  have hL' : beamMode L rA EI n a b t L = 0 := by
    simp only [beamMode]
    rw [div_mul_cancel₀ _ hL, sin_nat_mul_pi, zero_mul]
  rw [dx_dx_mode]
  exact ⟨h0, hL', by simp only [h0, mul_zero], by simp only [hL', mul_zero]⟩

/-- A finite superposition of normal modes `∑ₙ wₙ` with amplitudes `aₙ, bₙ`. -/
def beamModeSum (s : Finset ℕ) (a b : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑ n ∈ s, beamMode L rA EI n (a n) (b n) t x

/-- Spatial differentiability of a normal mode and of its first three `x`-derivatives. -/
theorem differentiableAt_mode_x (n : ℕ) (a b t x : ℝ) :
    DifferentiableAt ℝ (beamMode L rA EI n a b t) x ∧
      DifferentiableAt ℝ (dx (beamMode L rA EI n a b) t) x ∧
      DifferentiableAt ℝ (dx (dx (beamMode L rA EI n a b)) t) x ∧
      DifferentiableAt ℝ (dx (dx (dx (beamMode L rA EI n a b))) t) x := by
  simp only [beamMode_eq_sep, dx_sep]
  exact ⟨differentiableAt_sep_x .., differentiableAt_sep_x .., differentiableAt_sep_x ..,
    differentiableAt_sep_x ..⟩

/-- **Finite superpositions of normal modes solve the beam equation.** -/
theorem isBeamVib_modeSum (hrA : 0 < rA) (hEI : 0 ≤ EI) (s : Finset ℕ) (a b : ℕ → ℝ) :
    IsBeamVib rA EI (beamModeSum L rA EI s a b) := by
  have e : ∀ n, beamMode L rA EI n (a n) (b n) =
      sep (wavenumber L n) (beamOmega L rA EI n) 0 1 (a n) (b n) :=
    fun n => beamMode_eq_sep L rA EI n _ _
  refine isBeamVib_sum s (fun n => beamMode L rA EI n (a n) (b n)) (fun n t x => ?_)
    (fun n t x => ?_) (fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).1)
    (fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).2.1)
    (fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).2.2.1)
    (fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).2.2.2)
    fun n _ => isBeamVib_mode L hrA hEI n _ _
  · simp only [e]; exact differentiableAt_sep_t ..
  · simp only [e, dt_sep]; exact differentiableAt_sep_t ..

/-- **Finite superpositions of normal modes satisfy the simply supported boundary
conditions.** -/
theorem beamModeSum_boundary {L : ℝ} (hL : L ≠ 0) (s : Finset ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    beamModeSum L rA EI s a b t 0 = 0 ∧ beamModeSum L rA EI s a b t L = 0 ∧
      dx (dx (beamModeSum L rA EI s a b)) t 0 = 0 ∧
        dx (dx (beamModeSum L rA EI s a b)) t L = 0 := by
  have h2 : dx (dx (beamModeSum L rA EI s a b)) =
      fun t x => ∑ n ∈ s, dx (dx (beamMode L rA EI n (a n) (b n))) t x := by
    change dx (dx (fun t x => ∑ n ∈ s, beamMode L rA EI n (a n) (b n) t x)) = _
    rw [dx_sum s _ fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).1,
      dx_sum s (fun n => dx (beamMode L rA EI n (a n) (b n)))
        fun n t x => (differentiableAt_mode_x L rA EI n _ _ t x).2.1]
  rw [h2]
  exact ⟨Finset.sum_eq_zero fun n _ => (beamMode_boundary rA EI hL n _ _ t).1,
    Finset.sum_eq_zero fun n _ => (beamMode_boundary rA EI hL n _ _ t).2.1,
    Finset.sum_eq_zero fun n _ => (beamMode_boundary rA EI hL n _ _ t).2.2.1,
    Finset.sum_eq_zero fun n _ => (beamMode_boundary rA EI hL n _ _ t).2.2.2⟩

/-- **Orthogonality of the normal modes** in `L²(0, L)` at every time: for `m ≥ 1`,
`∫₀ᴸ wₙ(t) wₘ(t) dx = (L / 2) Tₙ(t) Tₘ(t) δₙₘ` with `Tₙ(t) = a cos ωₙt + b sin ωₙt`. -/
theorem integral_beamMode_mul_beamMode {L : ℝ} (hL : L ≠ 0) {n m : ℕ} (hm : m ≠ 0)
    (a b a' b' t : ℝ) :
    ∫ x in (0 : ℝ)..L, beamMode L rA EI n a b t x * beamMode L rA EI m a' b' t x =
      if n = m then L / 2 * (harm (beamOmega L rA EI n) a b t * harm (beamOmega L rA EI m) a' b' t)
      else 0 := by
  have e : ∀ x, beamMode L rA EI n a b t x * beamMode L rA EI m a' b' t x =
      sin (n * π / L * x) * sin (m * π / L * x) *
        (harm (beamOmega L rA EI n) a b t * harm (beamOmega L rA EI m) a' b' t) := fun x => by
    simp only [beamMode, harm]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_mul_const, integral_sin_mul_sin hL hm]
  split_ifs <;> simp

end Modes

/-! ### Partial derivatives of smooth fields -/

section Fields

variable {u v : ℝ → ℝ → ℝ}

/-- For a `C¹` field, `(t, x) ↦ u_t(t, x)` is the directional derivative `DU(t, x)(1, 0)`. -/
theorem uncurry_dt (hu : ContDiff ℝ 1 (Function.uncurry u)) :
    Function.uncurry (dt u) = dirDeriv (Function.uncurry u) (1, 0) :=
  funext fun ⟨t, x⟩ => (hasDerivAt_fst_of_differentiable (hu.differentiable one_ne_zero) t x).deriv

/-- For a `C¹` field, `(t, x) ↦ u_x(t, x)` is the directional derivative `DU(t, x)(0, 1)`. -/
theorem uncurry_dx (hu : ContDiff ℝ 1 (Function.uncurry u)) :
    Function.uncurry (dx u) = dirDeriv (Function.uncurry u) (0, 1) :=
  funext fun ⟨t, x⟩ => (hasDerivAt_snd_of_differentiable (hu.differentiable one_ne_zero) t x).deriv

/-- The time derivative of a `Cᵐ` field is `Cⁿ` for `n + 1 ≤ m`. -/
theorem contDiff_dt {m n : WithTop ℕ∞} (hu : ContDiff ℝ m (Function.uncurry u))
    (hmn : n + 1 ≤ m) : ContDiff ℝ n (Function.uncurry (dt u)) := by
  rw [uncurry_dt (hu.of_le (le_add_self.trans hmn))]
  exact (hu.fderiv_right hmn).clm_apply contDiff_const

/-- The space derivative of a `Cᵐ` field is `Cⁿ` for `n + 1 ≤ m`. -/
theorem contDiff_dx {m n : WithTop ℕ∞} (hu : ContDiff ℝ m (Function.uncurry u))
    (hmn : n + 1 ≤ m) : ContDiff ℝ n (Function.uncurry (dx u)) := by
  rw [uncurry_dx (hu.of_le (le_add_self.trans hmn))]
  exact (hu.fderiv_right hmn).clm_apply contDiff_const

/-- The time derivative of a `C¹` field, as a `HasDerivAt` statement. -/
theorem hasDerivAt_dt (hu : ContDiff ℝ 1 (Function.uncurry u)) (t x : ℝ) :
    HasDerivAt (fun s => u s x) (dt u t x) t :=
  (hasDerivAt_fst_of_differentiable (hu.differentiable one_ne_zero) t x).differentiableAt.hasDerivAt

/-- The space derivative of a `C¹` field, as a `HasDerivAt` statement. -/
theorem hasDerivAt_dx (hu : ContDiff ℝ 1 (Function.uncurry u)) (t x : ℝ) :
    HasDerivAt (u t) (dx u t x) x :=
  (hasDerivAt_snd_of_differentiable (hu.differentiable one_ne_zero) t x).differentiableAt.hasDerivAt

/-- **Symmetry of mixed partials** (Schwarz) for `C²` fields: `∂ₜ∂ₓu = ∂ₓ∂ₜu`. -/
theorem dt_dx_comm (hu : ContDiff ℝ 2 (Function.uncurry u)) : dt (dx u) = dx (dt u) := by
  have h1 : ContDiff ℝ 1 (Function.uncurry u) := hu.of_le (by norm_num)
  funext t x
  calc dt (dx u) t x = dirDeriv (Function.uncurry (dx u)) (1, 0) (t, x) :=
        congrFun (uncurry_dt (contDiff_dx hu (by norm_num))) (t, x)
    _ = dirDeriv (dirDeriv (Function.uncurry u) (0, 1)) (1, 0) (t, x) := by rw [uncurry_dx h1]
    _ = dirDeriv (dirDeriv (Function.uncurry u) (1, 0)) (0, 1) (t, x) :=
        fderiv_dirDeriv_comm hu _ _ _
    _ = dirDeriv (Function.uncurry (dt u)) (0, 1) (t, x) := by rw [uncurry_dt h1]
    _ = dx (dt u) t x := (congrFun (uncurry_dx (contDiff_dt hu (by norm_num))) (t, x)).symm

/-- Time derivative of a difference of `C¹` fields. -/
theorem dt_fun_sub (hu : ContDiff ℝ 1 (Function.uncurry u))
    (hv : ContDiff ℝ 1 (Function.uncurry v)) :
    dt (fun t x => u t x - v t x) = fun t x => dt u t x - dt v t x :=
  funext fun t => funext fun x => ((hasDerivAt_dt hu t x).sub (hasDerivAt_dt hv t x)).deriv

/-- Space derivative of a difference of `C¹` fields. -/
theorem dx_fun_sub (hu : ContDiff ℝ 1 (Function.uncurry u))
    (hv : ContDiff ℝ 1 (Function.uncurry v)) :
    dx (fun t x => u t x - v t x) = fun t x => dx u t x - dx v t x :=
  funext fun t => funext fun x => ((hasDerivAt_dx hu t x).sub (hasDerivAt_dx hv t x)).deriv

/-- The first three space derivatives of a difference of `C⁴` fields. -/
theorem dx_iter_sub (hu : ContDiff ℝ 4 (Function.uncurry u))
    (hv : ContDiff ℝ 4 (Function.uncurry v)) :
    dx (fun t x => u t x - v t x) = (fun t x => dx u t x - dx v t x) ∧
      dx (dx (fun t x => u t x - v t x)) = (fun t x => dx (dx u) t x - dx (dx v) t x) ∧
      dx (dx (dx (fun t x => u t x - v t x))) =
        fun t x => dx (dx (dx u)) t x - dx (dx (dx v)) t x := by
  have u1 : ContDiff ℝ 3 (Function.uncurry (dx u)) := contDiff_dx hu (by norm_num)
  have v1 : ContDiff ℝ 3 (Function.uncurry (dx v)) := contDiff_dx hv (by norm_num)
  have u2 : ContDiff ℝ 2 (Function.uncurry (dx (dx u))) := contDiff_dx u1 (by norm_num)
  have v2 : ContDiff ℝ 2 (Function.uncurry (dx (dx v))) := contDiff_dx v1 (by norm_num)
  have e1 := dx_fun_sub (hu.of_le (by norm_num)) (hv.of_le (by norm_num))
  have e2 := dx_fun_sub (u1.of_le (by norm_num)) (v1.of_le (by norm_num))
  have e3 := dx_fun_sub (u2.of_le (by norm_num)) (v2.of_le (by norm_num))
  exact ⟨e1, by rw [e1, e2], by rw [e1, e2, e3]⟩

/-- **Linearity**: the difference of two `C⁴` solutions of the beam equation is a solution. -/
theorem isBeamVib_sub {rA EI : ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u))
    (hv : ContDiff ℝ 4 (Function.uncurry v)) (hwu : IsBeamVib rA EI u)
    (hwv : IsBeamVib rA EI v) : IsBeamVib rA EI (fun t x => u t x - v t x) := by
  obtain ⟨-, -, e3⟩ := dx_iter_sub hu hv
  have u3 : ContDiff ℝ 1 (Function.uncurry (dx (dx (dx u)))) :=
    contDiff_dx (contDiff_dx (contDiff_dx hu (n := 3) (by norm_num)) (n := 2) (by norm_num))
      (by norm_num)
  have v3 : ContDiff ℝ 1 (Function.uncurry (dx (dx (dx v)))) :=
    contDiff_dx (contDiff_dx (contDiff_dx hv (n := 3) (by norm_num)) (n := 2) (by norm_num))
      (by norm_num)
  have ut : ContDiff ℝ 1 (Function.uncurry (dt u)) := contDiff_dt hu (by norm_num)
  have vt : ContDiff ℝ 1 (Function.uncurry (dt v)) := contDiff_dt hv (by norm_num)
  intro t x
  rw [dt_fun_sub (hu.of_le (by norm_num)) (hv.of_le (by norm_num)), dt_fun_sub ut vt, e3,
    dx_fun_sub u3 v3]
  linear_combination hwu t x - hwv t x

end Fields

/-! ### Energy conservation and uniqueness -/

section Energy

variable {rA EI L : ℝ} {w : ℝ → ℝ → ℝ}

/-- **Energy** of a vibrating beam on `[0, L]`:
`E(t) = ½ ∫₀ᴸ (ρA w_t² + EI w_xx²) dx`, kinetic plus bending (strain) energy. -/
def energy (rA EI L : ℝ) (w : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / 2 * ∫ x in (0 : ℝ)..L, (rA * dt w t x ^ 2 + EI * dx (dx w) t x ^ 2)

/-- The **power flux** (divided by `EI`) through the section at `x`:
`w_xx w_xt - w_t w_xxx`, i.e. (minus) the rate of work of the bending moment and shear force. -/
def flux (w : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  dx (dx w) t x * dx (dt w) t x - dt w t x * dx (dx (dx w)) t x

/-- **Energy balance**: for a `C⁴` solution of the beam equation whose power flux vanishes at
both ends, `dE/dt = 0`. -/
theorem hasDerivAt_energy (hU : ContDiff ℝ 4 (Function.uncurry w)) (hw : IsBeamVib rA EI w)
    (h0 : ∀ t, flux w t 0 = 0) (hL : ∀ t, flux w t L = 0) (t : ℝ) :
    HasDerivAt (energy rA EI L w) 0 t := by
  have cA : ContDiff ℝ 3 (Function.uncurry (dt w)) := contDiff_dt hU (by norm_num)
  have cAt : ContDiff ℝ 2 (Function.uncurry (dt (dt w))) := contDiff_dt cA (by norm_num)
  have c1 : ContDiff ℝ 3 (Function.uncurry (dx w)) := contDiff_dx hU (by norm_num)
  have c2 : ContDiff ℝ 2 (Function.uncurry (dx (dx w))) := contDiff_dx c1 (by norm_num)
  have c3 : ContDiff ℝ 1 (Function.uncurry (dx (dx (dx w)))) := contDiff_dx c2 (by norm_num)
  have c2t : ContDiff ℝ 1 (Function.uncurry (dt (dx (dx w)))) := contDiff_dt c2 (by norm_num)
  have cAx : ContDiff ℝ 2 (Function.uncurry (dx (dt w))) := contDiff_dx cA (by norm_num)
  -- mixed partials: `w_xxt = w_txx`
  have hmix : dt (dx (dx w)) = dx (dx (dt w)) := by
    rw [dt_dx_comm (c1.of_le (by norm_num)), dt_dx_comm (hU.of_le (by norm_num))]
  have kA : Continuous fun p : ℝ × ℝ => dt w p.1 p.2 := cA.continuous
  have kAt : Continuous fun p : ℝ × ℝ => dt (dt w) p.1 p.2 := cAt.continuous
  have k2 : Continuous fun p : ℝ × ℝ => dx (dx w) p.1 p.2 := c2.continuous
  have k2t : Continuous fun p : ℝ × ℝ => dt (dx (dx w)) p.1 p.2 := c2t.continuous
  set Fp : ℝ × ℝ → ℝ := fun p => rA * dt w p.1 p.2 ^ 2 + EI * dx (dx w) p.1 p.2 ^ 2 with hFp
  set Gp : ℝ × ℝ → ℝ := fun p => rA * (2 * dt w p.1 p.2 * dt (dt w) p.1 p.2) +
    EI * (2 * dx (dx w) p.1 p.2 * dt (dx (dx w)) p.1 p.2) with hGp
  have cF : Continuous Fp := (continuous_const.mul (kA.pow 2)).add (continuous_const.mul (k2.pow 2))
  have cG : Continuous Gp := (continuous_const.mul ((continuous_const.mul kA).mul kAt)).add
    (continuous_const.mul ((continuous_const.mul k2).mul k2t))
  have hE : energy rA EI L w = fun s => 1 / 2 * ∫ x in (0 : ℝ)..L, Fp (s, x) := rfl
  have hFd : ∀ s x, HasDerivAt (fun s => Fp (s, x)) (Gp (s, x)) s := by
    intro s x
    have h1 := hasDerivAt_dt (cA.of_le (by norm_num)) s x
    have h2 := hasDerivAt_dt (c2.of_le (by norm_num)) s x
    convert ((h1.pow 2).const_mul rA).add ((h2.pow 2).const_mul EI) using 1
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
  have hflux : ∀ x, HasDerivAt (fun y => 2 * EI * (dx (dx w) t y * dx (dt w) t y -
      dt w t y * dx (dx (dx w)) t y)) (Gp (t, x)) x := by
    intro x
    have g1 := hasDerivAt_dx (c2.of_le (by norm_num)) t x
    have g2 := hasDerivAt_dx (cAx.of_le (by norm_num)) t x
    have g3 := hasDerivAt_dx (cA.of_le (by norm_num)) t x
    have g4 := hasDerivAt_dx c3 t x
    convert ((g1.mul g2).sub (g3.mul g4)).const_mul (2 * EI) using 1
    simp only [Gp, hmix]
    linear_combination (2 * dt w t x) * hw t x
  have e0 := h0 t
  have eL := hL t
  simp only [flux] at e0 eL
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hflux x)
    ((cG.comp (Continuous.prodMk_right t)).intervalIntegrable 0 L)]
  rw [e0, eL]
  ring

/-- **Conservation of energy**: `E(t) = E(t')` for `C⁴` solutions with vanishing end flux. -/
theorem energy_const (hU : ContDiff ℝ 4 (Function.uncurry w)) (hw : IsBeamVib rA EI w)
    (h0 : ∀ t, flux w t 0 = 0) (hL : ∀ t, flux w t L = 0) (t t' : ℝ) :
    energy rA EI L w t = energy rA EI L w t' :=
  is_const_of_deriv_eq_zero (fun s => (hasDerivAt_energy hU hw h0 hL s).differentiableAt)
    (fun s => (hasDerivAt_energy hU hw h0 hL s).deriv) t t'

/-- If `f` vanishes on `[0, L]` (`L > 0`) and `f'` is continuous, then `f'` vanishes on `[0, L]`. -/
theorem deriv_eq_zero_of_eqOn {f : ℝ → ℝ} (hLpos : 0 < L) (hf : Continuous (deriv f))
    (h : ∀ x ∈ Icc 0 L, f x = 0) : ∀ x ∈ Icc 0 L, deriv f x = 0 := by
  have hE : EqOn (deriv f) 0 (Icc 0 L) := by
    refine EqOn.of_subset_closure (s := Ioo 0 L) (fun y hy => ?_) hf.continuousOn
      continuousOn_const Ioo_subset_Icc_self (closure_Ioo hLpos.ne).symm.subset
    have hev : f =ᶠ[nhds y] fun _ => 0 :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hy.1 hy.2) fun z hz => h z (Ioo_subset_Icc_self hz)
    simp only [Pi.zero_apply, hev.deriv_eq, deriv_const]
  exact fun x hx => hE hx

/-- **Zero data give the zero solution**: a `C⁴` solution of the beam equation on `[0, L]` with
vanishing end flux and vanishing initial displacement and velocity vanishes on `[0, L]` for all
time. The energy is conserved and initially zero, so `w_t ≡ 0` on `[0, L]`. -/
theorem eq_zero_of_zero_data (hLpos : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    (hU : ContDiff ℝ 4 (Function.uncurry w)) (hw : IsBeamVib rA EI w)
    (h0 : ∀ t, flux w t 0 = 0) (hL : ∀ t, flux w t L = 0)
    (hi : ∀ x ∈ Icc 0 L, w 0 x = 0) (hi' : ∀ x ∈ Icc 0 L, dt w 0 x = 0) :
    ∀ t, ∀ x ∈ Icc 0 L, w t x = 0 := by
  have cA : ContDiff ℝ 3 (Function.uncurry (dt w)) := contDiff_dt hU (by norm_num)
  have c1 : ContDiff ℝ 3 (Function.uncurry (dx w)) := contDiff_dx hU (by norm_num)
  have c2 : ContDiff ℝ 2 (Function.uncurry (dx (dx w))) := contDiff_dx c1 (by norm_num)
  have cF : ∀ t, Continuous fun y => rA * dt w t y ^ 2 + EI * dx (dx w) t y ^ 2 := fun t =>
    (continuous_const.mul ((cA.continuous.comp (Continuous.prodMk_right t)).pow 2)).add
      (continuous_const.mul ((c2.continuous.comp (Continuous.prodMk_right t)).pow 2))
  -- the initial curvature vanishes on `[0, L]`
  have hx1 : ∀ x ∈ Icc 0 L, dx w 0 x = 0 :=
    deriv_eq_zero_of_eqOn hLpos (c1.continuous.comp (Continuous.prodMk_right 0)) hi
  have hx2 : ∀ x ∈ Icc 0 L, dx (dx w) 0 x = 0 :=
    deriv_eq_zero_of_eqOn hLpos (c2.continuous.comp (Continuous.prodMk_right 0)) hx1
  -- the energy vanishes at all times
  have hE0 : energy rA EI L w 0 = 0 := by
    rw [energy, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
      rw [uIcc_of_le hLpos.le] at hx
      simp only [hi' x hx, hx2 x hx]
      ring)]
    simp
  have hE : ∀ t, ∫ x in (0 : ℝ)..L, (rA * dt w t x ^ 2 + EI * dx (dx w) t x ^ 2) = 0 := by
    intro t
    have h1 := energy_const hU hw h0 hL t 0
    rw [hE0, energy] at h1
    linarith
  -- hence `w_t = 0` on `[0, L]`
  have hF0 : ∀ s, EqOn (fun y => rA * dt w s y ^ 2 + EI * dx (dx w) s y ^ 2) 0 (Icc 0 L) := by
    intro s
    have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => by positivity)
      ((cF s).intervalIntegrable 0 L)).1 (hE s)
    rw [Ioc_eq_empty (not_lt.2 hLpos.le), union_empty,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
    exact Measure.eqOn_Icc_of_ae_eq volume hLpos.ne hae (cF s).continuousOn continuousOn_const
  intro t x hx
  have hAt : ∀ s, dt w s x = 0 := by
    intro s
    have h := hF0 s hx
    simp only [Pi.zero_apply] at h
    have h' : rA * dt w s x ^ 2 = 0 := by
      nlinarith [mul_nonneg hrA.le (sq_nonneg (dt w s x)),
        mul_nonneg hEI (sq_nonneg (dx (dx w) s x))]
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 h').resolve_left hrA.ne')
  have h1 : ContDiff ℝ 1 (Function.uncurry w) := hU.of_le (by norm_num)
  rw [is_const_of_deriv_eq_zero (f := fun s => w s x)
    (fun s => (hasDerivAt_dt h1 s x).differentiableAt) hAt t 0]
  exact hi x hx

end Energy

/-! ### Support conditions and uniqueness of the initial–boundary value problem -/

/-- The classical **support conditions** at an end `x₀` of a beam. -/
inductive EndSupport
  /-- Pinned (simply supported) end: `w = 0` and no bending moment, `w_xx = 0`. -/
  | pinned
  /-- Clamped (built-in) end: `w = 0` and `w_x = 0`. -/
  | clamped
  /-- Free end: no bending moment and no shear force, `w_xx = w_xxx = 0`. -/
  | free

namespace EndSupport

/-- The support condition `k` holds for the field `w` at the end `x₀`, at all times. -/
def Holds : EndSupport → (ℝ → ℝ → ℝ) → ℝ → Prop
  | pinned, w, x₀ => ∀ t, w t x₀ = 0 ∧ dx (dx w) t x₀ = 0
  | clamped, w, x₀ => ∀ t, w t x₀ = 0 ∧ dx w t x₀ = 0
  | free, w, x₀ => ∀ t, dx (dx w) t x₀ = 0 ∧ dx (dx (dx w)) t x₀ = 0

variable {w u v : ℝ → ℝ → ℝ} {x₀ : ℝ}

/-- An end held at zero displacement has zero velocity. -/
theorem dt_eq_zero_of_eq_zero {f : ℝ → ℝ → ℝ} (h : ∀ t, f t x₀ = 0) (t : ℝ) :
    dt f t x₀ = 0 := by
  have : (fun s => f s x₀) = fun _ => 0 := funext h
  simp only [dt, this, deriv_const]

/-- **No power flows through a supported end**: the flux vanishes at a pinned, clamped or free
end (for a clamped end, by symmetry of the mixed partials `w_xt = w_tx = 0`). -/
theorem flux_eq_zero (hU : ContDiff ℝ 2 (Function.uncurry w)) :
    ∀ {k : EndSupport}, k.Holds w x₀ → ∀ t, flux w t x₀ = 0
  | pinned, h, t => by
    simp only [flux, dt_eq_zero_of_eq_zero (fun s => (h s).1) t, (h t).2, zero_mul, sub_zero]
  | clamped, h, t => by
    have hxt : dx (dt w) t x₀ = 0 := by
      rw [← dt_dx_comm hU]
      exact dt_eq_zero_of_eq_zero (fun s => (h s).2) t
    simp only [flux, dt_eq_zero_of_eq_zero (fun s => (h s).1) t, hxt, mul_zero, zero_mul,
      sub_zero]
  | free, h, t => by simp only [flux, (h t).1, (h t).2, zero_mul, mul_zero, sub_zero]

/-- Support conditions are linear: they hold for the difference of two `C⁴` fields satisfying
them. -/
theorem holds_sub (hu : ContDiff ℝ 4 (Function.uncurry u))
    (hv : ContDiff ℝ 4 (Function.uncurry v)) :
    ∀ {k : EndSupport}, k.Holds u x₀ → k.Holds v x₀ → k.Holds (fun t x => u t x - v t x) x₀
  | pinned, h, h' => fun t => by
    rw [(dx_iter_sub hu hv).2.1]
    simp only [(h t).1, (h' t).1, (h t).2, (h' t).2, sub_self, and_self]
  | clamped, h, h' => fun t => by
    rw [(dx_iter_sub hu hv).1]
    simp only [(h t).1, (h' t).1, (h t).2, (h' t).2, sub_self, and_self]
  | free, h, h' => fun t => by
    rw [(dx_iter_sub hu hv).2.2, (dx_iter_sub hu hv).2.1]
    simp only [(h t).1, (h' t).1, (h t).2, (h' t).2, sub_self, and_self]

end EndSupport

section Unique

variable {rA EI L : ℝ} {w u v : ℝ → ℝ → ℝ}

/-- **Conservation of energy** for a beam with classical supports `k₀` at `x = 0` and `k₁` at
`x = L` (simply supported, clamped, cantilever, …). -/
theorem energy_const_of_supports {k₀ k₁ : EndSupport} (hU : ContDiff ℝ 4 (Function.uncurry w))
    (hw : IsBeamVib rA EI w) (h0 : k₀.Holds w 0) (hL : k₁.Holds w L) (t t' : ℝ) :
    energy rA EI L w t = energy rA EI L w t' :=
  energy_const hU hw (EndSupport.flux_eq_zero (hU.of_le (by norm_num)) h0)
    (EndSupport.flux_eq_zero (hU.of_le (by norm_num)) hL) t t'

/-- **Uniqueness for the initial–boundary value problem** of a vibrating beam with classical
supports `k₀` at `x = 0` and `k₁` at `x = L`: two `C⁴` solutions of `ρA w_tt + EI w_xxxx = 0`
satisfying the support conditions, with the same initial displacement and velocity on `[0, L]`,
coincide on `[0, L]` for all time. -/
theorem unique {k₀ k₁ : EndSupport} (hLpos : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    (hu : ContDiff ℝ 4 (Function.uncurry u)) (hv : ContDiff ℝ 4 (Function.uncurry v))
    (hwu : IsBeamVib rA EI u) (hwv : IsBeamVib rA EI v)
    (hu0 : k₀.Holds u 0) (huL : k₁.Holds u L) (hv0 : k₀.Holds v 0) (hvL : k₁.Holds v L)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = dt v 0 x) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = v t x := by
  intro t x hx
  have hd : ContDiff ℝ 4 (Function.uncurry fun t x => u t x - v t x) := hu.sub hv
  have h := eq_zero_of_zero_data hLpos hrA hEI hd (isBeamVib_sub hu hv hwu hwv)
    (EndSupport.flux_eq_zero (hd.of_le (by norm_num)) (EndSupport.holds_sub hu hv hu0 hv0))
    (EndSupport.flux_eq_zero (hd.of_le (by norm_num)) (EndSupport.holds_sub hu hv huL hvL))
    (fun x hx => sub_eq_zero.2 (hi x hx))
    (fun x hx => by
      rw [dt_fun_sub (hu.of_le (by norm_num)) (hv.of_le (by norm_num))]
      exact sub_eq_zero.2 (hi' x hx)) t x hx
  exact sub_eq_zero.1 h

/-- **Uniqueness for the simply supported beam** (`w = w_xx = 0` at both ends). -/
theorem unique_simplySupported (hLpos : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    (hu : ContDiff ℝ 4 (Function.uncurry u)) (hv : ContDiff ℝ 4 (Function.uncurry v))
    (hwu : IsBeamVib rA EI u) (hwv : IsBeamVib rA EI v)
    (hu0 : EndSupport.pinned.Holds u 0) (huL : EndSupport.pinned.Holds u L)
    (hv0 : EndSupport.pinned.Holds v 0) (hvL : EndSupport.pinned.Holds v L)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = dt v 0 x) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = v t x :=
  unique hLpos hrA hEI hu hv hwu hwv hu0 huL hv0 hvL hi hi'

/-- **Uniqueness for the clamped–clamped beam** (`w = w_x = 0` at both ends). -/
theorem unique_clamped (hLpos : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    (hu : ContDiff ℝ 4 (Function.uncurry u)) (hv : ContDiff ℝ 4 (Function.uncurry v))
    (hwu : IsBeamVib rA EI u) (hwv : IsBeamVib rA EI v)
    (hu0 : EndSupport.clamped.Holds u 0) (huL : EndSupport.clamped.Holds u L)
    (hv0 : EndSupport.clamped.Holds v 0) (hvL : EndSupport.clamped.Holds v L)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = dt v 0 x) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = v t x :=
  unique hLpos hrA hEI hu hv hwu hwv hu0 huL hv0 hvL hi hi'

/-- **Uniqueness for the cantilever** (clamped at `x = 0`, free at `x = L`). -/
theorem unique_cantilever (hLpos : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    (hu : ContDiff ℝ 4 (Function.uncurry u)) (hv : ContDiff ℝ 4 (Function.uncurry v))
    (hwu : IsBeamVib rA EI u) (hwv : IsBeamVib rA EI v)
    (hu0 : EndSupport.clamped.Holds u 0) (huL : EndSupport.free.Holds u L)
    (hv0 : EndSupport.clamped.Holds v 0) (hvL : EndSupport.free.Holds v L)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) (hi' : ∀ x ∈ Icc 0 L, dt u 0 x = dt v 0 x) :
    ∀ t, ∀ x ∈ Icc 0 L, u t x = v t x :=
  unique hLpos hrA hEI hu hv hwu hwv hu0 huL hv0 hvL hi hi'

end Unique

/-! ### The cantilever: frequency equation and mode shapes -/

section Cantilever

/-- The combination `p cosh βx + q cos βx + r sinh βx + s sin βx`, closed under `d/dx`. -/
def hypTrig (β p q r s x : ℝ) : ℝ :=
  p * cosh (β * x) + q * cos (β * x) + r * sinh (β * x) + s * sin (β * x)

/-- Derivative of `hypTrig`: `(p, q, r, s) ↦ β (r, s, p, -q)`. -/
theorem hasDerivAt_hypTrig (β p q r s x : ℝ) :
    HasDerivAt (hypTrig β p q r s) (hypTrig β (β * r) (β * s) (β * p) (-(β * q)) x) x := by
  have hl := (hasDerivAt_id' x).const_mul β
  have h := (((hl.cosh.const_mul p).add (hl.cos.const_mul q)).add (hl.sinh.const_mul r)).add
    (hl.sin.const_mul s)
  convert h using 1
  · funext y
    simp only [hypTrig, Pi.add_apply]
  · simp only [hypTrig]
    ring

/-- Derivative of `hypTrig` as a function. -/
theorem deriv_hypTrig (β p q r s : ℝ) :
    deriv (hypTrig β p q r s) = hypTrig β (β * r) (β * s) (β * p) (-(β * q)) :=
  funext fun x => (hasDerivAt_hypTrig β p q r s x).deriv

/-- `hypTrig` is differentiable. -/
theorem differentiable_hypTrig (β p q r s : ℝ) : Differentiable ℝ (hypTrig β p q r s) :=
  fun x => (hasDerivAt_hypTrig β p q r s x).differentiableAt

/-- **Fourth derivative of `hypTrig`**: `(hypTrig)'''' = β⁴ hypTrig`. -/
theorem iteratedDeriv_four_hypTrig (β p q r s x : ℝ) :
    iteratedDeriv 4 (hypTrig β p q r s) x = β ^ 4 * hypTrig β p q r s x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_hypTrig]
  simp only [hypTrig]
  ring

/-- The **cantilever mode shape**
`φ(x) = (cosh βx - cos βx) - σ (sinh βx - sin βx)`. -/
def cantileverShape (β σ : ℝ) : ℝ → ℝ := hypTrig β 1 (-1) (-σ) σ

/-- The ratio `σ = (cosh βL + cos βL) / (sinh βL + sin βL)` of the cantilever mode shape. -/
def sigma (β L : ℝ) : ℝ := (cosh (β * L) + cos (β * L)) / (sinh (β * L) + sin (β * L))

/-- `sinh y + sin y > 0` for `y > 0`. -/
theorem sinh_add_sin_pos {y : ℝ} (hy : 0 < y) : 0 < sinh y + sin y := by
  have h1 : y < sinh y := self_lt_sinh_iff.2 hy
  rcases le_or_gt y π with h | h
  · linarith [sin_nonneg_of_nonneg_of_le_pi hy.le h]
  · linarith [neg_one_le_sin y, two_le_pi]

/-- The choice of `σ` makes the bending moment vanish at the free end:
`(cosh βL + cos βL) - σ (sinh βL + sin βL) = 0`. -/
theorem sigma_moment {β L : ℝ} (hS : sinh (β * L) + sin (β * L) ≠ 0) :
    cosh (β * L) + cos (β * L) - sigma β L * (sinh (β * L) + sin (β * L)) = 0 := by
  rw [sigma, div_mul_cancel₀ _ hS, sub_self]

/-- Under the **cantilever frequency equation** `cos βL cosh βL + 1 = 0`, the shear force also
vanishes at the free end: `(sinh βL - sin βL) - σ (cosh βL + cos βL) = 0`. -/
theorem sigma_shear {β L : ℝ} (hS : sinh (β * L) + sin (β * L) ≠ 0)
    (hfreq : cos (β * L) * cosh (β * L) + 1 = 0) :
    sinh (β * L) - sin (β * L) - sigma β L * (cosh (β * L) + cos (β * L)) = 0 := by
  have key : (cosh (β * L) + cos (β * L)) * (cosh (β * L) + cos (β * L)) =
      (sinh (β * L) - sin (β * L)) * (sinh (β * L) + sin (β * L)) := by
    linear_combination -(sinh_sq (β * L)) + sin_sq_add_cos_sq (β * L) + 2 * hfreq
  rw [sigma, div_mul_eq_mul_div, key, mul_div_cancel_right₀ _ hS, sub_self]

/-- The cantilever mode shape solves the **mode-shape equation** `φ'''' = β⁴ φ`. -/
theorem iteratedDeriv_four_cantileverShape (β σ x : ℝ) :
    iteratedDeriv 4 (cantileverShape β σ) x = β ^ 4 * cantileverShape β σ x :=
  iteratedDeriv_four_hypTrig ..

/-- The cantilever mode shape satisfies the **clamped conditions** `φ(0) = φ'(0) = 0`, and is
nontrivial: `φ''(0) = 2β²`. -/
theorem cantileverShape_clamped (β σ : ℝ) :
    cantileverShape β σ 0 = 0 ∧ iteratedDeriv 1 (cantileverShape β σ) 0 = 0 ∧
      iteratedDeriv 2 (cantileverShape β σ) 0 = 2 * β ^ 2 := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, cantileverShape, deriv_hypTrig]
  simp only [hypTrig, mul_zero, cosh_zero, cos_zero, sinh_zero, sin_zero]
  refine ⟨by ring, by ring, by ring⟩

/-- **The cantilever mode shape satisfies the free-end conditions** `φ''(L) = φ'''(L) = 0`
(no bending moment, no shear force) when `σ = σ(β, L)` and `β` solves the **frequency equation**
`cos βL cosh βL = -1` (`βL > 0`). -/
theorem cantileverShape_free {β L : ℝ} (hβL : 0 < β * L)
    (hfreq : cos (β * L) * cosh (β * L) + 1 = 0) :
    iteratedDeriv 2 (cantileverShape β (sigma β L)) L = 0 ∧
      iteratedDeriv 3 (cantileverShape β (sigma β L)) L = 0 := by
  have hS := (sinh_add_sin_pos hβL).ne'
  have hM := sigma_moment hS
  have hV := sigma_shear hS hfreq
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, cantileverShape, deriv_hypTrig]
  simp only [hypTrig]
  exact ⟨by linear_combination β ^ 2 * hM, by linear_combination β ^ 3 * hV⟩

/-- **The cantilever frequency equation has a root in `(π/2, π)`**: there is `y ∈ (π/2, π)`
with `cos y cosh y + 1 = 0` (by the intermediate value theorem; numerically `y ≈ 1.8751`). -/
theorem exists_root_frequency_equation :
    ∃ y ∈ Ioo (π / 2) π, cos y * cosh y + 1 = 0 := by
  have hc : ContinuousOn (fun y => cos y * cosh y + 1) (Icc (π / 2) π) := by fun_prop
  have h1 : (fun y => cos y * cosh y + 1) (π / 2) = 1 := by simp
  have h2 : (fun y => cos y * cosh y + 1) π < 0 := by
    have := one_lt_cosh.2 pi_ne_zero
    simp only [cos_pi]
    linarith
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' (by linarith [pi_pos]) hc
    (show (0 : ℝ) ∈ Ioo _ _ from ⟨h2, by norm_num⟩)
  exact ⟨y, hy, hy0⟩

/-- A separated field `X(x) T(t)` with `X = hypTrig` and harmonic `T`. -/
def hsep (β ω p q r s a b t x : ℝ) : ℝ := hypTrig β p q r s x * harm ω a b t

/-- Time derivative of `hsep`. -/
theorem dt_hsep (β ω p q r s a b : ℝ) :
    dt (hsep β ω p q r s a b) = hsep β ω p q r s (ω * b) (-(ω * a)) := by
  funext t x
  simp only [dt, hsep]
  rw [deriv_const_mul _ (differentiable_harm ω a b t), deriv_harm]

/-- Space derivative of `hsep`. -/
theorem dx_hsep (β ω p q r s a b : ℝ) :
    dx (hsep β ω p q r s a b) = hsep β ω (β * r) (β * s) (β * p) (-(β * q)) a b := by
  funext t x
  change deriv (fun y => hypTrig β p q r s y * harm ω a b t) x = _
  rw [deriv_mul_const (differentiable_hypTrig β p q r s x), deriv_hypTrig]
  rfl

/-- `hsep` solves the beam equation when `ρA ω² = EI β⁴`. -/
theorem isBeamVib_hsep {rA EI β ω : ℝ} (hω : rA * ω ^ 2 = EI * β ^ 4) (p q r s a b : ℝ) :
    IsBeamVib rA EI (hsep β ω p q r s a b) := by
  intro t x
  rw [dt_hsep, dt_hsep, dx_hsep, dx_hsep, dx_hsep, dx_hsep]
  simp only [hsep, hypTrig, harm]
  linear_combination (-(p * cosh (β * x) + q * cos (β * x) + r * sinh (β * x) +
    s * sin (β * x)) * (a * cos (ω * t) + b * sin (ω * t))) * hω

/-- The **free vibration of a cantilever** in its mode `φ`:
`w(t, x) = φ(x) (a cos ωt + b sin ωt)`, with `φ = cantileverShape β (σ β L)`. -/
def cantileverMode (β L ω a b : ℝ) : ℝ → ℝ → ℝ :=
  hsep β ω 1 (-1) (-sigma β L) (sigma β L) a b

/-- **Cantilever modes**: if `cos βL cosh βL = -1` (`βL > 0`) and `ω = β² √(EI / ρA)`, then
`w(t, x) = φ(x) (a cos ωt + b sin ωt)` solves `ρA w_tt + EI w_xxxx = 0`, is clamped at `x = 0`
and free at `x = L`. -/
theorem cantileverMode_solves {rA EI β L : ℝ} (hrA : 0 < rA) (hEI : 0 ≤ EI) (hβL : 0 < β * L)
    (hfreq : cos (β * L) * cosh (β * L) + 1 = 0) (a b : ℝ) :
    IsBeamVib rA EI (cantileverMode β L (β ^ 2 * √(EI / rA)) a b) ∧
      EndSupport.clamped.Holds (cantileverMode β L (β ^ 2 * √(EI / rA)) a b) 0 ∧
      EndSupport.free.Holds (cantileverMode β L (β ^ 2 * √(EI / rA)) a b) L := by
  have hω : rA * (β ^ 2 * √(EI / rA)) ^ 2 = EI * β ^ 4 := by
    rw [mul_pow, sq_sqrt (div_nonneg hEI hrA.le)]
    field_simp
  have hS := (sinh_add_sin_pos hβL).ne'
  have hM := sigma_moment hS
  have hV := sigma_shear hS hfreq
  refine ⟨isBeamVib_hsep hω _ _ _ _ _ _, fun t => ?_, fun t => ?_⟩
  · simp only [cantileverMode, dx_hsep]
    simp only [hsep, hypTrig, mul_zero, cosh_zero, cos_zero, sinh_zero, sin_zero]
    constructor <;> ring
  · simp only [cantileverMode, dx_hsep]
    simp only [hsep, hypTrig]
    constructor
    · linear_combination β ^ 2 * harm (β ^ 2 * √(EI / rA)) a b t * hM
    · linear_combination β ^ 3 * harm (β ^ 2 * √(EI / rA)) a b t * hV

end Cantilever

/-! ### Rayleigh's quotient for the simply supported modes -/

/-- `(sin kx)'' = -k² sin kx`. -/
theorem iteratedDeriv_two_sin_mul (k x : ℝ) :
    iteratedDeriv 2 (fun y => sin (k * y)) x = -k ^ 2 * sin (k * x) := by
  have h1 : deriv (fun y => sin (k * y)) = fun y => k * cos (k * y) := funext fun y => by
    have := ((hasDerivAt_id' y).const_mul k).sin
    rw [this.deriv]
    ring
  have h2 : deriv (fun y => k * cos (k * y)) x = -k ^ 2 * sin (k * x) := by
    have := (((hasDerivAt_id' x).const_mul k).cos).const_mul k
    rw [this.deriv]
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2]

/-- **Rayleigh's quotient** for the simply supported beam: the `n`-th mode shape
`φₙ(x) = sin(nπx / L)` realises `ωₙ² = EI ∫₀ᴸ φₙ''² / (ρA ∫₀ᴸ φₙ²)`. -/
theorem beamOmega_sq_eq_rayleigh {L rA EI : ℝ} (hL : 0 < L) (hrA : 0 < rA) (hEI : 0 ≤ EI)
    {n : ℕ} (hn : n ≠ 0) :
    beamOmega L rA EI n ^ 2 =
      EI * (∫ x in (0 : ℝ)..L, iteratedDeriv 2 (fun y => sin (n * π / L * y)) x ^ 2) /
        (rA * ∫ x in (0 : ℝ)..L, sin (n * π / L * x) ^ 2) := by
  have hI : ∫ x in (0 : ℝ)..L, sin (n * π / L * x) ^ 2 = L / 2 := by
    simp_rw [sq]
    rw [integral_sin_mul_sin hL.ne' hn]
    simp
  have e : ∀ x, iteratedDeriv 2 (fun y => sin (n * π / L * y)) x ^ 2 =
      (n * π / L) ^ 4 * sin (n * π / L * x) ^ 2 := fun x => by
    rw [iteratedDeriv_two_sin_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, hI, beamOmega, mul_pow,
    sq_sqrt (div_nonneg hEI hrA.le)]
  have := hL.ne'
  have := hrA.ne'
  field_simp

end ContinuumMechanics.Beams.Vibration
