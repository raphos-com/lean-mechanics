import ClassicalMechanics.ForcedOscillator

/-!
# Duhamel's integral and the response of a single-degree-of-freedom structure

A single-degree-of-freedom (SDOF) structure of mass `m > 0`, viscous damping `c ≥ 0` and
stiffness `k > 0` under an arbitrary continuous load `F(t)` obeys

`m ẍ + c ẋ + k x = F(t)`.

We assume underdamping `c² < 4mk`, i.e. `ζ = c/(2√(km)) < 1` (`SDOF.ζ_lt_one`), and write
`ω = √(k/m)`, `ω_d = ω√(1 - ζ²)` ([Chopra2017], §§4.1–4.2, 6.6; [Clough1993], §§6-1–6-4).

* **Unit impulse response** (`SDOF.h`): `h(t) = e^{-ζωt} sin(ω_d t)/(m ω_d)` solves the free
  equation (`SDOF.h_solves`) with `h(0) = 0`, `ḣ(0) = 1/m` (`SDOF.h_zero`, `SDOF.hV_zero`).
* **Duhamel's integral** (`SDOF.x`): `x(t) = ∫₀ᵗ F(τ) h(t - τ) dτ` is differentiable with
  `ẋ(t) = ∫₀ᵗ F(τ) ḣ(t - τ) dτ` and `ẍ(t) = F(t)/m + ∫₀ᵗ F(τ) ḧ(t - τ) dτ`
  (`SDOF.hasDerivAt_x`, `SDOF.hasDerivAt_v`), solves the forced equation
  (`SDOF.duhamel_solves`) and starts at rest (`SDOF.x_zero`, `SDOF.v_zero`). The proof
  separates variables, `h(t - τ) = A(t) a(τ) + B(t) b(τ)` (`SDOF.ker_sub`), and uses the
  fundamental theorem of calculus.
* **Uniqueness** (`SDOF.Motion.eq_duhamel`): every motion starting at rest coincides with the
  Duhamel integral for `t ≥ 0` (energy argument on the difference, via `Damped.energy_antitone`).
* **Step load** (`SDOF.x_const_eq_stepResponse`): for `c = 0` the response to a suddenly applied
  constant load `F₀` is `x(t) = (F₀/k)(1 - cos ωt)`; its maximum is twice the static deflection
  (`SDOF.stepResponse_le`, `SDOF.stepResponse_pi_div`): the **dynamic amplification factor** is
  `2` (`SDOF.dynamic_amplification`).
* **Response spectrum**: under a ground acceleration `a_g` (effective load `-m a_g`), the
  relative displacement obeys `|x(t)| ≤ (1/ω_d) ∫₀ᵗ |a_g|` (`SDOF.abs_x_ground_le`); hence the
  spectral displacement `S_d = sup_{[0,T]} |x|` and pseudo-acceleration `S_a = ω² S_d` satisfy
  `S_d ≤ (1/ω_d) ∫₀ᵀ |a_g|` and `S_a ≤ (ω²/ω_d) ∫₀ᵀ |a_g|` (`SDOF.Sd_le`, `SDOF.Sa_le`).

## References

* [Chopra2017] A. K. Chopra, *Dynamics of Structures*, 5th ed., Ch. 4, 6.
* [Clough1993] R. W. Clough, J. Penzien, *Dynamics of Structures*, 2nd ed., Ch. 6.
-/

open Real
open scoped Real

noncomputable section

namespace ClassicalMechanics

/-- An **underdamped single-degree-of-freedom structure** `m ẍ + c ẋ + k x = F(t)`. -/
structure SDOF where
  m : ℝ
  c : ℝ
  k : ℝ
  m_pos : 0 < m
  c_nonneg : 0 ≤ c
  k_pos : 0 < k
  underdamped : c ^ 2 < 4 * m * k

namespace SDOF

variable (S : SDOF)

/-- The natural frequency `ω = √(k/m)`. -/
def ω : ℝ := √(S.k / S.m)

/-- The damping ratio `ζ = c/(2√(km))`. -/
def ζ : ℝ := S.c / (2 * √(S.k * S.m))

/-- The decay rate `ζω`. -/
def γ : ℝ := S.ζ * S.ω

/-- The damped frequency `ω_d = ω√(1 - ζ²)`. -/
def ωd : ℝ := S.ω * √(1 - S.ζ ^ 2)

/-- `ω > 0`. -/
theorem ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

/-- `ω² = k/m`. -/
theorem ω_sq : S.ω ^ 2 = S.k / S.m := sq_sqrt (div_pos S.k_pos S.m_pos).le

/-- `ζ² = c²/(4km)`. -/
theorem ζ_sq : S.ζ ^ 2 = S.c ^ 2 / (4 * (S.k * S.m)) := by
  rw [ζ, div_pow, mul_pow, sq_sqrt (mul_pos S.k_pos S.m_pos).le]
  norm_num

/-- `ζ ≥ 0`. -/
theorem ζ_nonneg : 0 ≤ S.ζ := div_nonneg S.c_nonneg (by positivity)

/-- `ζ² < 1`. -/
theorem ζ_sq_lt_one : S.ζ ^ 2 < 1 := by
  rw [ζ_sq, div_lt_one (by have := S.k_pos; have := S.m_pos; positivity)]
  linarith [S.underdamped]

/-- **Underdamping**: `0 ≤ ζ < 1`. -/
theorem ζ_lt_one : S.ζ < 1 := by
  nlinarith [S.ζ_sq_lt_one, S.ζ_nonneg]

/-- `ζω = c/(2m)`. -/
theorem γ_eq : S.γ = S.c / (2 * S.m) := by
  have hk := S.k_pos; have hm := S.m_pos
  rw [γ, ζ, ω, sqrt_mul hk.le, sqrt_div hk.le]
  have h1 : 0 < √S.k := sqrt_pos.mpr hk
  have h2 : 0 < √S.m := sqrt_pos.mpr hm
  have h3 : √S.m ^ 2 = S.m := sq_sqrt hm.le
  rw [show S.c / (2 * (√S.k * √S.m)) * (√S.k / √S.m) = S.c / (2 * (√S.m * √S.m)) by
    field_simp, mul_self_sqrt hm.le]

/-- `ζω ≥ 0`. -/
theorem γ_nonneg : 0 ≤ S.γ := mul_nonneg S.ζ_nonneg S.ω_pos.le

/-- `c = 2mγ`. -/
theorem c_eq : S.c = 2 * S.m * S.γ := by
  rw [γ_eq]; field_simp [S.m_pos.ne']

/-- `ω_d > 0`. -/
theorem ωd_pos : 0 < S.ωd :=
  mul_pos S.ω_pos (sqrt_pos.mpr (by linarith [S.ζ_sq_lt_one]))

/-- `ω_d² = ω² - (ζω)²`. -/
theorem ωd_sq : S.ωd ^ 2 = S.ω ^ 2 - S.γ ^ 2 := by
  rw [ωd, γ, mul_pow, sq_sqrt (by linarith [S.ζ_sq_lt_one])]
  ring

/-- `k = m (γ² + ω_d²)`. -/
theorem k_eq : S.k = S.m * (S.γ ^ 2 + S.ωd ^ 2) := by
  rw [ωd_sq, ω_sq]; field_simp [S.m_pos.ne']; ring

/-! ### Damped kernels and the unit impulse response -/

/-- A **damped kernel** `e^{-γs}(α cos ω_d s + β sin ω_d s)`, a free damped motion. -/
def ker (α β s : ℝ) : ℝ := exp (-S.γ * s) * (α * cos (S.ωd * s) + β * sin (S.ωd * s))

/-- Derivative of a damped kernel: again a damped kernel. -/
theorem hasDerivAt_ker (α β s : ℝ) :
    HasDerivAt (S.ker α β) (S.ker (β * S.ωd - S.γ * α) (-α * S.ωd - S.γ * β) s) s := by
  have hE := ((hasDerivAt_id s).const_mul (-S.γ)).exp
  have hC := ((hasDerivAt_id s).const_mul S.ωd).cos
  have hS := ((hasDerivAt_id s).const_mul S.ωd).sin
  refine (hE.mul ((hC.const_mul α).add (hS.const_mul β))).congr_deriv ?_
  simp only [ker, id, mul_one, Pi.add_apply]
  ring

/-- **Kernel shift identity**: `ker α β (t - τ)` splits into products of functions of `t` with
`e^{γτ} cos ω_d τ` and `e^{γτ} sin ω_d τ`. -/
theorem ker_sub (α β t τ : ℝ) :
    S.ker α β (t - τ) = S.ker α β t * (exp (S.γ * τ) * cos (S.ωd * τ)) +
      S.ker (-β) α t * (exp (S.γ * τ) * sin (S.ωd * τ)) := by
  simp only [ker]
  rw [show -S.γ * (t - τ) = -S.γ * t + S.γ * τ by ring, exp_add,
    show S.ωd * (t - τ) = S.ωd * t - S.ωd * τ by ring, cos_sub, sin_sub]
  ring

/-- The **unit impulse response** `h(t) = e^{-ζωt} sin(ω_d t)/(m ω_d)`. -/
def h (t : ℝ) : ℝ := exp (-S.γ * t) * sin (S.ωd * t) / (S.m * S.ωd)

/-- Velocity of the impulse response. -/
def hV (t : ℝ) : ℝ :=
  exp (-S.γ * t) * (S.ωd * cos (S.ωd * t) - S.γ * sin (S.ωd * t)) / (S.m * S.ωd)

/-- Acceleration of the impulse response. -/
def hA (t : ℝ) : ℝ := exp (-S.γ * t) *
  ((S.γ ^ 2 - S.ωd ^ 2) * sin (S.ωd * t) - 2 * S.γ * S.ωd * cos (S.ωd * t)) / (S.m * S.ωd)

/-- `h` as a damped kernel. -/
theorem h_eq_ker : S.h = S.ker 0 (1 / (S.m * S.ωd)) := by
  funext t; simp only [h, ker]; ring

/-- `ḣ` as a damped kernel. -/
theorem hV_eq_ker : S.hV = S.ker (1 / S.m) (-S.γ / (S.m * S.ωd)) := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  funext t; simp only [hV, ker]; field_simp; ring

/-- `ḧ` as a damped kernel. -/
theorem hA_eq_ker :
    S.hA = S.ker (-2 * S.γ / S.m) ((S.γ ^ 2 - S.ωd ^ 2) / (S.m * S.ωd)) := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  funext t; simp only [hA, ker]; field_simp; ring

/-- `ḣ = hV`. -/
theorem hasDerivAt_h (t : ℝ) : HasDerivAt S.h (S.hV t) t := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [h_eq_ker, hV_eq_ker]
  convert S.hasDerivAt_ker 0 (1 / (S.m * S.ωd)) t using 2 <;> field_simp <;> ring

/-- `ḣV = hA`. -/
theorem hasDerivAt_hV (t : ℝ) : HasDerivAt S.hV (S.hA t) t := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [hV_eq_ker, hA_eq_ker]
  convert S.hasDerivAt_ker (1 / S.m) (-S.γ / (S.m * S.ωd)) t using 2 <;> field_simp <;> ring

/-- `h(0) = 0`. -/
theorem h_zero : S.h 0 = 0 := by simp [h]

/-- `ḣ(0) = 1/m`: a unit impulse imparts the velocity `1/m`. -/
theorem hV_zero : S.hV 0 = 1 / S.m := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  simp only [hV, mul_zero, exp_zero, cos_zero, sin_zero, sub_zero, mul_one, one_mul]
  field_simp

/-- **The impulse response solves the free equation** `m ḧ + c ḣ + k h = 0`. -/
theorem h_solves (t : ℝ) : S.m * S.hA t + S.c * S.hV t + S.k * S.h t = 0 := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [S.c_eq, S.k_eq]
  simp only [h, hV, hA]
  field_simp
  ring

/-! ### Duhamel's integral -/

/-- The **convolution** `∫₀ᵗ F(τ) ker α β (t - τ) dτ` of a load with a damped kernel. -/
def conv (α β : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, F τ * S.ker α β (t - τ)

/-- The moment `∫₀ᵗ e^{γτ} cos(ω_d τ) F(τ) dτ`. -/
def Ic (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, exp (S.γ * τ) * cos (S.ωd * τ) * F τ

/-- The moment `∫₀ᵗ e^{γτ} sin(ω_d τ) F(τ) dτ`. -/
def Is (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, exp (S.γ * τ) * sin (S.ωd * τ) * F τ

variable {S} {F : ℝ → ℝ}

/-- **Separation of variables** in the convolution:
`∫₀ᵗ F(τ) ker(t - τ) dτ = ker α β (t) Ic(t) + ker (-β) α (t) Is(t)`. -/
theorem conv_eq (hF : Continuous F) (α β t : ℝ) :
    S.conv α β F t = S.ker α β t * S.Ic F t + S.ker (-β) α t * S.Is F t := by
  have e : (fun τ => F τ * S.ker α β (t - τ)) = fun τ =>
      S.ker α β t * (exp (S.γ * τ) * cos (S.ωd * τ) * F τ) +
        S.ker (-β) α t * (exp (S.γ * τ) * sin (S.ωd * τ) * F τ) := by
    funext τ; rw [S.ker_sub]; ring
  rw [conv, e, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, Ic, Is]

/-- **Leibniz rule** for the convolution with a damped kernel:
`d/dt ∫₀ᵗ F(τ) ker α β (t - τ) dτ = α F(t) + ∫₀ᵗ F(τ) ker' (t - τ) dτ`. -/
theorem hasDerivAt_conv (hF : Continuous F) {α β α' β' : ℝ}
    (hα : α' = β * S.ωd - S.γ * α) (hβ : β' = -α * S.ωd - S.γ * β) (t : ℝ) :
    HasDerivAt (S.conv α β F) (S.conv α' β' F t + α * F t) t := by
  have hc : S.conv α β F = fun t => S.ker α β t * S.Ic F t + S.ker (-β) α t * S.Is F t :=
    funext (conv_eq hF α β)
  have hIc : HasDerivAt (S.Ic F) (exp (S.γ * t) * cos (S.ωd * t) * F t) t :=
    ((by fun_prop : Continuous fun τ => exp (S.γ * τ) * cos (S.ωd * τ) * F τ
      ).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hIs : HasDerivAt (S.Is F) (exp (S.γ * t) * sin (S.ωd * t) * F t) t :=
    ((by fun_prop : Continuous fun τ => exp (S.γ * τ) * sin (S.ωd * τ) * F τ
      ).integral_hasStrictDerivAt 0 t).hasDerivAt
  rw [hc]
  refine (((S.hasDerivAt_ker α β t).mul hIc).add
    ((S.hasDerivAt_ker (-β) α t).mul hIs)).congr_deriv ?_
  rw [conv_eq hF, hα, hβ]
  have hexp : exp (-S.γ * t) * exp (S.γ * t) = 1 := by rw [← exp_add]; simp
  simp only [ker]
  linear_combination (α * F t * (cos (S.ωd * t) ^ 2 + sin (S.ωd * t) ^ 2)) * hexp +
    α * F t * sin_sq_add_cos_sq (S.ωd * t)

/-- The convolution vanishes at `t = 0`. -/
theorem conv_zero (α β : ℝ) : S.conv α β F 0 = 0 := by simp [conv]

variable (S F)

/-- **Duhamel's integral** `x(t) = ∫₀ᵗ F(τ) h(t - τ) dτ`. -/
def x (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, F τ * S.h (t - τ)

/-- Velocity of the Duhamel response, `ẋ(t) = ∫₀ᵗ F(τ) ḣ(t - τ) dτ`. -/
def v (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, F τ * S.hV (t - τ)

/-- Acceleration of the Duhamel response, `ẍ(t) = F(t)/m + ∫₀ᵗ F(τ) ḧ(t - τ) dτ`. -/
def a (t : ℝ) : ℝ := F t / S.m + ∫ τ in (0 : ℝ)..t, F τ * S.hA (t - τ)

variable {S F}

/-- `x` as a convolution with a damped kernel. -/
theorem x_eq_conv : S.x F = S.conv 0 (1 / (S.m * S.ωd)) F := by
  funext t; simp only [x, conv, h_eq_ker]

/-- `v` as a convolution with a damped kernel. -/
theorem v_eq_conv : S.v F = S.conv (1 / S.m) (-S.γ / (S.m * S.ωd)) F := by
  funext t; simp only [v, conv, hV_eq_ker]

/-- `a` as `F/m` plus a convolution with a damped kernel. -/
theorem a_eq_conv (t : ℝ) : S.a F t =
    F t / S.m + S.conv (-2 * S.γ / S.m) ((S.γ ^ 2 - S.ωd ^ 2) / (S.m * S.ωd)) F t := by
  simp only [a, conv, hA_eq_ker]

/-- `ẋ = v` (Leibniz rule; the boundary term vanishes since `h(0) = 0`). -/
theorem hasDerivAt_x (hF : Continuous F) (t : ℝ) : HasDerivAt (S.x F) (S.v F t) t := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [x_eq_conv, v_eq_conv]
  exact (hasDerivAt_conv (α' := 1 / S.m) (β' := -S.γ / (S.m * S.ωd)) hF
    (by field_simp; ring) (by ring) t).congr_deriv (by ring)

/-- `v̇ = a` (Leibniz rule; the boundary term is `F(t) ḣ(0) = F(t)/m`). -/
theorem hasDerivAt_v (hF : Continuous F) (t : ℝ) : HasDerivAt (S.v F) (S.a F t) t := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [v_eq_conv]
  refine (hasDerivAt_conv (α' := -2 * S.γ / S.m) (β' := (S.γ ^ 2 - S.ωd ^ 2) / (S.m * S.ωd))
    hF (by field_simp; ring) (by field_simp; ring) t).congr_deriv ?_
  rw [a_eq_conv]; ring

/-- `x(0) = 0`. -/
theorem x_zero : S.x F 0 = 0 := by simp [x]

/-- `ẋ(0) = 0`. -/
theorem v_zero : S.v F 0 = 0 := by simp [v]

/-- **Duhamel's integral solves the forced equation** `m ẍ + c ẋ + k x = F(t)`. -/
theorem duhamel_solves (hF : Continuous F) (t : ℝ) :
    S.m * S.a F t + S.c * S.v F t + S.k * S.x F t = F t := by
  have := S.ωd_pos.ne'; have := S.m_pos.ne'
  rw [a_eq_conv, v_eq_conv, x_eq_conv, conv_eq hF, conv_eq hF, conv_eq hF, S.c_eq, S.k_eq]
  simp only [ker]
  field_simp
  ring

/-! ### Uniqueness: Duhamel's integral is *the* response from rest -/

variable (S F)

/-- A **motion** of the structure under the load `F`: `m ẍ + c ẋ + k x = F(t)`. -/
structure Motion where
  x : ℝ → ℝ
  v : ℝ → ℝ
  a : ℝ → ℝ
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  eq : ∀ t, S.m * a t + S.c * v t + S.k * x t = F t

variable {S F}

/-- **Linearity**: the difference of two motions under the same load is a free damped
motion. -/
def Motion.sub (M N : S.Motion F) : Damped where
  m := S.m
  c := S.c
  k := S.k
  m_pos := S.m_pos
  c_nonneg := S.c_nonneg
  k_pos := S.k_pos
  x t := M.x t - N.x t
  v t := M.v t - N.v t
  a t := M.a t - N.a t
  hasDerivAt_x t := (M.hasDerivAt_x t).sub (N.hasDerivAt_x t)
  hasDerivAt_v t := (M.hasDerivAt_v t).sub (N.hasDerivAt_v t)
  eq t := by linear_combination M.eq t - N.eq t

/-- **Forward uniqueness**: two motions under the same load with the same initial data agree
for `t ≥ 0` (the energy of their difference is non-increasing and vanishes at `t = 0`). -/
theorem Motion.eq_of_initial (M N : S.Motion F) (hx : M.x 0 = N.x 0) (hv : M.v 0 = N.v 0)
    {t : ℝ} (ht : 0 ≤ t) : M.x t = N.x t := by
  have hE := (M.sub N).energy_antitone ht
  have h0 : (M.sub N).energy 0 = 0 := by simp [Damped.energy, Motion.sub, hx, hv]
  rw [h0] at hE
  have hk := S.k_pos; have hm := S.m_pos
  have hE' : S.m / 2 * (M.v t - N.v t) ^ 2 + S.k / 2 * (M.x t - N.x t) ^ 2 ≤ 0 := hE
  have h1 : (M.x t - N.x t) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (M.v t - N.v t), sq_nonneg (M.x t - N.x t)]
  have h2 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  linarith

/-- The **Duhamel motion** under a continuous load. -/
def duhamelMotion (hF : Continuous F) : S.Motion F where
  x := S.x F
  v := S.v F
  a := S.a F
  hasDerivAt_x := hasDerivAt_x hF
  hasDerivAt_v := hasDerivAt_v hF
  eq := duhamel_solves hF

/-- **Duhamel's principle**: every motion starting at rest from equilibrium is given, for
`t ≥ 0`, by Duhamel's integral `x(t) = ∫₀ᵗ F(τ) h(t - τ) dτ`. -/
theorem Motion.eq_duhamel (hF : Continuous F) (M : S.Motion F) (hx : M.x 0 = 0)
    (hv : M.v 0 = 0) {t : ℝ} (ht : 0 ≤ t) : M.x t = S.x F t :=
  M.eq_of_initial (duhamelMotion hF) (by rw [hx]; exact x_zero.symm)
    (by rw [hv]; exact v_zero.symm) ht

/-! ### Step load on the undamped structure -/

variable (S) in
/-- The **step response** `x(t) = (F₀/k)(1 - cos ωt)` of the undamped structure. -/
def stepResponse (F₀ t : ℝ) : ℝ := F₀ / S.k * (1 - cos (S.ω * t))

/-- **Step load**: for `c = 0`, Duhamel's integral of the constant load `F₀` is
`(F₀/k)(1 - cos ωt)` for `t ≥ 0`. -/
theorem x_const_eq_stepResponse (hc : S.c = 0) (F₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    S.x (fun _ => F₀) t = S.stepResponse F₀ t := by
  have hω := S.ω_sq; have := S.m_pos.ne'; have := S.k_pos.ne'
  let M : S.Motion (fun _ => F₀) :=
    { x := S.stepResponse F₀
      v := fun t => F₀ / S.k * (S.ω * sin (S.ω * t))
      a := fun t => F₀ / S.k * (S.ω ^ 2 * cos (S.ω * t))
      hasDerivAt_x := fun t => by
        have h := (((hasDerivAt_id t).const_mul S.ω).cos.const_sub 1).const_mul (F₀ / S.k)
        refine h.congr_deriv ?_
        simp only [id, mul_one]; ring
      hasDerivAt_v := fun t => by
        have h := (((hasDerivAt_id t).const_mul S.ω).sin.const_mul S.ω).const_mul (F₀ / S.k)
        refine h.congr_deriv ?_
        simp only [id, mul_one]; ring
      eq := fun t => by
        simp only [stepResponse, hc, hω]
        field_simp
        ring }
  exact (M.eq_duhamel continuous_const (by simp [M, stepResponse])
    (by simp [M]) ht).symm

/-- The step response never exceeds twice the static deflection `F₀/k` (for `F₀ ≥ 0`). -/
theorem stepResponse_le {F₀ : ℝ} (hF : 0 ≤ F₀) (t : ℝ) :
    S.stepResponse F₀ t ≤ 2 * (F₀ / S.k) := by
  have : 0 ≤ F₀ / S.k := div_nonneg hF S.k_pos.le
  rw [stepResponse, mul_comm 2]
  exact mul_le_mul_of_nonneg_left (by linarith [neg_one_le_cos (S.ω * t)]) this

/-- The step response reaches twice the static deflection at `t = π/ω`. -/
theorem stepResponse_pi_div (F₀ : ℝ) : S.stepResponse F₀ (π / S.ω) = 2 * (F₀ / S.k) := by
  rw [stepResponse, mul_div_cancel₀ _ S.ω_pos.ne', cos_pi]
  ring

/-- **Dynamic amplification factor of a step load**: `max x / x_static = 2`. -/
theorem dynamic_amplification {F₀ : ℝ} (hF : 0 < F₀) :
    sSup (Set.range (S.stepResponse F₀)) / (F₀ / S.k) = 2 := by
  have hG : IsGreatest (Set.range (S.stepResponse F₀)) (2 * (F₀ / S.k)) :=
    ⟨⟨_, S.stepResponse_pi_div F₀⟩, by rintro _ ⟨t, rfl⟩; exact S.stepResponse_le hF.le t⟩
  rw [hG.csSup_eq, mul_div_assoc, div_self (div_pos hF S.k_pos).ne', mul_one]

/-! ### Earthquake response spectrum -/

/-- `h` is continuous. -/
theorem continuous_h : Continuous S.h :=
  continuous_iff_continuousAt.2 fun t => (S.hasDerivAt_h t).continuousAt

/-- `|h(s)| ≤ 1/(m ω_d)` for `s ≥ 0`. -/
theorem abs_h_le {s : ℝ} (hs : 0 ≤ s) : |S.h s| ≤ 1 / (S.m * S.ωd) := by
  have hmω : 0 < S.m * S.ωd := mul_pos S.m_pos S.ωd_pos
  rw [h, abs_div, abs_mul, abs_of_pos hmω, abs_of_pos (exp_pos _)]
  gcongr
  have he : exp (-S.γ * s) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [S.γ_nonneg])
  calc exp (-S.γ * s) * |sin (S.ωd * s)| ≤ 1 * 1 :=
        mul_le_mul he (abs_sin_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Duhamel bound for ground motion**: the relative displacement under the ground
acceleration `a_g` (effective load `-m a_g`) satisfies `|x(t)| ≤ (1/ω_d) ∫₀ᵗ |a_g|`. -/
theorem abs_x_ground_le {ag : ℝ → ℝ} (hag : Continuous ag) {t : ℝ} (ht : 0 ≤ t) :
    |S.x (fun τ => -S.m * ag τ) t| ≤ 1 / S.ωd * ∫ τ in (0 : ℝ)..t, |ag τ| := by
  have hh := S.continuous_h
  have := S.m_pos.ne'; have := S.ωd_pos.ne'
  rw [x, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine intervalIntegral.integral_mono_on ht (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun τ hτ => ?_
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos S.m_pos]
  calc S.m * |ag τ| * |S.h (t - τ)| ≤ S.m * |ag τ| * (1 / (S.m * S.ωd)) :=
        mul_le_mul_of_nonneg_left (S.abs_h_le (sub_nonneg.mpr hτ.2))
          (mul_nonneg S.m_pos.le (abs_nonneg _))
    _ = 1 / S.ωd * |ag τ| := by field_simp

variable (S) in
/-- The **spectral displacement** `S_d = sup_{t ∈ [0, T]} |x(t)|` for the ground acceleration
`a_g` on `[0, T]`. -/
def Sd (ag : ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup ((fun t => |S.x (fun τ => -S.m * ag τ) t|) '' Set.Icc 0 T)

variable (S) in
/-- The **pseudo-acceleration** `S_a = ω² S_d`. -/
def Sa (ag : ℝ → ℝ) (T : ℝ) : ℝ := S.ω ^ 2 * S.Sd ag T

/-- **Bound on the spectral displacement**: `S_d ≤ (1/ω_d) ∫₀ᵀ |a_g|`. -/
theorem Sd_le {ag : ℝ → ℝ} (hag : Continuous ag) {T : ℝ} (hT : 0 ≤ T) :
    S.Sd ag T ≤ 1 / S.ωd * ∫ τ in (0 : ℝ)..T, |ag τ| := by
  refine csSup_le ((Set.nonempty_Icc.mpr hT).image _) ?_
  rintro _ ⟨t, ht, rfl⟩
  refine (S.abs_x_ground_le hag ht.1).trans
    (mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr S.ωd_pos).le)
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- **Bound on the pseudo-acceleration**: `S_a ≤ (ω²/ω_d) ∫₀ᵀ |a_g|`. -/
theorem Sa_le {ag : ℝ → ℝ} (hag : Continuous ag) {T : ℝ} (hT : 0 ≤ T) :
    S.Sa ag T ≤ S.ω ^ 2 / S.ωd * ∫ τ in (0 : ℝ)..T, |ag τ| := by
  rw [Sa, div_eq_mul_one_div, mul_assoc]
  exact mul_le_mul_of_nonneg_left (S.Sd_le hag hT) (sq_nonneg _)

end SDOF

end ClassicalMechanics
