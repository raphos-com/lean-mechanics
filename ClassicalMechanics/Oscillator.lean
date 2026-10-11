import ClassicalMechanics.Vector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Harmonic and damped oscillators

A mass `m > 0` on a spring of stiffness `k > 0` with viscous damping `c ≥ 0` obeys

`m ẍ + c ẋ + k x = 0`

([Goldstein2002], §§6.1–6.2; [Arnold1989], §5).

* **Energy** `E = ½ m ẋ² + ½ k x²`: conserved without damping (`Harmonic.energy_const`),
  dissipated at the rate `Ė = -c ẋ²` with damping, hence non-increasing (`Damped.energy_antitone`).
* **Harmonic oscillator** (`c = 0`, `ω = √(k/m)`): `x(t) = x₀ cos ωt + (v₀/ω) sin ωt` is a solution
  (`Harmonic.sol_solves`), and **every** motion is of this form (`Harmonic.eq_sol`, uniqueness by
  the energy argument); hence motions are periodic with period `2π/ω` (`Harmonic.periodic`).
* **Underdamped oscillator** (`c² < 4 m k`): `x(t) = e^{-γt} cos(ω_d t)` with `γ = c/(2m)`,
  `ω_d = √(k/m - γ²)` is a solution (`underdamped_solves`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §6.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §5.
-/

open Real
open scoped Real

noncomputable section

namespace ClassicalMechanics

/-- A **damped oscillator** `m ẍ + c ẋ + k x = 0`. -/
structure Damped where
  m : ℝ
  c : ℝ
  k : ℝ
  m_pos : 0 < m
  c_nonneg : 0 ≤ c
  k_pos : 0 < k
  x : ℝ → ℝ
  v : ℝ → ℝ
  a : ℝ → ℝ
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  eq : ∀ t, m * a t + c * v t + k * x t = 0

namespace Damped

variable (D : Damped)

/-- Mechanical energy `½ m ẋ² + ½ k x²`. -/
def energy (t : ℝ) : ℝ := D.m / 2 * D.v t ^ 2 + D.k / 2 * D.x t ^ 2

/-- `Ė = -c ẋ²`. -/
theorem hasDerivAt_energy (t : ℝ) : HasDerivAt D.energy (-D.c * D.v t ^ 2) t := by
  have h := (((D.hasDerivAt_v t).pow 2).const_mul (D.m / 2)).add
    (((D.hasDerivAt_x t).pow 2).const_mul (D.k / 2))
  convert h using 1
  · rfl
  have e := D.eq t
  simp only [Nat.cast_ofNat]
  linear_combination (-(D.v t)) * e

/-- **Energy dissipation**: the energy is non-increasing. -/
theorem energy_antitone : Antitone D.energy :=
  antitone_of_deriv_nonpos (fun t => (D.hasDerivAt_energy t).differentiableAt) fun t => by
    rw [(D.hasDerivAt_energy t).deriv]
    have := D.c_nonneg
    nlinarith [sq_nonneg (D.v t)]

end Damped

/-- A **harmonic oscillator**: a damped oscillator without damping. -/
structure Harmonic extends Damped where
  c_eq : c = 0

namespace Harmonic

variable (H : Harmonic)

/-- The angular frequency `ω = √(k/m)`. -/
def ω : ℝ := √(H.k / H.m)

theorem ω_pos : 0 < H.ω := sqrt_pos.mpr (div_pos H.k_pos H.m_pos)

theorem ω_sq : H.ω ^ 2 = H.k / H.m := sq_sqrt (div_pos H.k_pos H.m_pos).le

/-- **Conservation of energy**. -/
theorem energy_const (s t : ℝ) : H.energy s = H.energy t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := H.hasDerivAt_energy t
  rwa [H.c_eq, neg_zero, zero_mul] at h

/-- The candidate solution `x₀ cos ωt + (v₀/ω) sin ωt`. -/
def sol (x₀ v₀ : ℝ) (t : ℝ) : ℝ := x₀ * cos (H.ω * t) + v₀ / H.ω * sin (H.ω * t)

/-- Its velocity. -/
def solV (x₀ v₀ : ℝ) (t : ℝ) : ℝ := -x₀ * H.ω * sin (H.ω * t) + v₀ * cos (H.ω * t)

theorem hasDerivAt_sol (x₀ v₀ t : ℝ) : HasDerivAt (H.sol x₀ v₀) (H.solV x₀ v₀ t) t := by
  have hω := H.ω_pos.ne'
  have h1 := ((hasDerivAt_id t).const_mul H.ω).cos.const_mul x₀
  have h2 := ((hasDerivAt_id t).const_mul H.ω).sin.const_mul (v₀ / H.ω)
  convert h1.add h2 using 1
  · funext y; rfl
  simp only [solV, id, mul_one]
  field_simp

theorem hasDerivAt_solV (x₀ v₀ t : ℝ) :
    HasDerivAt (H.solV x₀ v₀) (-H.ω ^ 2 * H.sol x₀ v₀ t) t := by
  have hω := H.ω_pos.ne'
  have h1 := ((hasDerivAt_id t).const_mul H.ω).sin.const_mul (-x₀ * H.ω)
  have h2 := ((hasDerivAt_id t).const_mul H.ω).cos.const_mul v₀
  convert h1.add h2 using 1
  · funext y; simp only [solV, Pi.add_apply, id]
  simp only [sol, id, mul_one]
  field_simp
  ring

/-- `x₀ cos ωt + (v₀/ω) sin ωt` solves `m ẍ + k x = 0` with `x(0) = x₀`, `ẋ(0) = v₀`. -/
theorem sol_solves (x₀ v₀ t : ℝ) :
    H.m * (-H.ω ^ 2 * H.sol x₀ v₀ t) + H.k * H.sol x₀ v₀ t = 0 ∧
      H.sol x₀ v₀ 0 = x₀ ∧ H.solV x₀ v₀ 0 = v₀ := by
  refine ⟨?_, by simp [sol], by simp [solV]⟩
  rw [H.ω_sq]
  field_simp [H.m_pos.ne']
  ring

/-- **Uniqueness**: every motion of the harmonic oscillator is
`x(t) = x(0) cos ωt + (ẋ(0)/ω) sin ωt`. -/
theorem eq_sol (t : ℝ) : H.x t = H.sol (H.x 0) (H.v 0) t := by
  set x₀ := H.x 0
  set v₀ := H.v 0
  -- the difference `e = x - sol` has zero energy
  let e := fun s => H.x s - H.sol x₀ v₀ s
  let ev := fun s => H.v s - H.solV x₀ v₀ s
  have he : ∀ s, HasDerivAt e (ev s) s := fun s =>
    (H.hasDerivAt_x s).sub (H.hasDerivAt_sol x₀ v₀ s)
  have hev : ∀ s, HasDerivAt ev (H.a s - -H.ω ^ 2 * H.sol x₀ v₀ s) s := fun s =>
    (H.hasDerivAt_v s).sub (H.hasDerivAt_solV x₀ v₀ s)
  let En := fun s => H.m / 2 * ev s ^ 2 + H.k / 2 * e s ^ 2
  have hE : ∀ s, HasDerivAt En 0 s := fun s => by
    have h := (((hev s).pow 2).const_mul (H.m / 2)).add (((he s).pow 2).const_mul (H.k / 2))
    convert h using 1
    have eqs := H.eq s
    rw [H.c_eq, zero_mul, add_zero] at eqs
    have hω := H.ω_sq
    have hm := H.m_pos.ne'
    simp only [Nat.cast_ofNat, ev, e]
    rw [hω]
    field_simp
    linear_combination (-(H.v s - H.solV x₀ v₀ s)) * eqs
  have h0 : En t = En 0 := eq_of_hasDerivAt_zero hE t 0
  have hE0 : En 0 = 0 := by simp [En, ev, e, x₀, v₀, sol, solV]
  rw [hE0] at h0
  have hk := H.k_pos; have hm := H.m_pos
  have : e t ^ 2 = 0 := by
    have h1 : 0 ≤ H.m / 2 * ev t ^ 2 := by positivity
    have h2 : 0 ≤ H.k / 2 * e t ^ 2 := by positivity
    have : H.k / 2 * e t ^ 2 = 0 := by simp only [En] at h0; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- Motions are **periodic** with period `2π/ω`. -/
theorem periodic (t : ℝ) : H.x (t + 2 * π / H.ω) = H.x t := by
  have hω := H.ω_pos.ne'
  rw [H.eq_sol, H.eq_sol t, sol, sol,
    show H.ω * (t + 2 * π / H.ω) = H.ω * t + 2 * π by field_simp, cos_add_two_pi, sin_add_two_pi]

end Harmonic

/-- **Underdamped motion**: for `c² < 4mk`, `x(t) = e^{-γt} cos(ω_d t)` with `γ = c/(2m)` and
`ω_d = √(k/m - γ²)` solves `m ẍ + c ẋ + k x = 0`. -/
theorem underdamped_solves {m c k : ℝ} (hm : 0 < m) (hu : c ^ 2 < 4 * m * k) (t : ℝ) :
    let γ := c / (2 * m)
    let ωd := √(k / m - γ ^ 2)
    let x := fun t => exp (-γ * t) * cos (ωd * t)
    let v := fun t => exp (-γ * t) * (-γ * cos (ωd * t) - ωd * sin (ωd * t))
    HasDerivAt x (v t) t ∧
      HasDerivAt v (exp (-γ * t) * ((γ ^ 2 - ωd ^ 2) * cos (ωd * t) +
        2 * γ * ωd * sin (ωd * t))) t ∧
      m * (exp (-γ * t) * ((γ ^ 2 - ωd ^ 2) * cos (ωd * t) + 2 * γ * ωd * sin (ωd * t))) +
        c * v t + k * x t = 0 := by
  intro γ ωd x v
  have hpos : 0 ≤ k / m - γ ^ 2 := by
    simp only [γ]
    rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hm]
    nlinarith
  have hω2 : ωd ^ 2 = k / m - γ ^ 2 := sq_sqrt hpos
  have hE := ((hasDerivAt_id t).const_mul (-γ)).exp
  have hC := ((hasDerivAt_id t).const_mul ωd).cos
  have hS := ((hasDerivAt_id t).const_mul ωd).sin
  refine ⟨?_, ?_, ?_⟩
  · convert hE.mul hC using 1
    · funext y; simp only [x, Pi.mul_apply, neg_mul, id]
    simp only [v, id, mul_one]
    ring
  · convert hE.mul ((hC.const_mul (-γ)).sub (hS.const_mul ωd)) using 1
    · funext y; simp only [v, Pi.mul_apply, Pi.sub_apply, neg_mul, id]
    simp only [id, mul_one, Pi.sub_apply]
    ring
  · simp only [x, v]
    have hm' := hm.ne'
    have hγ : c = 2 * m * γ := by simp only [γ]; field_simp
    rw [hγ]
    have : k = m * (ωd ^ 2 + γ ^ 2) := by rw [hω2]; field_simp; ring
    rw [this]
    ring

end ClassicalMechanics
