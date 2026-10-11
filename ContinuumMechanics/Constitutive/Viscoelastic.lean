import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-dimensional linear viscoelasticity

Rheological models relating the stress `σ(t)` and the strain `ε(t)` of a one-dimensional
specimen, built from a spring of modulus `E > 0` and a dashpot of viscosity `η > 0`, with
relaxation time `τ = η / E` ([Findley1976], ch. 5; [Christensen1982], §1.1; [Lakes2009], ch. 2).

* **Kelvin–Voigt** (spring and dashpot in parallel): `σ = E ε + η ε̇`.
* **Maxwell** (spring and dashpot in series): `ε̇ = σ̇ / E + σ / η`.
* **Standard linear solid** (Zener; a spring `E∞` in parallel with a Maxwell element `E₁, η₁`):
  `σ + τ₁ σ̇ = E∞ ε + (E∞ + E₁) τ₁ ε̇` with `τ₁ = η₁ / E₁`.

## Main results

* `eq_mul_exp_of_hasDerivAt`: uniqueness for the linear ODE `u̇ = -u / τ` on `t ≥ 0`:
  `u(t) = u(0) e^{-t/τ}` (via `d/dt (e^{t/τ} u) = 0`).
* `Params.kv_creep_solves`, `Params.kv_creep_unique`: under constant stress `σ₀` with `ε(0) = 0`,
  the Kelvin–Voigt strain is `ε(t) = σ₀ J(t)` with creep compliance `J(t) = (1 - e^{-t/τ}) / E`;
  `Params.kv_creep_tendsto`: `ε(t) → σ₀ / E` as `t → ∞`.
* `Params.maxwell_relax_solves`, `Params.maxwell_relax_unique`: under constant strain `ε₀` with
  `σ(0) = E ε₀`, the Maxwell stress is `σ(t) = ε₀ G(t)` with relaxation modulus
  `G(t) = E e^{-t/τ}`; `Params.maxwell_relax_tendsto`: `σ(t) → 0`.
* `Params.maxwell_creep_unique`, `Params.maxwell_creep_tendsto_atTop`: under constant stress the
  Maxwell strain is `σ₀ / E + σ₀ t / η`, which grows without bound (viscous flow).
* `Zener.relax_unique`, `Zener.relax_tendsto`: the standard linear solid relaxes from
  `(E∞ + E₁) ε₀` to `E∞ ε₀`.
* `Params.kv_hasDerivAt_energy`, `Params.kv_energy_rate_le`: for Kelvin–Voigt,
  `d/dt (½ E ε²) = σ ε̇ - η ε̇² ≤ σ ε̇`.
* `Params.maxwell_hasDerivAt_energy`: for Maxwell, `d/dt (σ² / (2E)) = σ ε̇ - σ² / η`.
* `Params.kv_harmonic_stress`, `Params.kv_harmonic_stress_eq_amplitude_phase`: for
  `ε = ε₀ cos ωt`, `σ = E ε₀ cos ωt - η ω ε₀ sin ωt = |E*| ε₀ cos (ωt + δ)` with
  `|E*| = √(E² + η² ω²)`, `tan δ = η ω / E` (`Params.kv_tan_lossAngle`).
* `Params.kv_dissipation_per_cycle`: the work per cycle is `∫₀^{2π/ω} σ ε̇ dt = π η ω ε₀²`.

## References

* [Findley1976] W. N. Findley, J. S. Lai, K. Onaran, *Creep and Relaxation of Nonlinear
  Viscoelastic Materials*, ch. 5.
* [Christensen1982] R. M. Christensen, *Theory of Viscoelasticity*, 2nd ed., §1.1.
* [Lakes2009] R. Lakes, *Viscoelastic Materials*, ch. 2–3.
-/

open Real Filter Set
open scoped Topology

noncomputable section

namespace ContinuumMechanics

namespace Viscoelastic

/-- **Uniqueness for exponential decay**: if `u̇ = -u / τ` for `t ≥ 0`, then
`u(t) = u(0) e^{-t/τ}` for `t ≥ 0`. The proof shows that `e^{t/τ} u(t)` is constant. -/
theorem eq_mul_exp_of_hasDerivAt {τ : ℝ} (hτ : τ ≠ 0) {u u' : ℝ → ℝ}
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (u' t) t) (h : ∀ t, 0 ≤ t → u' t = -u t / τ)
    {t : ℝ} (ht : 0 ≤ t) : u t = u 0 * exp (-t / τ) := by
  set g : ℝ → ℝ := fun s => exp (s / τ) * u s with hg
  have hgd : ∀ s, 0 ≤ s → HasDerivAt g 0 s := by
    intro s hs
    have h1 : HasDerivAt (fun s => exp (s / τ)) (exp (s / τ) * (1 / τ)) s :=
      ((hasDerivAt_id s).div_const τ).exp
    convert h1.mul (hu s hs) using 1
    rw [h s hs]
    field_simp
    ring
  have hc := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := t)
    (fun s hs => (hgd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [hg, zero_div, exp_zero, one_mul] at hc
  have he : exp (-t / τ) * exp (t / τ) = 1 := by
    rw [← exp_add, neg_div, neg_add_cancel, exp_zero]
  calc u t = exp (-t / τ) * exp (t / τ) * u t := by rw [he, one_mul]
    _ = u 0 * exp (-t / τ) := by rw [mul_assoc, hc, mul_comm]

/-- `e^{-t/τ} → 0` as `t → ∞`, for `τ > 0`. -/
theorem tendsto_exp_neg_div {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun t => exp (-t / τ)) atTop (𝓝 0) := by
  simp_rw [neg_div]
  exact tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const hτ)

/-- The material parameters of a spring–dashpot model: modulus `E > 0`, viscosity `η > 0`. -/
structure Params where
  /-- The elastic modulus. -/
  E : ℝ
  /-- The viscosity. -/
  η : ℝ
  E_pos : 0 < E
  η_pos : 0 < η

namespace Params

variable (P : Params)

/-- The relaxation (retardation) time `τ = η / E`. -/
def τ : ℝ := P.η / P.E

theorem τ_pos : 0 < P.τ := div_pos P.η_pos P.E_pos

/-- `E τ = η`. -/
theorem E_mul_τ : P.E * P.τ = P.η := by
  rw [τ]; field_simp [P.E_pos.ne']

/-! ### Kelvin–Voigt model -/

/-- The Kelvin–Voigt law `σ = E ε + η ε̇`. -/
def KelvinVoigt (σ ε ε' : ℝ) : Prop := σ = P.E * ε + P.η * ε'

/-- The Kelvin–Voigt **creep compliance** `J(t) = (1 - e^{-t/τ}) / E`. -/
def creepCompliance (t : ℝ) : ℝ := (1 - exp (-t / P.τ)) / P.E

/-- `J(0) = 0`: no instantaneous elastic response. -/
theorem creepCompliance_zero : P.creepCompliance 0 = 0 := by
  simp [creepCompliance]

/-- Derivative of the creep compliance: `J̇(t) = e^{-t/τ} / η`. -/
theorem hasDerivAt_creepCompliance (t : ℝ) :
    HasDerivAt P.creepCompliance (exp (-t / P.τ) / P.η) t := by
  have h : HasDerivAt (fun t => exp (-t / P.τ)) (exp (-t / P.τ) * (-1 / P.τ)) t :=
    ((hasDerivAt_neg t).div_const P.τ).exp
  refine ((h.const_sub 1).div_const P.E).congr_deriv ?_
  rw [← P.E_mul_τ]
  field_simp [P.E_pos.ne', P.τ_pos.ne']

/-- **Kelvin–Voigt creep**: `ε(t) = σ₀ J(t)` satisfies `σ₀ = E ε + η ε̇`. -/
theorem kv_creep_solves (σ₀ t : ℝ) :
    HasDerivAt (fun t => σ₀ * P.creepCompliance t) (σ₀ * (exp (-t / P.τ) / P.η)) t ∧
      P.KelvinVoigt σ₀ (σ₀ * P.creepCompliance t) (σ₀ * (exp (-t / P.τ) / P.η)) := by
  refine ⟨(P.hasDerivAt_creepCompliance t).const_mul σ₀, ?_⟩
  rw [KelvinVoigt, creepCompliance]
  field_simp [P.E_pos.ne', P.η_pos.ne']
  ring

/-- **Uniqueness of Kelvin–Voigt creep**: a strain history with `ε(0) = 0` obeying
`σ₀ = E ε + η ε̇` for `t ≥ 0` is `ε(t) = σ₀ J(t) = (σ₀ / E)(1 - e^{-t/τ})`. -/
theorem kv_creep_unique {σ₀ : ℝ} {ε ε' : ℝ → ℝ} (hε : ∀ t, 0 ≤ t → HasDerivAt ε (ε' t) t)
    (hlaw : ∀ t, 0 ≤ t → P.KelvinVoigt σ₀ (ε t) (ε' t)) (h0 : ε 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ε t = σ₀ * P.creepCompliance t := by
  have key := eq_mul_exp_of_hasDerivAt P.τ_pos.ne' (u := fun t => ε t - σ₀ / P.E)
    (fun t ht => (hε t ht).sub_const _) (fun t ht => by
      have hl := hlaw t ht
      rw [KelvinVoigt] at hl
      rw [← P.E_mul_τ] at hl
      field_simp [P.E_pos.ne', P.τ_pos.ne']
      linear_combination -hl) ht
  simp only [h0, zero_sub] at key
  rw [creepCompliance]
  linear_combination key

/-- Under constant stress the Kelvin–Voigt strain tends to the elastic value `σ₀ / E`. -/
theorem kv_creep_tendsto (σ₀ : ℝ) :
    Tendsto (fun t => σ₀ * P.creepCompliance t) atTop (𝓝 (σ₀ / P.E)) := by
  rw [show σ₀ / P.E = σ₀ * ((1 - 0) / P.E) by ring]
  exact ((tendsto_exp_neg_div P.τ_pos).const_sub 1).div_const P.E |>.const_mul σ₀

/-! ### Maxwell model -/

/-- The Maxwell law `ε̇ = σ̇ / E + σ / η`. -/
def Maxwell (σ σ' ε' : ℝ) : Prop := ε' = σ' / P.E + σ / P.η

/-- The Maxwell **relaxation modulus** `G(t) = E e^{-t/τ}`. -/
def relaxModulus (t : ℝ) : ℝ := P.E * exp (-t / P.τ)

/-- `G(0) = E`. -/
theorem relaxModulus_zero : P.relaxModulus 0 = P.E := by
  simp [relaxModulus]

/-- Derivative of the relaxation modulus: `Ġ = -G / τ`. -/
theorem hasDerivAt_relaxModulus (t : ℝ) :
    HasDerivAt P.relaxModulus (-P.relaxModulus t / P.τ) t := by
  have h : HasDerivAt (fun t => exp (-t / P.τ)) (exp (-t / P.τ) * (-1 / P.τ)) t :=
    ((hasDerivAt_neg t).div_const P.τ).exp
  exact (h.const_mul P.E).congr_deriv (by simp only [relaxModulus]; ring)

/-- **Maxwell relaxation**: at constant strain (`ε̇ = 0`), `σ(t) = ε₀ G(t)` satisfies the
Maxwell law. -/
theorem maxwell_relax_solves (ε₀ t : ℝ) :
    HasDerivAt (fun t => ε₀ * P.relaxModulus t) (ε₀ * (-P.relaxModulus t / P.τ)) t ∧
      P.Maxwell (ε₀ * P.relaxModulus t) (ε₀ * (-P.relaxModulus t / P.τ)) 0 := by
  refine ⟨(P.hasDerivAt_relaxModulus t).const_mul ε₀, ?_⟩
  rw [Maxwell, ← P.E_mul_τ]
  field_simp [P.E_pos.ne', P.τ_pos.ne']
  ring

/-- **Uniqueness of Maxwell relaxation**: a stress history with `σ(0) = E ε₀` obeying the
Maxwell law at constant strain (`ε̇ = 0`) for `t ≥ 0` is `σ(t) = ε₀ G(t) = E ε₀ e^{-t/τ}`. -/
theorem maxwell_relax_unique {ε₀ : ℝ} {σ σ' : ℝ → ℝ} (hσ : ∀ t, 0 ≤ t → HasDerivAt σ (σ' t) t)
    (hlaw : ∀ t, 0 ≤ t → P.Maxwell (σ t) (σ' t) 0) (h0 : σ 0 = P.E * ε₀) {t : ℝ}
    (ht : 0 ≤ t) : σ t = ε₀ * P.relaxModulus t := by
  have key := eq_mul_exp_of_hasDerivAt P.τ_pos.ne' hσ (fun t ht => by
      have hl := hlaw t ht
      rw [Maxwell, ← P.E_mul_τ] at hl
      field_simp [P.E_pos.ne', P.τ_pos.ne'] at hl ⊢
      linear_combination -hl) ht
  rw [key, h0, relaxModulus]
  ring

/-- Under constant strain the Maxwell stress relaxes completely: `σ(t) → 0`. -/
theorem maxwell_relax_tendsto (ε₀ : ℝ) :
    Tendsto (fun t => ε₀ * P.relaxModulus t) atTop (𝓝 0) := by
  have h := ((tendsto_exp_neg_div P.τ_pos).const_mul P.E).const_mul ε₀
  simp only [mul_zero] at h
  exact h

/-- **Maxwell creep**: at constant stress `σ₀` (`σ̇ = 0`) the strain
`ε(t) = σ₀ / E + σ₀ t / η` satisfies the Maxwell law. -/
theorem maxwell_creep_solves (σ₀ t : ℝ) :
    HasDerivAt (fun t => σ₀ / P.E + σ₀ * t / P.η) (σ₀ / P.η) t ∧
      P.Maxwell σ₀ 0 (σ₀ / P.η) := by
  refine ⟨?_, by simp [Maxwell]⟩
  simpa using (((hasDerivAt_id t).const_mul σ₀).div_const P.η).const_add (σ₀ / P.E)

/-- **Uniqueness of Maxwell creep**: a strain history with the instantaneous elastic response
`ε(0) = σ₀ / E` obeying the Maxwell law at constant stress for `t ≥ 0` is
`ε(t) = σ₀ / E + σ₀ t / η`. -/
theorem maxwell_creep_unique {σ₀ : ℝ} {ε ε' : ℝ → ℝ} (hε : ∀ t, 0 ≤ t → HasDerivAt ε (ε' t) t)
    (hlaw : ∀ t, 0 ≤ t → P.Maxwell σ₀ 0 (ε' t)) (h0 : ε 0 = σ₀ / P.E) {t : ℝ} (ht : 0 ≤ t) :
    ε t = σ₀ / P.E + σ₀ * t / P.η := by
  set g : ℝ → ℝ := fun s => ε s - σ₀ * s / P.η with hg
  have hgd : ∀ s, 0 ≤ s → HasDerivAt g 0 s := by
    intro s hs
    have h1 := (hε s hs).sub (((hasDerivAt_id s).const_mul σ₀).div_const P.η)
    have hl := hlaw s hs
    rw [Maxwell] at hl
    exact h1.congr_deriv (by rw [hl]; ring)
  have hc := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := t)
    (fun s hs => (hgd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [hg, mul_zero, zero_div, sub_zero, h0] at hc
  linear_combination hc

/-- Under a positive constant stress the Maxwell strain grows without bound (viscous flow). -/
theorem maxwell_creep_tendsto_atTop {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    Tendsto (fun t => σ₀ / P.E + σ₀ * t / P.η) atTop atTop := by
  refine tendsto_atTop_add_const_left _ _ ?_
  exact (tendsto_id.const_mul_atTop hσ₀).atTop_div_const P.η_pos

/-! ### Energy dissipation -/

/-- **Kelvin–Voigt energy balance**: the stored energy `½ E ε²` changes at the rate
`σ ε̇ - η ε̇²` (stress power minus dissipation). -/
theorem kv_hasDerivAt_energy {σ ε ε' : ℝ → ℝ} {t : ℝ} (hε : HasDerivAt ε (ε' t) t)
    (hlaw : P.KelvinVoigt (σ t) (ε t) (ε' t)) :
    HasDerivAt (fun t => P.E / 2 * ε t ^ 2) (σ t * ε' t - P.η * ε' t ^ 2) t := by
  convert (hε.pow 2).const_mul (P.E / 2) using 1
  rw [hlaw]
  push_cast
  ring

/-- The Kelvin–Voigt dissipation `η ε̇²` is nonnegative, so the stored energy grows at most at
the rate of the stress power: `σ ε̇ - η ε̇² ≤ σ ε̇`. -/
theorem kv_energy_rate_le (σ ε' : ℝ) : σ * ε' - P.η * ε' ^ 2 ≤ σ * ε' := by
  have := P.η_pos
  nlinarith [sq_nonneg ε']

/-- **Maxwell energy balance**: the energy `σ² / (2E)` stored in the spring changes at the rate
`σ ε̇ - σ² / η` (stress power minus dissipation in the dashpot). -/
theorem maxwell_hasDerivAt_energy {σ σ' ε' : ℝ → ℝ} {t : ℝ} (hσ : HasDerivAt σ (σ' t) t)
    (hlaw : P.Maxwell (σ t) (σ' t) (ε' t)) :
    HasDerivAt (fun t => σ t ^ 2 / (2 * P.E)) (σ t * ε' t - σ t ^ 2 / P.η) t := by
  convert (hσ.pow 2).div_const (2 * P.E) using 1
  rw [hlaw]
  field_simp [P.E_pos.ne', P.η_pos.ne']
  ring

/-- The Maxwell dissipation `σ² / η` is nonnegative: `σ ε̇ - σ² / η ≤ σ ε̇`. -/
theorem maxwell_energy_rate_le (σ ε' : ℝ) : σ * ε' - σ ^ 2 / P.η ≤ σ * ε' := by
  have := div_nonneg (sq_nonneg σ) P.η_pos.le
  linarith

/-! ### Harmonic response of the Kelvin–Voigt model -/

/-- **Harmonic response**: for `ε = ε₀ cos ωt`, the Kelvin–Voigt stress is
`σ = E ε₀ cos ωt - η ω ε₀ sin ωt`. -/
theorem kv_harmonic_stress (ε₀ ω t : ℝ) :
    HasDerivAt (fun t => ε₀ * cos (ω * t)) (-(ε₀ * ω * sin (ω * t))) t ∧
      P.KelvinVoigt (P.E * ε₀ * cos (ω * t) - P.η * ω * ε₀ * sin (ω * t))
        (ε₀ * cos (ω * t)) (-(ε₀ * ω * sin (ω * t))) := by
  refine ⟨?_, by rw [KelvinVoigt]; ring⟩
  exact ((((hasDerivAt_id t).const_mul ω).cos).const_mul ε₀).congr_deriv
    (by simp only [id]; ring)

/-- The **loss angle** `δ = arctan (η ω / E)` of the Kelvin–Voigt model. -/
def lossAngle (ω : ℝ) : ℝ := arctan (P.η * ω / P.E)

/-- The **loss tangent** `tan δ = η ω / E`. -/
theorem kv_tan_lossAngle (ω : ℝ) : tan (P.lossAngle ω) = P.η * ω / P.E := by
  rw [lossAngle, tan_arctan]

/-- **Amplitude–phase form**: `σ = |E*| ε₀ cos (ωt + δ)` with dynamic modulus
`|E*| = √(E² + η² ω²)` and loss angle `δ`. -/
theorem kv_harmonic_stress_eq_amplitude_phase (ε₀ ω t : ℝ) :
    P.E * ε₀ * cos (ω * t) - P.η * ω * ε₀ * sin (ω * t) =
      √(P.E ^ 2 + P.η ^ 2 * ω ^ 2) * ε₀ * cos (ω * t + P.lossAngle ω) := by
  have hE := P.E_pos
  have hs : √(P.E ^ 2 + P.η ^ 2 * ω ^ 2) = P.E * √(1 + (P.η * ω / P.E) ^ 2) := by
    rw [← sqrt_sq hE.le, ← sqrt_mul (sq_nonneg _), sqrt_sq hE.le]
    congr 1
    field_simp
  have hpos : 0 < √(1 + (P.η * ω / P.E) ^ 2) := sqrt_pos.mpr (by positivity)
  rw [cos_add, lossAngle, cos_arctan, sin_arctan, hs]
  field_simp

/-- **Energy dissipated per cycle** by the Kelvin–Voigt model under `ε = ε₀ cos ωt`:
`∫₀^{2π/ω} σ ε̇ dt = π η ω ε₀²` (for `ω ≠ 0`). -/
theorem kv_dissipation_per_cycle (ε₀ : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    ∫ t in (0 : ℝ)..2 * π / ω,
        (P.E * ε₀ * cos (ω * t) - P.η * ω * ε₀ * sin (ω * t)) * (-(ε₀ * ω * sin (ω * t))) =
      π * P.η * ω * ε₀ ^ 2 := by
  set F : ℝ → ℝ := fun t => -(P.E * ε₀ ^ 2 * sin (ω * t) ^ 2 / 2) +
    P.η * ω * ε₀ ^ 2 * (ω * t - sin (ω * t) * cos (ω * t)) / 2 with hF
  have hd : ∀ t, HasDerivAt F
      ((P.E * ε₀ * cos (ω * t) - P.η * ω * ε₀ * sin (ω * t)) * (-(ε₀ * ω * sin (ω * t)))) t := by
    intro t
    have hl : HasDerivAt (fun t => ω * t) ω t := by
      simpa using (hasDerivAt_id t).const_mul ω
    have hs := hl.sin
    have hc := hl.cos
    have h := ((((hs.pow 2).const_mul (P.E * ε₀ ^ 2)).div_const 2).neg).add
      ((((hl.sub (hs.mul hc)).const_mul (P.η * ω * ε₀ ^ 2))).div_const 2)
    convert h using 1
    push_cast
    linear_combination (P.η * ω ^ 2 * ε₀ ^ 2 / 2) * sin_sq_add_cos_sq (ω * t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)]
  · have h2 : ω * (2 * π / ω) = 2 * π := by field_simp
    simp only [hF, h2, sin_two_pi, mul_zero, zero_mul, sin_zero, cos_zero]
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

end Params

/-! ### Standard linear solid (Zener model) -/

/-- The parameters of a **standard linear solid**: an equilibrium spring `E∞ > 0` in parallel
with a Maxwell element of modulus `E₁ > 0` and viscosity `η₁ > 0`. -/
structure Zener where
  /-- The equilibrium (long-time) modulus. -/
  Einf : ℝ
  /-- The modulus of the Maxwell arm. -/
  E₁ : ℝ
  /-- The viscosity of the Maxwell arm. -/
  η₁ : ℝ
  Einf_pos : 0 < Einf
  E₁_pos : 0 < E₁
  η₁_pos : 0 < η₁

namespace Zener

variable (Z : Zener)

/-- The relaxation time `τ₁ = η₁ / E₁` of the Maxwell arm. -/
def τ₁ : ℝ := Z.η₁ / Z.E₁

theorem τ₁_pos : 0 < Z.τ₁ := div_pos Z.η₁_pos Z.E₁_pos

/-- The Zener law `σ + τ₁ σ̇ = E∞ ε + (E∞ + E₁) τ₁ ε̇`. -/
def Law (σ σ' ε ε' : ℝ) : Prop := σ + Z.τ₁ * σ' = Z.Einf * ε + (Z.Einf + Z.E₁) * Z.τ₁ * ε'

/-- The Zener **relaxation modulus** `G(t) = E∞ + E₁ e^{-t/τ₁}`. -/
def relaxModulus (t : ℝ) : ℝ := Z.Einf + Z.E₁ * exp (-t / Z.τ₁)

/-- `G(0) = E∞ + E₁` (instantaneous modulus). -/
theorem relaxModulus_zero : Z.relaxModulus 0 = Z.Einf + Z.E₁ := by
  simp [relaxModulus]

/-- **Zener relaxation**: at constant strain `ε₀`, `σ(t) = ε₀ G(t)` satisfies the Zener law. -/
theorem relax_solves (ε₀ t : ℝ) :
    HasDerivAt (fun t => ε₀ * Z.relaxModulus t) (-(ε₀ * Z.E₁ * exp (-t / Z.τ₁)) / Z.τ₁) t ∧
      Z.Law (ε₀ * Z.relaxModulus t) (-(ε₀ * Z.E₁ * exp (-t / Z.τ₁)) / Z.τ₁) ε₀ 0 := by
  have h : HasDerivAt (fun t => exp (-t / Z.τ₁)) (exp (-t / Z.τ₁) * (-1 / Z.τ₁)) t :=
    ((hasDerivAt_neg t).div_const Z.τ₁).exp
  refine ⟨?_, ?_⟩
  · exact (((h.const_mul Z.E₁).const_add Z.Einf).const_mul ε₀).congr_deriv (by ring)
  · rw [Law, relaxModulus]
    field_simp [Z.τ₁_pos.ne']
    ring

/-- **Uniqueness of Zener relaxation**: a stress history with `σ(0) = (E∞ + E₁) ε₀` obeying the
Zener law at constant strain `ε₀` for `t ≥ 0` is `σ(t) = ε₀ (E∞ + E₁ e^{-t/τ₁})`. -/
theorem relax_unique {ε₀ : ℝ} {σ σ' : ℝ → ℝ} (hσ : ∀ t, 0 ≤ t → HasDerivAt σ (σ' t) t)
    (hlaw : ∀ t, 0 ≤ t → Z.Law (σ t) (σ' t) ε₀ 0) (h0 : σ 0 = (Z.Einf + Z.E₁) * ε₀) {t : ℝ}
    (ht : 0 ≤ t) : σ t = ε₀ * Z.relaxModulus t := by
  have key := eq_mul_exp_of_hasDerivAt Z.τ₁_pos.ne' (u := fun t => σ t - Z.Einf * ε₀)
    (fun t ht => (hσ t ht).sub_const _) (fun t ht => by
      have hl := hlaw t ht
      rw [Law] at hl
      field_simp [Z.τ₁_pos.ne']
      linear_combination hl) ht
  simp only [h0] at key
  rw [relaxModulus]
  linear_combination key

/-- The Zener stress relaxes to the equilibrium value `E∞ ε₀`. -/
theorem relax_tendsto (ε₀ : ℝ) :
    Tendsto (fun t => ε₀ * Z.relaxModulus t) atTop (𝓝 (ε₀ * Z.Einf)) := by
  have h := (((tendsto_exp_neg_div Z.τ₁_pos).const_mul Z.E₁).const_add Z.Einf).const_mul ε₀
  simp only [mul_zero, add_zero] at h
  exact h

end Zener

end Viscoelastic

end ContinuumMechanics
