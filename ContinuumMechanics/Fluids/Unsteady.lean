import ContinuumMechanics.Fluids.Viscous
import ContinuumMechanics.Thermal.Heat
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Unsteady viscous shear flows: Stokes' first and second problems

A **unidirectional shear flow** `v = (u(t, y), 0, 0)` (`shearVel`) is automatically
divergence-free and its convective acceleration `(v·∇)v` vanishes. With constant pressure and no
body force the incompressible Navier–Stokes equations (`IsNavierStokes`) therefore reduce to the
**diffusion equation** `u_t = ν u_yy` for the kinematic viscosity `ν = μ/ρ`
(`isNavierStokes_shearVel_iff_isHeat`), i.e. the heat equation `Heat.IsHeat` of
`ContinuumMechanics.Thermal.Heat`. The shear stress on the planes `y = const` is
`σ₁₂ = μ u_y` (`viscStress_shearVel`).

* **Stokes' second problem** (`stokesII`): a plate oscillating in its own plane with velocity
  `U cos ωt` drives the **Stokes layer** `u(t, y) = U e^{-ky} cos(ωt - ky)`, `k = √(ω/(2ν))`.
  It decays exponentially away from the plate with **penetration depth** `δ = 1/k = √(2ν/ω)`,
  lags behind the wall by the phase `ky`, and exerts the wall shear stress
  `τ_w = -μUk(cos ωt - sin ωt) = -√2 μUk cos(ωt + π/4)`.
* **Stokes' first problem** (`stokesI`): a plate impulsively set into motion with velocity `U`
  generates `u(t, y) = U erfc(y/(2√(νt)))` for `t > 0`. The complementary error function is
  defined by `erfc z = 1 - (2/√π) ∫₀ᶻ e^{-s²} ds` (`erfc`); the diffusion equation follows from
  the fundamental theorem of calculus, the chain rule and `erfc'' = -2z erfc'`. The layer is
  **self-similar**, `u(λ²t, λy) = u(t, y)`, and the wall shear stress is `τ_w = -μU/√(πνt)`.

Fields are functions `u : ℝ → ℝ → ℝ` of time and the wall distance `y`, with the partial
derivatives `dt`, `dx` of `ContinuumMechanics.Strings`.

## Main results

* `shear_momentum_iff`: for `v = (u(t, y), 0, 0)`, the momentum equation at a point is
  `ρ u_t = μ u_yy`; `divergence_shearVel`: `div v = 0`.
* `isNavierStokes_shearVel_iff`, `isNavierStokes_shearVel_iff_isHeat`: the Navier–Stokes
  equations for a shear flow are equivalent to `u_t = (μ/ρ) u_yy`.
* `isHeat_stokesII`, `isHeat_stokesII_wavenumber`, `stokesII_isNavierStokes`: the Stokes layer
  solves the diffusion and the Navier–Stokes equations.
* `stokesII_wall`, `abs_stokesII_le`, `tendsto_stokesII`, `inv_stokesWavenumber`,
  `stokesII_phase`, `stokesII_wallShear`, `stokesII_wallShear_phase`: boundary values,
  exponential decay, penetration depth, phase lag and wall shear stress.
* `hasDerivAt_erfc`, `hasDerivAt_erfcDeriv`, `erfc_zero`, `tendsto_erfc_atTop`: the
  complementary error function (the limit uses the Gaussian integral).
* `stokesI_diffusion`, `stokesI_momentum`: the impulsively started layer solves the diffusion
  and the Navier–Stokes momentum equations for `t > 0`.
* `stokesI_wall`, `tendsto_stokesI`, `tendsto_stokesI_initial`, `stokesI_scaling`,
  `stokesI_wallShear`: no slip, rest at infinity, initial rest, self-similarity and
  `τ_w = -μU/√(πνt)`.

## References

* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §4.3.
* [LandauLifshitz1987] L. D. Landau, E. M. Lifshitz, *Fluid Mechanics*, 2nd ed., §24.
* [Schlichting2017] H. Schlichting, K. Gersten, *Boundary-Layer Theory*, 9th ed., §5.3.
-/

open MeasureTheory Real Filter Topology Set
open ContinuumMechanics.Strings (dx)

noncomputable section

namespace ContinuumMechanics.Fluids

open Korn

/-! ### Reduction of the Navier–Stokes equations for shear flows -/

section Shear

/-- The **unidirectional shear flow** `v = (u(t, y), 0, 0)` with `y = x 1`. -/
def shearVel (u : ℝ → ℝ → ℝ) (t : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![u t (x 1), 0, 0]

/-- `∂ⱼ f(x₂) = δⱼ₂ f'(x₂)` for a function of `y = x 1` alone. -/
theorem pd_comp_one {f : ℝ → ℝ} {x : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f (x 1)) (j : Fin 3) :
    pd (fun y : Fin 3 → ℝ => f (y 1)) j x = if j = 1 then deriv f (x 1) else 0 := by
  have h1 : HasFDerivAt (fun y : Fin 3 → ℝ => y 1) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) 1) x := hasFDerivAt_apply 1 x
  have h := hf.hasDerivAt.hasFDerivAt.comp x h1
  rw [show (fun y : Fin 3 → ℝ => f (y 1)) = f ∘ fun y => y 1 from rfl, pd_eq h]
  by_cases hj : j = 1 <;> simp [hj, e]

/-- The Laplacian of a function of `y = x 1` alone is its second derivative. -/
theorem lap_comp_one {f : ℝ → ℝ} {x : Fin 3 → ℝ} (hf : Differentiable ℝ f)
    (hf' : DifferentiableAt ℝ (deriv f) (x 1)) :
    lap (fun y : Fin 3 → ℝ => f (y 1)) x = deriv (deriv f) (x 1) := by
  have h : ∀ j, pd (fun y : Fin 3 → ℝ => f (y 1)) j =
      fun y => if j = 1 then deriv f (y 1) else 0 := fun j =>
    funext fun y => pd_comp_one (hf _) j
  simp only [lap, Fin.sum_univ_three, h]
  simp [pd_comp_one hf']
  simp [pd]


/-- The components of the shear flow. -/
theorem shearVel_comp (u : ℝ → ℝ → ℝ) (t : ℝ) :
    (fun y => shearVel u t y 0) = (fun y : Fin 3 → ℝ => u t (y 1)) ∧
      (fun y => shearVel u t y 1) = (fun _ => 0) ∧ (fun y => shearVel u t y 2) = (fun _ => 0) :=
  ⟨rfl, funext fun y => by simp [shearVel], funext fun y => by simp [shearVel]⟩

variable {ρ μ p₀ : ℝ} {u : ℝ → ℝ → ℝ} {t : ℝ} {x : Fin 3 → ℝ}

/-- The velocity gradient of a shear flow: `∂ⱼvᵢ = u_y` for `(i, j) = (1, 2)`, else `0`. -/
theorem pd_shearVel (hu : DifferentiableAt ℝ (u t) (x 1)) (i j : Fin 3) :
    pd (fun y => shearVel u t y i) j x = if i = 0 ∧ j = 1 then dx u t (x 1) else 0 := by
  obtain ⟨h0, h1, h2⟩ := shearVel_comp u t
  have hz : ∀ j, pd (fun _ : Fin 3 → ℝ => (0 : ℝ)) j = fun _ => 0 := Torsion.pd_const 0
  match i with
  | 0 => rw [h0, pd_comp_one hu]; simp [dx]
  | 1 => rw [h1, hz]; simp
  | 2 => rw [h2, hz]; simp

/-- A shear flow is **incompressible**: `div v = 0`. -/
theorem divergence_shearVel (hu : DifferentiableAt ℝ (u t) (x 1)) :
    divergence (shearVel u t) x = 0 := by
  simp [divergence, Fin.sum_univ_three, pd_shearVel hu]

/-- The **shear stress** of a shear flow on the planes `y = const` is `σ₁₂ = μ u_y`. -/
theorem viscStress_shearVel (hu : DifferentiableAt ℝ (u t) (x 1)) :
    viscStress μ (fun _ => p₀) (shearVel u t) 0 1 x = μ * dx u t (x 1) := by
  simp [viscStress, pd_shearVel hu]

/-- **Reduction of Navier–Stokes for a shear flow**: at a point `(t, x)`, the momentum equation
for `v = (u(t, y), 0, 0)` with constant pressure and no body force is `ρ u_t = μ u_yy`; the
convective acceleration `(v·∇)v` vanishes. -/
theorem shear_momentum_iff (hu : Differentiable ℝ (u t))
    (hu' : DifferentiableAt ℝ (dx u t) (x 1)) :
    ρ • accel (shearVel u) t x =
        -grad (fun _ => p₀) x + μ • vecLap (shearVel u t) x + ρ • (0 : Fin 3 → ℝ) ↔
      ρ * Strings.dt u t (x 1) = μ * dx (dx u) t (x 1) := by
  obtain ⟨h0, h1, h2⟩ := shearVel_comp u t
  have hl : lap (fun y : Fin 3 → ℝ => u t (y 1)) x = dx (dx u) t (x 1) := lap_comp_one hu hu'
  have hz : ∀ j, pd (fun _ : Fin 3 → ℝ => (0 : ℝ)) j = fun _ => 0 := Torsion.pd_const 0
  have hc : convect (shearVel u t) x = 0 := by
    ext i
    simp only [convect, Fin.sum_univ_three, pd_shearVel (hu _)]
    simp [shearVel]
  have hL : vecLap (shearVel u t) x = ![dx (dx u) t (x 1), 0, 0] := by
    ext i
    match i with
    | 0 => exact hl
    | 1 => change lap (fun y => shearVel u t y 1) x = 0; rw [h1]; simp [lap, hz]
    | 2 => change lap (fun y => shearVel u t y 2) x = 0; rw [h2]; simp [lap, hz]
  have hg : grad (fun _ : Fin 3 → ℝ => p₀) x = 0 := by ext j; simp [grad, pd]
  have hd : ∀ i, Fluids.dt (fun s y => shearVel u s y i) t x =
      if i = 0 then Strings.dt u t (x 1) else 0 := by
    intro i
    fin_cases i <;> simp [Fluids.dt, Strings.dt, shearVel]
  rw [accel_eq, hc, add_zero, hL, hg]
  constructor
  · intro h
    simpa [hd] using congrFun h 0
  · intro h
    ext i
    fin_cases i <;> simp [hd, h]

/-- The **Navier–Stokes equations for a shear flow** `v = (u(t, y), 0, 0)` with constant
pressure and no body force are equivalent to `ρ u_t = μ u_yy`. -/
theorem isNavierStokes_shearVel_iff (hu : ∀ t, Differentiable ℝ (u t))
    (hu' : ∀ t, Differentiable ℝ (dx u t)) :
    IsNavierStokes ρ μ (shearVel u) (fun _ _ => p₀) 0 ↔
      ∀ t y, ρ * Strings.dt u t y = μ * dx (dx u) t y := by
  constructor
  · intro h t y
    have := (shear_momentum_iff (p₀ := p₀) (x := ![0, y, 0]) (hu t) (hu' t _)).1
      (h.momentum t _)
    simpa using this
  · intro h
    exact ⟨fun t x => (shear_momentum_iff (hu t) (hu' t _)).2 (h t (x 1)),
      fun t x => divergence_shearVel (hu t _)⟩

/-- **Shear flows obey the diffusion equation**: for `ρ ≠ 0`, the Navier–Stokes equations for
`v = (u(t, y), 0, 0)` hold iff `u_t = ν u_yy` with the kinematic viscosity `ν = μ/ρ`. -/
theorem isNavierStokes_shearVel_iff_isHeat (hρ : ρ ≠ 0) (hu : ∀ t, Differentiable ℝ (u t))
    (hu' : ∀ t, Differentiable ℝ (dx u t)) :
    IsNavierStokes ρ μ (shearVel u) (fun _ _ => p₀) 0 ↔ Heat.IsHeat (μ / ρ) u := by
  rw [isNavierStokes_shearVel_iff hu hu']
  refine forall₂_congr fun t y => ?_
  constructor <;> intro h
  · field_simp; linarith
  · rw [h]; field_simp

end Shear

/-! ### Stokes' second problem: the oscillating plate -/

section Second

/-- **Stokes' second problem**: `u(t, y) = U e^{-ky} cos(ωt - ky)`. -/
def stokesII (U k ω t y : ℝ) : ℝ := U * exp (-(k * y)) * cos (ω * t - k * y)

variable {U k ω ν : ℝ}

/-- Time derivative of the Stokes layer. -/
theorem hasDerivAt_stokesII_t (t y : ℝ) :
    HasDerivAt (fun s => stokesII U k ω s y)
      (-(U * exp (-(k * y)) * (ω * sin (ω * t - k * y)))) t := by
  have h : HasDerivAt (fun s => ω * s - k * y) ω t := by
    simpa using ((hasDerivAt_id t).const_mul ω).sub_const (k * y)
  refine (h.cos.const_mul (U * exp (-(k * y)))).congr_deriv ?_
  ring

/-- Space derivative of the Stokes layer:
`u_y = U k e^{-ky} (sin(ωt - ky) - cos(ωt - ky))`. -/
theorem hasDerivAt_stokesII_y (t y : ℝ) :
    HasDerivAt (stokesII U k ω t)
      (U * k * exp (-(k * y)) * (sin (ω * t - k * y) - cos (ω * t - k * y))) y := by
  have h1 : HasDerivAt (fun z => -(k * z)) (-k) y := by
    simpa using ((hasDerivAt_id y).const_mul k).fun_neg
  have h2 : HasDerivAt (fun z => ω * t - k * z) (-k) y := by
    simpa using ((hasDerivAt_id y).const_mul k).const_sub (ω * t)
  refine ((h1.exp.const_mul U).mul h2.cos).congr_deriv ?_
  ring

/-- The space derivative field of the Stokes layer. -/
theorem dx_stokesII :
    dx (stokesII U k ω) = fun t y =>
      U * k * exp (-(k * y)) * (sin (ω * t - k * y) - cos (ω * t - k * y)) :=
  funext fun t => funext fun y => (hasDerivAt_stokesII_y t y).deriv

/-- Second space derivative: `u_yy = -2 U k² e^{-ky} sin(ωt - ky)`. -/
theorem hasDerivAt_dx_stokesII (t y : ℝ) :
    HasDerivAt (dx (stokesII U k ω) t)
      (-(2 * U * k ^ 2 * exp (-(k * y)) * sin (ω * t - k * y))) y := by
  rw [dx_stokesII]
  have h1 : HasDerivAt (fun z => -(k * z)) (-k) y := by
    simpa using ((hasDerivAt_id y).const_mul k).fun_neg
  have h2 : HasDerivAt (fun z => ω * t - k * z) (-k) y := by
    simpa using ((hasDerivAt_id y).const_mul k).const_sub (ω * t)
  refine ((h1.exp.const_mul (U * k)).mul (h2.sin.fun_sub h2.cos)).congr_deriv ?_
  ring

/-- **Stokes' second problem solves the diffusion equation** `u_t = ν u_yy` whenever
`2νk² = ω`. -/
theorem isHeat_stokesII (h : 2 * ν * k ^ 2 = ω) : Heat.IsHeat ν (stokesII U k ω) := by
  intro t y
  change deriv _ t = ν * deriv (dx (stokesII U k ω) t) y
  rw [(hasDerivAt_stokesII_t t y).deriv, (hasDerivAt_dx_stokesII t y).deriv, ← h]
  ring


/-- The **wave number** `k = √(ω/(2ν))` of the Stokes layer. -/
def stokesWavenumber (ν ω : ℝ) : ℝ := √(ω / (2 * ν))

/-- The wave number satisfies the dispersion relation `2νk² = ω`. -/
theorem stokesWavenumber_sq (hν : 0 < ν) (hω : 0 ≤ ω) :
    2 * ν * stokesWavenumber ν ω ^ 2 = ω := by
  rw [stokesWavenumber, sq_sqrt (div_nonneg hω (by positivity))]
  field_simp

/-- The **oscillating plate** `u(t, y) = U e^{-ky} cos(ωt - ky)`, `k = √(ω/(2ν))`, solves the
diffusion equation `u_t = ν u_yy`. -/
theorem isHeat_stokesII_wavenumber (hν : 0 < ν) (hω : 0 ≤ ω) :
    Heat.IsHeat ν (stokesII U (stokesWavenumber ν ω) ω) :=
  isHeat_stokesII (stokesWavenumber_sq hν hω)

/-- **No slip** at the oscillating plate: `u(t, 0) = U cos ωt`. -/
theorem stokesII_wall (t : ℝ) : stokesII U k ω t 0 = U * cos (ω * t) := by
  simp [stokesII]

/-- The amplitude decays exponentially: `|u(t, y)| ≤ |U| e^{-ky}`. -/
theorem abs_stokesII_le (t y : ℝ) : |stokesII U k ω t y| ≤ |U| * exp (-(k * y)) := by
  rw [stokesII, abs_mul, abs_mul, abs_exp]
  exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)

/-- Far from the plate the fluid is at rest: `u(t, y) → 0` as `y → ∞` (for `k > 0`). -/
theorem tendsto_stokesII (hk : 0 < k) (t : ℝ) :
    Tendsto (stokesII U k ω t) atTop (𝓝 0) := by
  have h : Tendsto (fun y => |U| * exp (-(k * y))) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hk)).const_mul |U|
  exact squeeze_zero_norm (fun y => abs_stokesII_le t y) h

/-- The **penetration depth** `δ = 1/k = √(2ν/ω)` of the Stokes layer. -/
theorem inv_stokesWavenumber (ν ω : ℝ) : (stokesWavenumber ν ω)⁻¹ = √(2 * ν / ω) := by
  rw [stokesWavenumber, ← sqrt_inv, inv_div]

/-- At the penetration depth `δ = 1/k` the amplitude has dropped by the factor `e⁻¹`. -/
theorem stokesII_amplitude_depth (hk : k ≠ 0) : U * exp (-(k * k⁻¹)) = U * exp (-1) := by
  rw [mul_inv_cancel₀ hk]

/-- **Phase lag**: the velocity at depth `y` repeats the wall velocity with time lag `ky/ω`,
`u(t + ky/ω, y) = U e^{-ky} cos ωt`. -/
theorem stokesII_phase (hω : ω ≠ 0) (t y : ℝ) :
    stokesII U k ω (t + k * y / ω) y = U * exp (-(k * y)) * cos (ω * t) := by
  rw [stokesII]
  congr 2
  field_simp
  ring

/-- The **wall shear stress** `τ_w = μ u_y(t, 0) = -μUk(cos ωt - sin ωt)`. -/
theorem stokesII_wallShear (μ t : ℝ) :
    μ * dx (stokesII U k ω) t 0 = -(μ * U * k * (cos (ω * t) - sin (ω * t))) := by
  rw [dx_stokesII]
  simp
  ring

/-- `cos a - sin a = √2 cos(a + π/4)`. -/
theorem cos_sub_sin_eq (a : ℝ) : cos a - sin a = √2 * cos (a + π / 4) := by
  rw [cos_add, cos_pi_div_four, sin_pi_div_four]
  have h : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  linear_combination (-(cos a - sin a) / 2) * h

/-- The wall shear stress of the Stokes layer, `τ_w = -√2 μUk cos(ωt + π/4)`: it leads the wall
velocity by a phase `π/4` (up to sign). -/
theorem stokesII_wallShear_phase (μ t : ℝ) :
    μ * dx (stokesII U k ω) t 0 = -(√2 * μ * U * k * cos (ω * t + π / 4)) := by
  rw [stokesII_wallShear, cos_sub_sin_eq]
  ring

/-- The Stokes layer with `k = √(ω/(2ν))`, `ν = μ/ρ`, together with constant pressure solves
the **Navier–Stokes equations**. -/
theorem stokesII_isNavierStokes {ρ μ p₀ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hω : 0 ≤ ω) :
    IsNavierStokes ρ μ (shearVel (stokesII U (stokesWavenumber (μ / ρ) ω) ω))
      (fun _ _ => p₀) 0 :=
  (isNavierStokes_shearVel_iff_isHeat hρ.ne'
    (fun t y => (hasDerivAt_stokesII_y t y).differentiableAt)
    (fun t y => (hasDerivAt_dx_stokesII t y).differentiableAt)).2
    (isHeat_stokesII_wavenumber (div_pos hμ hρ) hω)

end Second

/-! ### The complementary error function -/

section Erfc

/-- The **complementary error function** `erfc z = 1 - (2/√π) ∫₀ᶻ e^{-s²} ds`. -/
def erfc (z : ℝ) : ℝ := 1 - 2 / √π * ∫ s in (0 : ℝ)..z, exp (-s ^ 2)

/-- The derivative `erfc' z = -(2/√π) e^{-z²}`. -/
def erfcDeriv (z : ℝ) : ℝ := -(2 / √π) * exp (-z ^ 2)

/-- `erfc(0) = 1`. -/
@[simp] theorem erfc_zero : erfc 0 = 1 := by simp [erfc]

/-- **Fundamental theorem of calculus**: `erfc' = -(2/√π) e^{-z²}`. -/
theorem hasDerivAt_erfc (z : ℝ) : HasDerivAt erfc (erfcDeriv z) z := by
  have hc : Continuous fun s : ℝ => exp (-s ^ 2) := by fun_prop
  have h := (hc.integral_hasStrictDerivAt 0 z).hasDerivAt
  refine (h.const_mul (2 / √π)).const_sub 1 |>.congr_deriv ?_
  simp [erfcDeriv]

/-- `erfc'' = -2z erfc'`. -/
theorem hasDerivAt_erfcDeriv (z : ℝ) : HasDerivAt erfcDeriv (-2 * z * erfcDeriv z) z := by
  have h : HasDerivAt (fun s : ℝ => -s ^ 2) (-(2 * z)) z := by
    simpa using (hasDerivAt_pow 2 z).fun_neg
  refine (h.exp.const_mul (-(2 / √π))).congr_deriv ?_
  simp only [erfcDeriv]
  ring

/-- `erfc z → 0` as `z → ∞`, by the Gaussian integral `∫₀^∞ e^{-s²} ds = √π/2`. -/
theorem tendsto_erfc_atTop : Tendsto erfc atTop (𝓝 0) := by
  have hi : IntegrableOn (fun s : ℝ => exp (-s ^ 2)) (Ioi 0) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn
  have h := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  have hg : ∫ s in Ioi (0 : ℝ), exp (-s ^ 2) = √π / 2 := by
    simpa using integral_gaussian_Ioi 1
  rw [hg] at h
  have hπ : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  have := (h.const_mul (2 / √π)).const_sub 1
  rw [show (1 : ℝ) - 2 / √π * (√π / 2) = 0 by field_simp; ring] at this
  exact this


end Erfc

/-! ### Stokes' first problem: the impulsively started plate -/

section First

/-- **Stokes' first problem** (impulsively started plate):
`u(t, y) = U erfc(y/(2√(νt)))`, meaningful for `t > 0`. -/
def stokesI (U ν t y : ℝ) : ℝ := U * erfc (y / (2 * √(ν * t)))

variable {U ν : ℝ}

/-- Space derivative of the impulsively started layer: `u_y = U erfc'(η)/(2√(νt))`. -/
theorem hasDerivAt_stokesI_y (t y : ℝ) :
    HasDerivAt (stokesI U ν t)
      (U * erfcDeriv (y / (2 * √(ν * t))) * (1 / (2 * √(ν * t)))) y := by
  have h := (hasDerivAt_id y).div_const (2 * √(ν * t))
  refine ((hasDerivAt_erfc _).comp y h).const_mul U |>.congr_deriv ?_
  simp only [id]
  ring

/-- The space derivative field of the impulsively started layer. -/
theorem dx_stokesI : dx (stokesI U ν) = fun t y =>
    U * erfcDeriv (y / (2 * √(ν * t))) * (1 / (2 * √(ν * t))) :=
  funext fun t => funext fun y => (hasDerivAt_stokesI_y t y).deriv

/-- Second space derivative: `u_yy = U erfc''(η)/(4νt)`. -/
theorem hasDerivAt_dx_stokesI (t y : ℝ) :
    HasDerivAt (dx (stokesI U ν) t)
      (U * (-2 * (y / (2 * √(ν * t))) * erfcDeriv (y / (2 * √(ν * t)))) *
        (1 / (2 * √(ν * t))) ^ 2) y := by
  rw [dx_stokesI]
  have h := (hasDerivAt_id y).div_const (2 * √(ν * t))
  refine (((hasDerivAt_erfcDeriv _).comp y h).const_mul U).mul_const (1 / (2 * √(ν * t)))
    |>.congr_deriv ?_
  simp only [id]
  ring

/-- Time derivative of the impulsively started layer for `t > 0`:
`u_t = U erfc'(η) η_t` with `η_t = -y/(4t√(νt))`. -/
theorem hasDerivAt_stokesI_t (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => stokesI U ν s y)
      (U * erfcDeriv (y / (2 * √(ν * t))) * (-(y / (4 * t * √(ν * t))))) t := by
  have hνt : 0 < ν * t := mul_pos hν ht
  have hs : 0 < √(ν * t) := sqrt_pos.2 hνt
  have h1 : HasDerivAt (fun s => ν * s) ν t := by
    simpa using (hasDerivAt_id t).const_mul ν
  have h2 := (h1.sqrt hνt.ne').const_mul 2
  have h3 : HasDerivAt (fun s => y / (2 * √(ν * s)))
      ((0 * (2 * √(ν * t)) - y * (2 * (ν / (2 * √(ν * t))))) / (2 * √(ν * t)) ^ 2) t :=
    (hasDerivAt_const t y).div h2 (by positivity)
  refine ((hasDerivAt_erfc _).comp t h3).const_mul U |>.congr_deriv ?_
  have hsq : √(ν * t) ^ 2 = ν * t := sq_sqrt hνt.le
  field_simp
  rw [hsq]
  ring

/-- **Stokes' first problem solves the diffusion equation**: `u_t = ν u_yy` for `t > 0`. -/
theorem stokesI_diffusion (hν : 0 < ν) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Strings.dt (stokesI U ν) t y = ν * dx (dx (stokesI U ν)) t y := by
  change deriv _ t = ν * deriv (dx (stokesI U ν) t) y
  rw [(hasDerivAt_stokesI_t hν ht y).deriv, (hasDerivAt_dx_stokesI t y).deriv]
  have hνt : 0 < ν * t := mul_pos hν ht
  have hs : 0 < √(ν * t) := sqrt_pos.2 hνt
  have hsq : √(ν * t) ^ 2 = ν * t := sq_sqrt hνt.le
  field_simp
  rw [hsq]
  ring

/-- **No slip** at the impulsively started plate: `u(t, 0) = U`. -/
theorem stokesI_wall (t : ℝ) : stokesI U ν t 0 = U := by simp [stokesI]

/-- Far from the plate the fluid is at rest: `u(t, y) → 0` as `y → ∞`, for `t > 0`. -/
theorem tendsto_stokesI (hν : 0 < ν) {t : ℝ} (ht : 0 < t) :
    Tendsto (stokesI U ν t) atTop (𝓝 0) := by
  have hs : 0 < 2 * √(ν * t) := by have := sqrt_pos.2 (mul_pos hν ht); positivity
  have h := tendsto_erfc_atTop.comp (tendsto_id.atTop_div_const hs)
  have := h.const_mul U
  rw [mul_zero] at this
  exact this

/-- **Self-similarity**: `u(λ²t, λy) = u(t, y)` for `λ > 0`; the solution depends on `(t, y)`
only through the similarity variable `η = y/(2√(νt))`. -/
theorem stokesI_scaling {l : ℝ} (hl : 0 < l) (t y : ℝ) :
    stokesI U ν (l ^ 2 * t) (l * y) = stokesI U ν t y := by
  rw [stokesI, stokesI, show ν * (l ^ 2 * t) = l ^ 2 * (ν * t) by ring,
    sqrt_mul (sq_nonneg l), sqrt_sq hl.le, show 2 * (l * √(ν * t)) = l * (2 * √(ν * t)) by ring,
    mul_div_mul_left _ _ hl.ne']

/-- The **wall shear stress** of the impulsively started plate,
`τ_w = μ u_y(t, 0) = -μU/√(πνt)`. -/
theorem stokesI_wallShear (μ t : ℝ) :
    μ * dx (stokesI U ν) t 0 = -(μ * U / √(π * ν * t)) := by
  rw [dx_stokesI]
  simp only [zero_div, erfcDeriv]
  rw [mul_assoc π, sqrt_mul pi_pos.le]
  have hπ : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  simp
  field_simp

/-- **Initial rest**: at every `y > 0` the fluid is at rest initially, `u(t, y) → 0` as
`t → 0⁺`. -/
theorem tendsto_stokesI_initial (hν : 0 < ν) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun t => stokesI U ν t y) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun t => √(ν * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht =>
      sqrt_pos.2 (mul_pos hν ht)⟩
    have hc : Continuous fun t => √(ν * t) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hη : Tendsto (fun t => y / (2 * √(ν * t))) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp hs).const_mul_atTop (div_pos hy two_pos)
    refine this.congr fun t => ?_
    simp only [Function.comp_apply]
    ring
  have := (tendsto_erfc_atTop.comp hη).const_mul U
  rw [mul_zero] at this
  exact this

/-- The impulsively started layer with `ν = μ/ρ` and constant pressure satisfies the
**Navier–Stokes momentum equation** at every time `t > 0`. -/
theorem stokesI_momentum {ρ μ p₀ t : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (ht : 0 < t)
    (x : Fin 3 → ℝ) :
    ρ • accel (shearVel (stokesI U (μ / ρ))) t x =
      -grad (fun _ => p₀) x + μ • vecLap (shearVel (stokesI U (μ / ρ)) t) x +
        ρ • (0 : Fin 3 → ℝ) := by
  refine (shear_momentum_iff (fun y => (hasDerivAt_stokesI_y t y).differentiableAt)
    (hasDerivAt_dx_stokesI t _).differentiableAt).2 ?_
  rw [stokesI_diffusion (div_pos hμ hρ) ht]
  field_simp

end First

end ContinuumMechanics.Fluids
