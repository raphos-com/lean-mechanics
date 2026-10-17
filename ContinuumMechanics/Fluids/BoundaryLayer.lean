import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The laminar flat-plate boundary layer: the momentum-integral method

A uniform stream of speed `U` and kinematic viscosity `ν = μ/ρ` flows along a flat plate; at the
distance `x` from the leading edge the viscous layer has thickness `δ(x)`. In the
**Kármán–Pohlhausen method** one assumes a similar velocity profile `u/U = f(η)`,
`η = y/δ ∈ [0, 1]`, and imposes only the **von Kármán momentum integral** for zero pressure
gradient, `dθ/dx = τ_w/(ρU²)`.

* The profile determines the **integral thicknesses**: the displacement thickness
  `δ*/δ = ∫₀¹ (1 - f)` (`dispRatio`), the momentum thickness `θ/δ = α = ∫₀¹ f(1 - f)`
  (`momRatio`), and the wall shear stress `τ_w = μU β/δ`, `β = f'(0)` (`wallShear`).
* The momentum integral becomes `δ δ' = (β/α) ν/U` (`vonKarman_iff`), whose solution with
  `δ(0) = 0` is `δ(x) = √(2(β/α) νx/U)` (`blThickness`), i.e. `δ/x = √(2β/α)/√Re_x` with
  `Re_x = Ux/ν`. The solution is unique among positive solutions continuous at the leading edge
  (`eq_blThickness_of_hasDerivAt`), since `(δ²)' = 2(β/α)ν/U` is constant.
* **Profiles**: the linear profile `f = η` (`α = 1/6`, `β = 1`, `δ/x = √12/√Re_x`), the
  **Pohlhausen cubic** `f = (3/2)η - (1/2)η³` (`α = 39/280`, `β = 3/2`,
  `δ/x = √(280/13)/√Re_x ≈ 4.64/√Re_x`) and the sine profile `f = sin(πη/2)`
  (`α = (4 - π)/(2π)`, `β = π/2`, `δ/x = √(2π²/(4 - π))/√Re_x ≈ 4.80/√Re_x`).
* **Skin friction**: `c_f = 2τ_w/(ρU²) = 2βν/(Uδ)` and `c_f √Re_x = √(2αβ)`; for Pohlhausen
  `√(117/280) ≈ 0.646` (Blasius: `0.664`). Averaging `c_f ∝ x^{-1/2}` over `[0, L]` gives the
  drag coefficient `C_D = 2 c_f(L)`, from `∫₀ᴸ x^{-1/2} dx = 2√L`.
* For Pohlhausen `δ*/δ = 3/8`, so `δ*/x = (3/8)√(280/13)/√Re_x ≈ 1.74/√Re_x`.

## Main results

* `vonKarman_iff`: the momentum integral `α δ' = τ_w/(ρU²)` is `δ δ' = (β/α) ν/U`.
* `hasDerivAt_blThickness`, `blThickness_zero`, `blThickness_mul_deriv`: `δ(x) = √(2kx)`,
  `k = (β/α)ν/U`, solves the momentum integral for `x > 0` and vanishes at the leading edge.
* `eq_blThickness_of_hasDerivAt`, `eq_blThickness_of_vonKarman`: uniqueness.
* `blThickness_div`: `δ/x = √(2β/α)/√Re_x`.
* `momRatio_linear`, `linear_coeff`, `sqrt_twelve_bounds`: the linear profile.
* `pohlhausen_*`, `momRatio_pohlhausen`, `dispRatio_pohlhausen`, `pohlhausen_coeff`,
  `sqrt_pohlhausen_bounds`: the Pohlhausen cubic, `δ/x = √(280/13)/√Re_x`,
  `4.64 < √(280/13) < 4.65`.
* `momRatio_sine`, `sine_coeff`, `sqrt_sine_bounds`: the sine profile.
* `skinFriction_eq`, `skinFriction_mul_sqrt_reynolds`, `pohlhausen_skinFriction`,
  `sqrt_pohlhausen_skin_bounds`: the local skin-friction coefficient.
* `integral_inv_sqrt`, `dragCoeff_eq`: `∫₀ᴸ x^{-1/2} = 2√L` and `C_D = 2 c_f(L)`.
* `pohlhausen_displacement`, `pohlhausen_displacement_bounds`: `δ*/x ≈ 1.74/√Re_x`.

## References

* [Schlichting2017] H. Schlichting, K. Gersten, *Boundary-Layer Theory*, 9th ed., §10.4.
* [White2006] F. M. White, *Viscous Fluid Flow*, 3rd ed., §4-6.
* [Pohlhausen1921] K. Pohlhausen, *Zur näherungsweisen Integration der Differentialgleichung
  der laminaren Grenzschicht*, ZAMM 1 (1921).
-/

open Real Set intervalIntegral

noncomputable section

namespace ContinuumMechanics.Fluids.BoundaryLayer

/-! ### Integral thicknesses and the momentum integral -/

section Integral

/-- The **displacement-thickness ratio** `δ*/δ = ∫₀¹ (1 - f(η)) dη` of a profile `f`. -/
def dispRatio (f : ℝ → ℝ) : ℝ := ∫ η in (0 : ℝ)..1, (1 - f η)

/-- The **momentum-thickness ratio** `θ/δ = ∫₀¹ f(η)(1 - f(η)) dη` of a profile `f`. -/
def momRatio (f : ℝ → ℝ) : ℝ := ∫ η in (0 : ℝ)..1, f η * (1 - f η)

/-- The **wall shear stress** `τ_w = μ U β/δ` of a profile with wall slope `f'(0) = β`. -/
def wallShear (μ U β δ : ℝ) : ℝ := μ * U * β / δ

/-- The wall shear stress is `μ ∂u/∂y` at `y = 0` for `u(y) = U f(y/δ)`. -/
theorem hasDerivAt_profile_wall {f : ℝ → ℝ} {β : ℝ} (hf : HasDerivAt f β 0) (μ U δ : ℝ) :
    HasDerivAt (fun y => μ * (U * f (y / δ))) (wallShear μ U β δ) 0 := by
  have h : HasDerivAt (fun y : ℝ => y / δ) (1 / δ) 0 := (hasDerivAt_id 0).div_const δ
  have h2 : HasDerivAt (fun y => f (y / δ)) (β * (1 / δ)) 0 := by
    have hf' : HasDerivAt f β (0 / δ) := by simpa using hf
    exact hf'.comp 0 h
  convert (h2.const_mul U).const_mul μ using 1
  simp only [wallShear]
  ring

/-- **von Kármán momentum integral** for a flat plate with `θ = αδ`, `τ_w = μUβ/δ`:
`α δ' = τ_w/(ρU²)` is equivalent to `δ δ' = (β/α) ν/U`, `ν = μ/ρ`. -/
theorem vonKarman_iff {α β μ ρ U δ δ' : ℝ} (hα : α ≠ 0) (hρ : ρ ≠ 0) (hU : U ≠ 0)
    (hδ : δ ≠ 0) :
    α * δ' = wallShear μ U β δ / (ρ * U ^ 2) ↔ δ * δ' = β / α * (μ / ρ) / U := by
  have e1 : wallShear μ U β δ / (ρ * U ^ 2) = μ * β / (δ * ρ * U) := by
    unfold wallShear; field_simp
  have e2 : β / α * (μ / ρ) / U = μ * β / (α * ρ * U) := by field_simp
  rw [e1, e2, eq_div_iff (by positivity), eq_div_iff (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- The **momentum-integral boundary-layer thickness** `δ(x) = √(2kx)`; with
`k = (β/α) ν/U` this is `δ(x) = √(2(β/α) νx/U)`. -/
def blThickness (k x : ℝ) : ℝ := √(2 * k * x)

/-- The layer starts at the leading edge: `δ(0) = 0`. -/
@[simp] theorem blThickness_zero (k : ℝ) : blThickness k 0 = 0 := by simp [blThickness]

/-- `δ(x) > 0` for `x > 0`. -/
theorem blThickness_pos {k x : ℝ} (hk : 0 < k) (hx : 0 < x) : 0 < blThickness k x :=
  Real.sqrt_pos.2 (by positivity)

/-- `δ(x)² = 2kx`. -/
theorem blThickness_sq {k x : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) : blThickness k x ^ 2 = 2 * k * x :=
  Real.sq_sqrt (by positivity)

/-- `δ(x) = √(2kx)` solves `δ' = k/δ` for `x > 0`. -/
theorem hasDerivAt_blThickness {k x : ℝ} (hk : 0 < k) (hx : 0 < x) :
    HasDerivAt (blThickness k) (k / blThickness k x) x := by
  have h : HasDerivAt (fun x => 2 * k * x) (2 * k) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * k)
  refine (h.sqrt (by positivity)).congr_deriv ?_
  simp only [blThickness]
  field_simp

/-- The momentum integral in the form `δ δ' = k`. -/
theorem blThickness_mul_deriv {k x : ℝ} (hk : 0 < k) (hx : 0 < x) :
    blThickness k x * deriv (blThickness k) x = k := by
  rw [(hasDerivAt_blThickness hk hx).deriv]
  field_simp [(blThickness_pos hk hx).ne']

/-- `δ(x) = √(2(β/α)νx/U)` solves the von Kármán momentum integral for `x > 0`. -/
theorem blThickness_vonKarman {α β μ ρ U x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hμ : 0 < μ)
    (hρ : 0 < ρ) (hU : 0 < U) (hx : 0 < x) :
    α * deriv (blThickness (β / α * (μ / ρ) / U)) x =
      wallShear μ U β (blThickness (β / α * (μ / ρ) / U) x) / (ρ * U ^ 2) := by
  have hk : 0 < β / α * (μ / ρ) / U := by positivity
  rw [vonKarman_iff hα.ne' hρ.ne' hU.ne' (blThickness_pos hk hx).ne']
  exact blThickness_mul_deriv hk hx

/-- **Uniqueness**: a positive solution of `δ' = k/δ` on `x > 0` which is continuous at the
leading edge with `δ(0) = 0` equals `√(2kx)`, since `(δ² - 2kx)' = 0`. -/
theorem eq_blThickness_of_hasDerivAt {k : ℝ} {δ : ℝ → ℝ}
    (hd : ∀ x, 0 < x → HasDerivAt δ (k / δ x) x) (hpos : ∀ x, 0 < x → 0 < δ x)
    (h0 : δ 0 = 0) (hc : ContinuousWithinAt δ (Ici 0) 0) {x : ℝ} (hx : 0 ≤ x) :
    δ x = blThickness k x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [h0]
  have hcont : ContinuousOn δ (Icc 0 x) := by
    intro y hy
    rcases hy.1.eq_or_lt with rfl | hy0
    · exact hc.mono Icc_subset_Ici_self
    · exact (hd y hy0).continuousAt.continuousWithinAt
  obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope (fun y => δ y ^ 2 - 2 * k * y)
    (fun y => 2 * δ y * (k / δ y) - 2 * k) hx
    ((hcont.pow 2).sub (by fun_prop))
    (fun y hy => by
      have := ((hd y hy.1).pow 2).sub ((hasDerivAt_id y).const_mul (2 * k))
      exact this.congr_deriv (by simp))
  have hδc := (hpos c hc'.1).ne'
  have hzero : 2 * δ c * (k / δ c) - 2 * k = 0 := by field_simp; ring
  rw [hzero, h0, eq_comm, div_eq_zero_iff] at hcd
  have hsq : δ x ^ 2 = 2 * k * x := by
    rcases hcd with h | h
    · linarith
    · linarith
  have hk : 0 ≤ 2 * k * x := hsq ▸ sq_nonneg _
  rw [blThickness, ← hsq, Real.sqrt_sq (hpos x hx).le]

/-- Uniqueness for the von Kármán momentum integral itself. -/
theorem eq_blThickness_of_vonKarman {α β μ ρ U : ℝ} {δ : ℝ → ℝ} (hα : α ≠ 0) (hρ : ρ ≠ 0)
    (hU : U ≠ 0) (hd : ∀ x, 0 < x → DifferentiableAt ℝ δ x)
    (hvk : ∀ x, 0 < x → α * deriv δ x = wallShear μ U β (δ x) / (ρ * U ^ 2))
    (hpos : ∀ x, 0 < x → 0 < δ x) (h0 : δ 0 = 0) (hc : ContinuousWithinAt δ (Ici 0) 0)
    {x : ℝ} (hx : 0 ≤ x) : δ x = blThickness (β / α * (μ / ρ) / U) x := by
  refine eq_blThickness_of_hasDerivAt (fun y hy => ?_) hpos h0 hc hx
  have h := (vonKarman_iff hα hρ hU (hpos y hy).ne').1 (hvk y hy)
  have hy' := (hpos y hy).ne'
  convert (hd y hy).hasDerivAt using 1
  rw [← h, mul_div_cancel_left₀ _ hy']

/-- **Similarity law** `δ/x = √(2β/α)/√Re_x` for `δ = √(2(β/α)νx/U)` and `Re_x = Ux/ν`. -/
theorem blThickness_div {α β ν U x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hν : 0 < ν) (hU : 0 < U)
    (hx : 0 < x) :
    blThickness (β / α * ν / U) x / x = √(2 * β / α) / √(U * x / ν) := by
  have hR : 0 < U * x / ν := by positivity
  have h : 2 * (β / α * ν / U) * x = 2 * β / α * x ^ 2 / (U * x / ν) := by
    field_simp
  rw [blThickness, h, Real.sqrt_div' _ hR.le, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hx.le]
  field_simp

end Integral

/-! ### Velocity profiles -/

section Profiles

/-- Integral of a function with an explicit antiderivative on `[0, 1]`. -/
theorem integral_unit_of_hasDerivAt {f F : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) : ∫ η in (0 : ℝ)..1, f η = F 1 - F 0 :=
  integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hf.intervalIntegrable _ _)

/-- Linear profile: `∫₀¹ η(1 - η) dη = 1/6`. -/
theorem momRatio_linear : momRatio id = 1 / 6 := by
  rw [momRatio, integral_unit_of_hasDerivAt (F := fun x => x ^ 2 / 2 - x ^ 3 / 3)
    (fun x => by
      refine (((hasDerivAt_pow 2 x).div_const 2).sub
        ((hasDerivAt_pow 3 x).div_const 3)).congr_deriv ?_
      simp only [id]; push_cast; ring) (by fun_prop)]
  norm_num

/-- Linear profile: `2β/α = 12` for `α = 1/6`, `β = 1`, so `δ/x = √12/√Re_x`. -/
theorem linear_coeff : 2 * 1 / momRatio id = 12 := by rw [momRatio_linear]; norm_num

/-- `3.46 < √12 < 3.47`. -/
theorem sqrt_twelve_bounds : 3.46 < √(12 : ℝ) ∧ √(12 : ℝ) < 3.47 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The **Pohlhausen cubic profile** `f(η) = (3/2)η - (1/2)η³`. -/
def pohlhausen (η : ℝ) : ℝ := 3 / 2 * η - 1 / 2 * η ^ 3

/-- The derivative of the Pohlhausen profile: `f'(η) = 3/2 - (3/2)η²`. -/
theorem hasDerivAt_pohlhausen (η : ℝ) :
    HasDerivAt pohlhausen (3 / 2 - 3 / 2 * η ^ 2) η := by
  convert ((hasDerivAt_id η).const_mul (3 / 2)).sub ((hasDerivAt_pow 3 η).const_mul (1 / 2))
    using 1
  · ext; simp [pohlhausen]
  · simp; ring

/-- The second derivative of the Pohlhausen profile: `f''(η) = -3η`. -/
theorem hasDerivAt_pohlhausen_deriv (η : ℝ) :
    HasDerivAt (fun η : ℝ => 3 / 2 - 3 / 2 * η ^ 2) (-3 * η) η := by
  convert ((hasDerivAt_pow 2 η).const_mul (3 / 2)).const_sub (3 / 2) using 1
  simp; ring

/-- No slip and matching to the free stream: `f(0) = 0`, `f(1) = 1`. -/
theorem pohlhausen_zero_one : pohlhausen 0 = 0 ∧ pohlhausen 1 = 1 := by
  constructor <;> norm_num [pohlhausen]

/-- Smooth matching `f'(1) = 0`, wall slope `β = f'(0) = 3/2`, and `f''(0) = 0` (zero pressure
gradient at the wall). -/
theorem pohlhausen_conditions :
    deriv pohlhausen 1 = 0 ∧ deriv pohlhausen 0 = 3 / 2 ∧
      deriv (deriv pohlhausen) 0 = 0 := by
  have hd : deriv pohlhausen = fun η : ℝ => 3 / 2 - 3 / 2 * η ^ 2 :=
    funext fun η => (hasDerivAt_pohlhausen η).deriv
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; norm_num
  · rw [hd]; norm_num
  · rw [hd, (hasDerivAt_pohlhausen_deriv 0).deriv]; norm_num

/-- Pohlhausen: `α = θ/δ = ∫₀¹ f(1 - f) = 39/280`. -/
theorem momRatio_pohlhausen : momRatio pohlhausen = 39 / 280 := by
  rw [momRatio, integral_unit_of_hasDerivAt (F := fun x => 3 / 4 * x ^ 2 - 3 / 4 * x ^ 3
      - 1 / 8 * x ^ 4 + 3 / 10 * x ^ 5 - 1 / 28 * x ^ 7)
    (fun x => by
      have := (((((hasDerivAt_pow 2 x).const_mul (3 / 4)).sub
        ((hasDerivAt_pow 3 x).const_mul (3 / 4))).sub
        ((hasDerivAt_pow 4 x).const_mul (1 / 8))).add
        ((hasDerivAt_pow 5 x).const_mul (3 / 10))).sub
        ((hasDerivAt_pow 7 x).const_mul (1 / 28))
      refine this.congr_deriv ?_
      simp only [pohlhausen]; push_cast; ring) (by unfold pohlhausen; fun_prop)]
  norm_num

/-- Pohlhausen: `δ*/δ = ∫₀¹ (1 - f) = 3/8`. -/
theorem dispRatio_pohlhausen : dispRatio pohlhausen = 3 / 8 := by
  rw [dispRatio, integral_unit_of_hasDerivAt (F := fun x => x - 3 / 4 * x ^ 2 + 1 / 8 * x ^ 4)
    (fun x => by
      have := ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).const_mul (3 / 4))).add
        ((hasDerivAt_pow 4 x).const_mul (1 / 8))
      refine this.congr_deriv ?_
      simp only [pohlhausen]; push_cast; ring) (by unfold pohlhausen; fun_prop)]
  norm_num

/-- Pohlhausen: `2β/α = 2 (3/2)/(39/280) = 280/13`, so `δ/x = √(280/13)/√Re_x`. -/
theorem pohlhausen_coeff : 2 * deriv pohlhausen 0 / momRatio pohlhausen = 280 / 13 := by
  rw [pohlhausen_conditions.2.1, momRatio_pohlhausen]; norm_num

/-- Pohlhausen thickness: `δ/x = √(280/13)/√Re_x`. -/
theorem pohlhausen_thickness {ν U x : ℝ} (hν : 0 < ν) (hU : 0 < U) (hx : 0 < x) :
    blThickness (deriv pohlhausen 0 / momRatio pohlhausen * ν / U) x / x =
      √(280 / 13) / √(U * x / ν) := by
  rw [blThickness_div (by rw [momRatio_pohlhausen]; norm_num)
    (by rw [pohlhausen_conditions.2.1]; norm_num) hν hU hx, pohlhausen_coeff]

/-- `4.64 < √(280/13) < 4.65`. -/
theorem sqrt_pohlhausen_bounds : 4.64 < √(280 / 13 : ℝ) ∧ √(280 / 13 : ℝ) < 4.65 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The **sine profile** `f(η) = sin(πη/2)`. -/
def sineProfile (η : ℝ) : ℝ := sin (π * η / 2)

/-- The wall slope of the sine profile: `β = f'(0) = π/2`. -/
theorem hasDerivAt_sineProfile_zero : HasDerivAt sineProfile (π / 2) 0 := by
  have h : HasDerivAt (fun η : ℝ => π * η / 2) (π / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul π).div_const 2
  exact h.sin.congr_deriv (by simp)

/-- Sine profile: `α = ∫₀¹ f(1 - f) = (4 - π)/(2π)`. -/
theorem momRatio_sine : momRatio sineProfile = (4 - π) / (2 * π) := by
  have hπ := Real.pi_pos.ne'
  rw [momRatio, integral_unit_of_hasDerivAt
    (F := fun x => -(2 / π) * cos (π * x / 2) - x / 2 + sin (π * x) / (2 * π))
    (fun x => by
      have h1 : HasDerivAt (fun x : ℝ => π * x / 2) (π / 2) x := by
        simpa using ((hasDerivAt_id x).const_mul π).div_const 2
      have h2 : HasDerivAt (fun x : ℝ => π * x) π x := by
        simpa using (hasDerivAt_id x).const_mul π
      have := ((h1.cos.const_mul (-(2 / π))).sub ((hasDerivAt_id x).div_const 2)).add
        (h2.sin.div_const (2 * π))
      refine this.congr_deriv ?_
      have hc : cos (π * x) = 1 - 2 * sin (π * x / 2) ^ 2 := by
        have h := cos_two_mul (π * x / 2)
        rw [show 2 * (π * x / 2) = π * x by ring] at h
        rw [h, cos_sq']; ring
      simp only [sineProfile, hc]
      field_simp
      ring) (by unfold sineProfile; fun_prop)]
  simp
  field_simp
  ring

/-- Sine profile: `2β/α = 2π²/(4 - π)`. -/
theorem sine_coeff : 2 * (π / 2) / momRatio sineProfile = 2 * π ^ 2 / (4 - π) := by
  have hπ := Real.pi_pos.ne'
  have h4 : 4 - π ≠ 0 := by linarith [Real.pi_lt_d2]
  rw [momRatio_sine]; field_simp

/-- `4.79 < √(2π²/(4 - π)) < 4.80`. -/
theorem sqrt_sine_bounds : 4.79 < √(2 * π ^ 2 / (4 - π)) ∧ √(2 * π ^ 2 / (4 - π)) < 4.80 := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.pi_lt_d4
  have h4 : 0 < 4 - π := by linarith
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ h4]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ h4]; nlinarith

end Profiles

/-! ### Skin friction and drag -/

section Friction

/-- The **local skin-friction coefficient** `c_f = 2τ_w/(ρU²)`. -/
def skinFriction (ρ U τ : ℝ) : ℝ := 2 * τ / (ρ * U ^ 2)

/-- `c_f = 2βν/(Uδ)` with `ν = μ/ρ`. -/
theorem skinFriction_eq {ρ μ U β δ : ℝ} (hρ : ρ ≠ 0) (hU : U ≠ 0) :
    skinFriction ρ U (wallShear μ U β δ) = 2 * β * (μ / ρ) / (U * δ) := by
  unfold skinFriction wallShear
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp
  field_simp

/-- **Skin-friction law** `c_f √Re_x = √(2αβ)` for the momentum-integral thickness. -/
theorem skinFriction_mul_sqrt_reynolds {α β ν U x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hν : 0 < ν)
    (hU : 0 < U) (hx : 0 < x) :
    2 * β * ν / (U * blThickness (β / α * ν / U) x) * √(U * x / ν) = √(2 * α * β) := by
  have hδ := blThickness_div hα hβ hν hU hx
  have hR : 0 < √(U * x / ν) := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < √(2 * β / α) := Real.sqrt_pos.2 (by positivity)
  have hδ' : blThickness (β / α * ν / U) x = x * √(2 * β / α) / √(U * x / ν) := by
    rw [div_eq_iff hx.ne'] at hδ; rw [hδ]; ring
  have hRsq : √(U * x / ν) ^ 2 = U * x / ν := Real.sq_sqrt (by positivity)
  have hprod : √(2 * α * β) * √(2 * β / α) = 2 * β := by
    rw [← Real.sqrt_mul (by positivity), show 2 * α * β * (2 * β / α) = (2 * β) ^ 2 by
      field_simp, Real.sqrt_sq (by positivity)]
  have hl : 2 * β * ν / (U * (x * √(2 * β / α) / √(U * x / ν))) * √(U * x / ν) =
      2 * β / √(2 * β / α) := by
    field_simp
    rw [hRsq]
    field_simp
  rw [hδ', hl, div_eq_iff hs.ne', hprod]

/-- Pohlhausen: `c_f √Re_x = √(2αβ) = √(117/280)`. -/
theorem pohlhausen_skinFriction :
    √(2 * momRatio pohlhausen * deriv pohlhausen 0) = √(117 / 280) := by
  rw [momRatio_pohlhausen, pohlhausen_conditions.2.1]; norm_num

/-- `0.646 < √(117/280) < 0.647`, slightly below the Blasius value `0.664`. -/
theorem sqrt_pohlhausen_skin_bounds :
    0.646 < √(117 / 280 : ℝ) ∧ √(117 / 280 : ℝ) < 0.647 ∧ √(117 / 280 : ℝ) < 0.664 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `∫₀ᴸ x^{-1/2} dx = 2√L`. -/
theorem integral_inv_sqrt (L : ℝ) :
    ∫ x in (0 : ℝ)..L, x ^ (-(1 / 2 : ℝ)) = 2 * √L := by
  rw [integral_rpow (Or.inl (by norm_num)), Real.sqrt_eq_rpow]
  norm_num
  ring

/-- **Drag coefficient** `C_D = (1/L) ∫₀ᴸ c_f dx = 2 c_f(L)` for a local skin friction
`c_f(x) = K/√Re_x`, `Re_x = Ux/ν`. -/
theorem dragCoeff_eq {K ν U L : ℝ} (hν : 0 < ν) (hU : 0 < U) (hL : 0 < L) :
    (1 / L) * ∫ x in (0 : ℝ)..L, K / √(U * x / ν) = 2 * (K / √(U * L / ν)) := by
  have hc : 0 < √(U / ν) := Real.sqrt_pos.2 (by positivity)
  have hcongr : EqOn (fun x => K / √(U * x / ν))
      (fun x => K * (√(U / ν))⁻¹ * x ^ (-(1 / 2 : ℝ))) (uIcc 0 L) := by
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    simp only
    rw [Real.rpow_neg hx.1, ← Real.sqrt_eq_rpow, mul_div_right_comm,
      Real.sqrt_mul (by positivity), mul_comm (√(U / ν))]
    · rw [div_mul_eq_div_div]; field_simp
  rw [integral_congr hcongr, intervalIntegral.integral_const_mul, integral_inv_sqrt,
    mul_div_right_comm U, Real.sqrt_mul (by positivity) L]
  have hsL : 0 < √L := Real.sqrt_pos.2 hL
  have hLsq : √L ^ 2 = L := Real.sq_sqrt hL.le
  field_simp
  rw [hLsq]
  ring

/-- Pohlhausen displacement thickness: `δ*/x = (3/8)√(280/13)/√Re_x`. -/
theorem pohlhausen_displacement {ν U x : ℝ} (hν : 0 < ν) (hU : 0 < U) (hx : 0 < x) :
    dispRatio pohlhausen *
        blThickness (deriv pohlhausen 0 / momRatio pohlhausen * ν / U) x / x =
      3 / 8 * √(280 / 13) / √(U * x / ν) := by
  rw [mul_div_assoc (dispRatio _), pohlhausen_thickness hν hU hx, dispRatio_pohlhausen]
  ring

/-- `1.74 < (3/8)√(280/13) < 1.75`. -/
theorem pohlhausen_displacement_bounds :
    1.74 < 3 / 8 * √(280 / 13 : ℝ) ∧ 3 / 8 * √(280 / 13 : ℝ) < 1.75 := by
  obtain ⟨h1, h2⟩ := sqrt_pohlhausen_bounds
  constructor <;> linarith

end Friction

end ContinuumMechanics.Fluids.BoundaryLayer
