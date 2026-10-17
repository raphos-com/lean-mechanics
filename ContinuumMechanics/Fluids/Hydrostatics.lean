import ContinuumMechanics.Fluids.Ideal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Hydrostatics, buoyancy and floating stability

A fluid of constant density `ρ` at rest in the gravity field `g = (0, 0, -g)` of `ℝ³`
(coordinates `x 0, x 1, x 2 = x, y, z`, `z` pointing up).

* **Hydrostatic equilibrium** (`IsHydrostatic`): `∇p = ρ g`. The linear pressure
  `p = p₀ - ρ g z` (`hydroPressure`) is a solution, it is the rest state of the steady Euler
  equations with potential `Φ = g z` (`isSteadyEuler_rest`), and every differentiable solution is
  of this form (`IsHydrostatic.eq_hydroPressure`, `isHydrostatic_iff`).
* **Submerged plane gate**: a vertical rectangular gate of width `b` between depths `h₁ < h₂`
  carries the resultant `F = ∫ ρ g h b dh = ρ g b (h₂² - h₁²)/2 = ρ g h_c A` (`gateForce_eq`,
  `gateForce_eq_centroid`); its **centre of pressure** lies at depth
  `h_p = ∫ h² / ∫ h = h_c + I_c/(h_c A)` with `I_c = b (h₂ - h₁)³/12`
  (`centreOfPressure_eq`, `gateSecondMoment_eq_integral`), strictly below the centroid.
* **Archimedes' principle for a box** `[x₁, x₂] × [y₁, y₂] × [z₁, z₂]`: the pressure forces on
  opposite faces, integrated over the faces, give a net vertical force `ρ g V` and vanishing
  horizontal resultants (`archimedes_box`, `forceX_hydro`, `forceY_hydro`). For an arbitrary `C¹`
  pressure field the net vertical face force is `-∫∫∫ ∂_z p` (the vertical part of the
  divergence theorem, by the fundamental theorem of calculus on each vertical column,
  `forceZ_eq_integral_pd`).
* **Box barge** of length `ℓ`, beam `B`, depth `H` and density ratio `s = ρ_body/ρ_water`:
  equilibrium draft `d = s H` (`buoyancy_eq_weight_iff`); `KB = d/2`, `KG = H/2`,
  `BM = I/V = B²/(12 d)` (`bm_eq`); **metacentric height** `GM = KB + BM - KG`, and the barge is
  initially stable (`GM > 0`) iff `B/H > √(6 s (1 - s))` (`stable_iff`). The heeled section
  (wall-sided, waterline through the centre) is integrated explicitly: displacement is kept
  (`heelArea_eq`), the centre of buoyancy moves to `(BM tan φ, KB + BM tan² φ / 2)`, and the
  righting arm is the **wall-sided formula** `GZ = sin φ (GM + BM tan² φ / 2)` (`gz_eq_wallSided`),
  so `GZ = GM sin φ` to first order (`hasDerivAt_gz`, `gz_sub_gzSmall`).

## Main results

* `isHydrostatic_iff`: differentiable `p` solves `∇p = ρ g` iff `p = c - ρ g z`.
* `gateForce_eq_centroid`, `centreOfPressure_eq`: force and centre of pressure on a gate.
* `archimedes_box`, `forceX_hydro`, `forceY_hydro`, `forceZ_eq_integral_pd`: Archimedes.
* `buoyancy_eq_weight_iff`, `metacentricHeight_eq`, `stable_iff`: floating box barge.
* `gz_eq_wallSided`, `hasDerivAt_gz`: righting arm of the heeled barge.

## References

* [White2011] F. M. White, *Fluid Mechanics*, 7th ed., §§2.3–2.8.
* [Rawson2001] K. J. Rawson, E. C. Tupper, *Basic Ship Theory*, 5th ed., Ch. 4.
* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §1.4.
-/

open MeasureTheory Real

noncomputable section

namespace ContinuumMechanics.Fluids.Hydrostatics

open Korn ContinuumMechanics.Fluids

/-! ### Hydrostatic pressure -/

section Pressure

/-- The gravitational acceleration `(0, 0, -g)` of `ℝ³`. -/
def gravity (g : ℝ) : Fin 3 → ℝ := ![0, 0, -g]

/-- **Hydrostatic equilibrium** `∇p = ρ g` of a fluid of density `ρ` at rest. -/
def IsHydrostatic (ρ g : ℝ) (p : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ x, grad p x = ρ • gravity g

/-- The hydrostatic pressure `p = p₀ - ρ g z`. -/
def hydroPressure (p₀ ρ g : ℝ) (x : Fin 3 → ℝ) : ℝ := p₀ - ρ * g * x 2

/-- The Fréchet derivative of the hydrostatic pressure is `-ρ g dz`. -/
theorem hasFDerivAt_hydroPressure (p₀ ρ g : ℝ) (x : Fin 3 → ℝ) :
    HasFDerivAt (hydroPressure p₀ ρ g) (-((ρ * g) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) 2)) x :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt
    (x := x)).const_mul (ρ * g) |>.const_sub p₀

/-- The hydrostatic pressure is differentiable. -/
theorem differentiable_hydroPressure (p₀ ρ g : ℝ) : Differentiable ℝ (hydroPressure p₀ ρ g) :=
  fun x => (hasFDerivAt_hydroPressure p₀ ρ g x).differentiableAt

/-- Partial derivatives of the hydrostatic pressure: `∂ₓp = ∂_yp = 0`, `∂_zp = -ρ g`. -/
theorem pd_hydroPressure (p₀ ρ g : ℝ) (x : Fin 3 → ℝ) (j : Fin 3) :
    pd (hydroPressure p₀ ρ g) j x = if j = 2 then -(ρ * g) else 0 := by
  rw [pd_eq (hasFDerivAt_hydroPressure p₀ ρ g x)]
  fin_cases j <;> simp

/-- `∇(p₀ - ρ g z) = ρ g`. -/
theorem grad_hydroPressure (p₀ ρ g : ℝ) (x : Fin 3 → ℝ) :
    grad (hydroPressure p₀ ρ g) x = ρ • gravity g := by
  funext j
  simp only [grad, pd_hydroPressure, gravity, Pi.smul_apply, smul_eq_mul]
  fin_cases j <;> simp

/-- `p = p₀ - ρ g z` is in hydrostatic equilibrium. -/
theorem isHydrostatic_hydroPressure (p₀ ρ g : ℝ) :
    IsHydrostatic ρ g (hydroPressure p₀ ρ g) :=
  grad_hydroPressure p₀ ρ g

/-- The pressure increases linearly with depth: `p(x) = p(y) + ρ g (y_z - x_z)`. -/
theorem hydroPressure_sub (p₀ ρ g : ℝ) (x y : Fin 3 → ℝ) :
    hydroPressure p₀ ρ g x = hydroPressure p₀ ρ g y + ρ * g * (y 2 - x 2) := by
  simp only [hydroPressure]; ring

/-- **Uniqueness**: a differentiable pressure in hydrostatic equilibrium is
`p = p(0) - ρ g z`. -/
theorem IsHydrostatic.eq_hydroPressure {ρ g : ℝ} {p : (Fin 3 → ℝ) → ℝ}
    (h : IsHydrostatic ρ g p) (hp : Differentiable ℝ p) :
    p = hydroPressure (p 0) ρ g := by
  set q : (Fin 3 → ℝ) → ℝ := fun x => p x - hydroPressure (p 0) ρ g x with hq_def
  have hq : Differentiable ℝ q := hp.sub (differentiable_hydroPressure _ _ _)
  have hq' : ∀ x, fderiv ℝ q x = 0 := by
    intro x
    apply fderiv_eq_zero_of_grad
    funext j
    have hfd : fderiv ℝ q x = fderiv ℝ p x - fderiv ℝ (hydroPressure (p 0) ρ g) x :=
      fderiv_sub (hp x) (differentiable_hydroPressure _ _ _ x)
    have e1 := congrFun (h x) j
    have e2 := congrFun (grad_hydroPressure (p 0) ρ g x) j
    simp only [grad, pd] at e1 e2 ⊢
    rw [hfd, sub_apply, e1, e2, sub_self, Pi.zero_apply]
  funext x
  have := is_const_of_fderiv_eq_zero hq hq' x 0
  simp only [hq_def, hydroPressure, Pi.zero_apply, mul_zero, sub_zero, sub_self] at this
  simp only [hydroPressure]
  linarith

/-- Differentiable solutions of `∇p = ρ g` are exactly the pressures `c - ρ g z`. -/
theorem isHydrostatic_iff {ρ g : ℝ} {p : (Fin 3 → ℝ) → ℝ} (hp : Differentiable ℝ p) :
    IsHydrostatic ρ g p ↔ ∃ c, p = hydroPressure c ρ g :=
  ⟨fun h => ⟨p 0, h.eq_hydroPressure hp⟩, fun ⟨c, hc⟩ => hc ▸ isHydrostatic_hydroPressure c ρ g⟩

/-- The gravitational potential `Φ = g z`. -/
def gravPotential (g : ℝ) (x : Fin 3 → ℝ) : ℝ := g * x 2

/-- `∇(g z) = -g`. -/
theorem grad_gravPotential (g : ℝ) (x : Fin 3 → ℝ) : grad (gravPotential g) x = -gravity g := by
  have hΦ : HasFDerivAt (gravPotential g) (g • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) 2) x :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt
      (x := x)).const_mul g
  funext j
  simp only [grad, pd_eq hΦ, gravity]
  fin_cases j <;> simp

/-- The hydrostatic state `v = 0`, `p = p₀ - ρ g z` solves the steady Euler equations with
gravitational potential `Φ = g z`. -/
theorem isSteadyEuler_rest (p₀ ρ g : ℝ) :
    IsSteadyEuler ρ 0 (hydroPressure p₀ ρ g) (gravPotential g) where
  momentum x := by
    have hc : convect (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) x = 0 := by
      funext i; simp [convect]
    rw [hc, grad_hydroPressure, grad_gravPotential, smul_zero, smul_neg]
    abel
  incompressible x := by
    simp [divergence, pd]

end Pressure

/-! ### Force on a submerged vertical gate -/

section Gate

/-- `∫ₐᵇ (c₀ + c₁ x + c₂ x²) dx`. -/
theorem integral_quad (c₀ c₁ c₂ a b : ℝ) :
    ∫ x in a..b, (c₀ + c₁ * x + c₂ * x ^ 2) =
      c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 + c₂ * (b ^ 3 - a ^ 3) / 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => c₀ * x + c₁ * x ^ 2 / 2 + c₂ * x ^ 3 / 3)]
  · ring
  · intro x _
    have := (((hasDerivAt_id x).const_mul c₀).add
      (((hasDerivAt_id x).pow 2).const_mul c₁ |>.div_const 2)).add
      (((hasDerivAt_id x).pow 3).const_mul c₂ |>.div_const 3)
    convert this using 1
    · funext y; simp
    · simp; ring
  · exact (by fun_prop : Continuous fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2).intervalIntegrable _ _

variable (ρ g b h₁ h₂ : ℝ)

/-- The resultant pressure force `F = ∫_{h₁}^{h₂} ρ g h b dh` on a vertical rectangular gate of
width `b` between depths `h₁` and `h₂` (gauge pressure `ρ g h`). -/
def gateForce : ℝ := ∫ h in h₁..h₂, ρ * g * h * b

/-- The moment `∫_{h₁}^{h₂} (ρ g h b) h dh` of the pressure force about the free surface. -/
def gateMoment : ℝ := ∫ h in h₁..h₂, ρ * g * h * b * h

/-- The depth `h_c = (h₁ + h₂)/2` of the centroid of the gate. -/
def gateCentroid : ℝ := (h₁ + h₂) / 2

/-- The area `A = b (h₂ - h₁)` of the gate. -/
def gateArea : ℝ := b * (h₂ - h₁)

/-- The second moment of area `I_c = b (h₂ - h₁)³/12` about the horizontal centroidal axis. -/
def gateSecondMoment : ℝ := b * (h₂ - h₁) ^ 3 / 12

/-- The depth of the **centre of pressure** `h_p = ∫ p h dA / ∫ p dA`. -/
def centreOfPressure : ℝ := gateMoment ρ g b h₁ h₂ / gateForce ρ g b h₁ h₂

/-- `F = ρ g b (h₂² - h₁²)/2`. -/
theorem gateForce_eq : gateForce ρ g b h₁ h₂ = ρ * g * b * (h₂ ^ 2 - h₁ ^ 2) / 2 := by
  have : (fun h : ℝ => ρ * g * h * b) = fun h => 0 + (ρ * g * b) * h + 0 * h ^ 2 := by
    funext h; ring
  rw [gateForce, this, integral_quad]; ring

/-- `F = ρ g h_c A`: the force equals the pressure at the centroid times the area. -/
theorem gateForce_eq_centroid :
    gateForce ρ g b h₁ h₂ = ρ * g * gateCentroid h₁ h₂ * gateArea b h₁ h₂ := by
  rw [gateForce_eq, gateCentroid, gateArea]; ring

/-- `∫ (ρ g h b) h dh = ρ g b (h₂³ - h₁³)/3`. -/
theorem gateMoment_eq : gateMoment ρ g b h₁ h₂ = ρ * g * b * (h₂ ^ 3 - h₁ ^ 3) / 3 := by
  have : (fun h : ℝ => ρ * g * h * b * h) = fun h => 0 + 0 * h + (ρ * g * b) * h ^ 2 := by
    funext h; ring
  rw [gateMoment, this, integral_quad]; ring

/-- `I_c = ∫_{h₁}^{h₂} (h - h_c)² b dh`. -/
theorem gateSecondMoment_eq_integral :
    gateSecondMoment b h₁ h₂ = ∫ h in h₁..h₂, (h - gateCentroid h₁ h₂) ^ 2 * b := by
  have : (fun h : ℝ => (h - gateCentroid h₁ h₂) ^ 2 * b) = fun h =>
      gateCentroid h₁ h₂ ^ 2 * b + (-2 * gateCentroid h₁ h₂ * b) * h + b * h ^ 2 := by
    funext h; ring
  rw [this, integral_quad, gateSecondMoment, gateCentroid]; ring

variable {ρ g b h₁ h₂}

/-- **Centre of pressure** of a vertical rectangular gate:
`h_p = h_c + I_c / (h_c A)`. -/
theorem centreOfPressure_eq (hρg : ρ * g ≠ 0) (hb : b ≠ 0) (h₀ : 0 ≤ h₁) (h₁₂ : h₁ < h₂) :
    centreOfPressure ρ g b h₁ h₂ = gateCentroid h₁ h₂ +
      gateSecondMoment b h₁ h₂ / (gateCentroid h₁ h₂ * gateArea b h₁ h₂) := by
  have hρ : ρ ≠ 0 := left_ne_zero_of_mul hρg
  have hg : g ≠ 0 := right_ne_zero_of_mul hρg
  have hs : h₂ - h₁ ≠ 0 := by linarith
  have ha : h₁ + h₂ ≠ 0 := by linarith
  have hd : h₂ ^ 2 - h₁ ^ 2 ≠ 0 := by
    rw [show h₂ ^ 2 - h₁ ^ 2 = (h₂ - h₁) * (h₁ + h₂) by ring]; exact mul_ne_zero hs ha
  rw [centreOfPressure, gateMoment_eq, gateForce_eq, gateCentroid, gateSecondMoment, gateArea]
  field_simp
  ring

/-- The centre of pressure lies strictly below the centroid. -/
theorem gateCentroid_lt_centreOfPressure (hρg : ρ * g ≠ 0) (hb : 0 < b) (h₀ : 0 ≤ h₁)
    (h₁₂ : h₁ < h₂) : gateCentroid h₁ h₂ < centreOfPressure ρ g b h₁ h₂ := by
  rw [centreOfPressure_eq hρg hb.ne' h₀ h₁₂, lt_add_iff_pos_right]
  have hs : 0 < h₂ - h₁ := by linarith
  apply div_pos
  · unfold gateSecondMoment; positivity
  · unfold gateCentroid gateArea
    have : 0 < (h₁ + h₂) / 2 := by linarith
    positivity

end Gate

/-! ### Archimedes' principle for a box -/

section Box

variable (p : (Fin 3 → ℝ) → ℝ) (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ)

/-- Net vertical pressure force on the box `[x₁, x₂] × [y₁, y₂] × [z₁, z₂]`: the pressure on the
bottom face `z = z₁` pushes up, the pressure on the top face `z = z₂` pushes down. -/
def forceZ : ℝ := ∫ x in x₁..x₂, ∫ y in y₁..y₂, (p ![x, y, z₁] - p ![x, y, z₂])

/-- Net pressure force on the box in the `x`-direction (faces `x = x₁` and `x = x₂`). -/
def forceX : ℝ := ∫ y in y₁..y₂, ∫ z in z₁..z₂, (p ![x₁, y, z] - p ![x₂, y, z])

/-- Net pressure force on the box in the `y`-direction (faces `y = y₁` and `y = y₂`). -/
def forceY : ℝ := ∫ x in x₁..x₂, ∫ z in z₁..z₂, (p ![x, y₁, z] - p ![x, y₂, z])

/-- The volume `V = (x₂ - x₁)(y₂ - y₁)(z₂ - z₁)` of the box. -/
def boxVolume : ℝ := (x₂ - x₁) * (y₂ - y₁) * (z₂ - z₁)

/-- **Archimedes' principle** for a submerged box: the net vertical pressure force is the weight
`ρ g V` of the displaced fluid. -/
theorem archimedes_box (p₀ ρ g : ℝ) :
    forceZ (hydroPressure p₀ ρ g) x₁ x₂ y₁ y₂ z₁ z₂ = ρ * g * boxVolume x₁ x₂ y₁ y₂ z₁ z₂ := by
  simp only [forceZ, hydroPressure, Matrix.cons_val, intervalIntegral.integral_const,
    smul_eq_mul, boxVolume]
  ring

/-- The horizontal pressure resultant on a submerged box vanishes (`x`-direction). -/
theorem forceX_hydro (p₀ ρ g : ℝ) : forceX (hydroPressure p₀ ρ g) x₁ x₂ y₁ y₂ z₁ z₂ = 0 := by
  simp [forceX, hydroPressure]

/-- The horizontal pressure resultant on a submerged box vanishes (`y`-direction). -/
theorem forceY_hydro (p₀ ρ g : ℝ) : forceY (hydroPressure p₀ ρ g) x₁ x₂ y₁ y₂ z₁ z₂ = 0 := by
  simp [forceY, hydroPressure]

/-- Archimedes for any differentiable pressure field in hydrostatic equilibrium. -/
theorem IsHydrostatic.archimedes_box {ρ g : ℝ} {p : (Fin 3 → ℝ) → ℝ} (h : IsHydrostatic ρ g p)
    (hp : Differentiable ℝ p) :
    forceZ p x₁ x₂ y₁ y₂ z₁ z₂ = ρ * g * boxVolume x₁ x₂ y₁ y₂ z₁ z₂ ∧
      forceX p x₁ x₂ y₁ y₂ z₁ z₂ = 0 ∧ forceY p x₁ x₂ y₁ y₂ z₁ z₂ = 0 := by
  rw [h.eq_hydroPressure hp]
  exact ⟨Hydrostatics.archimedes_box .., forceX_hydro .., forceY_hydro ..⟩

/-- The vertical line `z ↦ (x, y, z)` has velocity `e₂`. -/
theorem hasDerivAt_vec3 (x y z : ℝ) :
    HasDerivAt (fun z : ℝ => (![x, y, z] : Fin 3 → ℝ)) (e 2) z := by
  have h := ((hasDerivAt_id z).smul_const (e 2 : Fin 3 → ℝ)).const_add ![x, y, 0]
  convert h using 1
  · funext w i
    fin_cases i <;> simp
  · simp

/-- **Vertical part of the divergence theorem** for the box: for a `C¹` pressure, the net
vertical face force equals `-∫∫∫ ∂_z p dV`. -/
theorem forceZ_eq_integral_pd {p : (Fin 3 → ℝ) → ℝ} (hp : ContDiff ℝ 1 p) :
    forceZ p x₁ x₂ y₁ y₂ z₁ z₂ =
      -∫ x in x₁..x₂, ∫ y in y₁..y₂, ∫ z in z₁..z₂, pd p 2 ![x, y, z] := by
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hd : ∀ z, HasDerivAt (fun z : ℝ => p ![x, y, z]) (pd p 2 ![x, y, z]) z := fun z =>
    ((hp.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt z (hasDerivAt_vec3 x y z)
  have hc : Continuous fun z : ℝ => pd p 2 ![x, y, z] := by
    have h1 : Continuous fun w => fderiv ℝ p w := hp.continuous_fderiv one_ne_zero
    have h2 : Continuous fun z : ℝ => (![x, y, z] : Fin 3 → ℝ) :=
      continuous_iff_continuousAt.2 fun z => (hasDerivAt_vec3 x y z).continuousAt
    exact ((h1.comp h2).clm_apply continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (hc.intervalIntegrable _ _)]
  ring

end Box

/-! ### Floating box barge and its stability -/

section Barge

variable (ρ g s ℓ B H d : ℝ)

/-- Weight `ρ_body g ℓ B H` of a uniform box barge with `ρ_body = s ρ`. -/
def bargeWeight : ℝ := s * ρ * g * (ℓ * B * H)

/-- Buoyancy `ρ g ℓ B d` at draft `d` (weight of the displaced water). -/
def buoyancy : ℝ := ρ * g * (ℓ * B * d)

/-- **Equilibrium draft**: buoyancy balances weight iff `d = s H`. -/
theorem buoyancy_eq_weight_iff (hρg : ρ * g ≠ 0) (hℓ : ℓ ≠ 0) (hB : B ≠ 0) :
    buoyancy ρ g ℓ B d = bargeWeight ρ g s ℓ B H ↔ d = s * H := by
  rw [buoyancy, bargeWeight, show s * ρ * g * (ℓ * B * H) = ρ * g * (ℓ * B * (s * H)) by ring]
  constructor
  · intro h
    exact mul_left_cancel₀ (mul_ne_zero hℓ hB) (mul_left_cancel₀ hρg h)
  · rintro rfl; rfl

/-- Height `KB = d/2` of the centre of buoyancy above the keel. -/
def kb : ℝ := d / 2

/-- Height `KG = H/2` of the centre of gravity above the keel. -/
def kg : ℝ := H / 2

/-- Second moment `I = ℓ B³/12` of the waterplane about the longitudinal centreline. -/
def waterplaneInertia : ℝ := ℓ * B ^ 3 / 12

/-- The displaced volume `V = ℓ B d`. -/
def displacedVolume : ℝ := ℓ * B * d

/-- Metacentric radius `BM = B²/(12 d)`. -/
def bm : ℝ := B ^ 2 / (12 * d)

/-- **Metacentric height** `GM = KB + BM - KG`. -/
def gm : ℝ := kb d + bm B d - kg H

/-- `BM = I/V`. -/
theorem bm_eq (hℓ : ℓ ≠ 0) (hB : B ≠ 0) :
    waterplaneInertia ℓ B / displacedVolume ℓ B d = bm B d := by
  rw [waterplaneInertia, displacedVolume, bm]
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · field_simp

/-- At the equilibrium draft `d = s H`: `GM = s H/2 + B²/(12 s H) - H/2`. -/
theorem metacentricHeight_eq :
    gm B H (s * H) = s * H / 2 + B ^ 2 / (12 * (s * H)) - H / 2 := rfl

/-- `12 s H · GM = B² - 6 s (1 - s) H²` at the equilibrium draft. -/
theorem gm_mul (hs : s ≠ 0) (hH : H ≠ 0) :
    12 * s * H * gm B H (s * H) = B ^ 2 - 6 * s * (1 - s) * H ^ 2 := by
  rw [metacentricHeight_eq]
  field_simp
  ring

/-- **Stability criterion** `GM > 0 ⇔ B²/(12 s H²) > (1 - s)/2`. -/
theorem stable_iff_ratio (hH : 0 < H) (hs : 0 < s) :
    0 < gm B H (s * H) ↔ (1 - s) / 2 < B ^ 2 / (12 * s * H ^ 2) := by
  have hk : 0 < 12 * s * H := by positivity
  rw [← mul_pos_iff_of_pos_left hk, gm_mul s B H hs.ne' hH.ne', sub_pos,
    lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- **Stability of a box barge**: for `0 < s < 1` the barge floats stably upright (`GM > 0`)
iff `B/H > √(6 s (1 - s))`. -/
theorem stable_iff (hB : 0 < B) (hH : 0 < H) (hs : 0 < s) :
    0 < gm B H (s * H) ↔ √(6 * s * (1 - s)) < B / H := by
  have hk : 0 < 12 * s * H := by positivity
  rw [← mul_pos_iff_of_pos_left hk, gm_mul s B H hs.ne' hH.ne', sub_pos,
    Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]

/-! #### The heeled barge: wall-sided formula -/

/-- Height of the waterline above the keel at transverse position `y` when heeled with
`t = tan φ`, the waterline turning about the centreline (wall-sided section, deck and bilge
neither immersed nor emerged: `|t| B/2 ≤ min d (H - d)`). -/
def heelHeight (t y : ℝ) : ℝ := d + y * t

/-- Submerged cross-section area `∫ (d + y t) dy` of the heeled barge. -/
def heelArea (t : ℝ) : ℝ := ∫ y in -B / 2..B / 2, heelHeight d t y

/-- First moment `∫ y (d + y t) dy` of the heeled section about the centreline. -/
def heelMomentY (t : ℝ) : ℝ := ∫ y in -B / 2..B / 2, y * heelHeight d t y

/-- First moment `∫ (d + y t)²/2 dy` of the heeled section about the keel. -/
def heelMomentZ (t : ℝ) : ℝ := ∫ y in -B / 2..B / 2, heelHeight d t y ^ 2 / 2

/-- Heeling preserves displacement: the heeled area is `B d`. -/
theorem heelArea_eq (t : ℝ) : heelArea B d t = B * d := by
  have : heelHeight d t = fun y => d + t * y + 0 * y ^ 2 := by funext y; rw [heelHeight]; ring
  rw [heelArea, this, integral_quad]; ring

/-- `∫ y (d + y t) dy = t B³/12`. -/
theorem heelMomentY_eq (t : ℝ) : heelMomentY B d t = t * B ^ 3 / 12 := by
  have : (fun y => y * heelHeight d t y) = fun y => 0 + d * y + t * y ^ 2 := by
    funext y; rw [heelHeight]; ring
  rw [heelMomentY, this, integral_quad]; ring

/-- `∫ (d + y t)²/2 dy = d² B/2 + t² B³/24`. -/
theorem heelMomentZ_eq (t : ℝ) : heelMomentZ B d t = d ^ 2 * B / 2 + t ^ 2 * B ^ 3 / 24 := by
  have : (fun y => heelHeight d t y ^ 2 / 2) = fun y =>
      d ^ 2 / 2 + (d * t) * y + (t ^ 2 / 2) * y ^ 2 := by
    funext y; rw [heelHeight]; ring
  rw [heelMomentZ, this, integral_quad]; ring

/-- Transverse coordinate of the centre of buoyancy of the heeled barge. -/
def yB (t : ℝ) : ℝ := heelMomentY B d t / heelArea B d t

/-- Height above the keel of the centre of buoyancy of the heeled barge. -/
def zB (t : ℝ) : ℝ := heelMomentZ B d t / heelArea B d t

variable {B d} in
/-- The centre of buoyancy moves out by `BM tan φ`. -/
theorem yB_eq (hB : B ≠ 0) (hd : d ≠ 0) (t : ℝ) : yB B d t = bm B d * t := by
  rw [yB, heelMomentY_eq, heelArea_eq, bm]; field_simp

variable {B d} in
/-- The centre of buoyancy rises to `KB + BM tan² φ / 2`. -/
theorem zB_eq (hB : B ≠ 0) (hd : d ≠ 0) (t : ℝ) : zB B d t = kb d + bm B d * t ^ 2 / 2 := by
  rw [zB, heelMomentZ_eq, heelArea_eq, kb, bm]; field_simp; ring

/-- The **righting arm** `GZ(φ)`: the horizontal distance from `G = (0, KG)` to the centre of
buoyancy of the section heeled by `φ`, measured along the rotated waterline. -/
def gz (φ : ℝ) : ℝ := yB B d (tan φ) * cos φ + (zB B d (tan φ) - kg H) * sin φ

/-- The small-angle righting arm `GM sin φ`. -/
def gzSmall (φ : ℝ) : ℝ := gm B H d * sin φ

/-- The righting moment `W · GZ(φ)` for a displacement weight `W`. -/
def rightingMoment (W φ : ℝ) : ℝ := W * gz B H d φ

variable {B d}

/-- Closed form of the righting arm. -/
theorem gz_eq (hB : B ≠ 0) (hd : d ≠ 0) (φ : ℝ) :
    gz B H d φ = bm B d * tan φ * cos φ + (kb d + bm B d * tan φ ^ 2 / 2 - kg H) * sin φ := by
  rw [gz, yB_eq hB hd, zB_eq hB hd]

/-- **Wall-sided formula** `GZ = sin φ (GM + BM tan² φ / 2)` (for `cos φ ≠ 0`). -/
theorem gz_eq_wallSided (hB : B ≠ 0) (hd : d ≠ 0) {φ : ℝ} (hφ : cos φ ≠ 0) :
    gz B H d φ = sin φ * (gm B H d + bm B d / 2 * tan φ ^ 2) := by
  rw [gz_eq H hB hd, mul_assoc, tan_mul_cos hφ, gm]; ring

/-- The correction to the small-angle righting arm is `sin φ · BM tan² φ / 2`, of third
order in `φ`. -/
theorem gz_sub_gzSmall (hB : B ≠ 0) (hd : d ≠ 0) {φ : ℝ} (hφ : cos φ ≠ 0) :
    gz B H d φ - gzSmall B H d φ = sin φ * (bm B d / 2 * tan φ ^ 2) := by
  rw [gz_eq_wallSided H hB hd hφ, gzSmall]; ring

/-- **Initial stability**: `GZ'(0) = GM`, i.e. `GZ ≈ GM φ ≈ GM sin φ` for small heel. -/
theorem hasDerivAt_gz (hB : B ≠ 0) (hd : d ≠ 0) : HasDerivAt (gz B H d) (gm B H d) 0 := by
  have ht : HasDerivAt tan (1 / cos 0 ^ 2) 0 := Real.hasDerivAt_tan (by simp)
  have h := (((ht.const_mul (bm B d)).mul (hasDerivAt_cos 0))).add
    ((((ht.pow 2).const_mul (bm B d) |>.div_const 2).const_add (kb d) |>.sub_const (kg H)).mul
      (hasDerivAt_sin 0))
  rw [show gz B H d = _ from funext (gz_eq H hB hd)]
  convert h using 1
  simp [gm]
  ring

/-- The small-angle righting arm has the same slope `GM` at `φ = 0`. -/
theorem hasDerivAt_gzSmall : HasDerivAt (gzSmall B H d) (gm B H d) 0 := by
  have h := (hasDerivAt_sin 0).const_mul (gm B H d)
  rw [cos_zero, mul_one] at h
  exact h

end Barge

end ContinuumMechanics.Fluids.Hydrostatics
