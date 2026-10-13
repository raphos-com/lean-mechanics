import ContinuumMechanics.Fluids.Ideal
import ContinuumMechanics.Elastostatics.Torsion

/-!
# Viscous fluids: the incompressible Navier–Stokes equations and exact solutions

A Newtonian fluid of constant density `ρ` and dynamic viscosity `μ` has the **viscous stress**
`σ = -p I + 2μ D(v)`, `Dᵢⱼ = (∂ⱼvᵢ + ∂ᵢvⱼ)/2` the rate of strain. Balance of momentum
`ρ Dv/Dt = div σ + ρg` together with incompressibility gives the **incompressible Navier–Stokes
equations**

`ρ(∂ₜv + (v·∇)v) = -∇p + μΔv + ρg`,   `div v = 0`   (`IsNavierStokes`).

* **Viscous stress** (`divStress_viscStress`, `divStress_viscStress_of_incompressible`):
  `(div σ)ᵢ = -∂ᵢp + μΔvᵢ + μ∂ᵢ(div v)`, which is `-∇p + μΔv` for incompressible `C²` flows.
* **Plane Couette flow** (`couetteVel`): `v = (U y/h, 0, 0)` with constant pressure solves the
  steady equations, satisfies no slip on the plates `y = 0` (at rest) and `y = h` (moving with
  velocity `U`), and exerts the wall shear stress `σ₁₂ = μU/h`.
* **Plane Poiseuille flow** (`poiseuilleVel`): `v = (G/(2μ) y(h - y), 0, 0)` driven by the pressure
  `p = p₀ - G x`; the flow rate per unit width is `Q = G h³/(12μ)`.
* **Hagen–Poiseuille flow** (`hagenVel`): `v = (0, 0, G/(4μ)(R² - x² - y²))` in a circular pipe of
  radius `R`, `p = p₀ - G z`; the flow rate is `Q = π G R⁴/(8μ)` (computed in polar coordinates).
* **Viscous dissipation**: the pointwise identity `v·Δv = Δ(|v|²/2) - |∇v|²` and, for compactly
  supported `C²` fields, `∫ v·Δv = -∫ |∇v|²`, so the viscous force `μΔv` dissipates kinetic energy.

The plane flows are written in `ℝ³` with coordinates `x = x 0`, `y = x 1`, `z = x 2`.

## Main results

* `IsNavierStokes`, `IsSteadyNavierStokes`, `IsSteadyNavierStokes.isNavierStokes`.
* `divStress_viscStress_of_incompressible`: `div σ = -∇p + μΔv` when `div v = 0`.
* `IsNavierStokes.momentum_stress`: the Navier–Stokes equations in stress form
  `ρ Dv/Dt = div σ + ρg`.
* `couette_isSteadyNavierStokes`, `couette_wall`, `couette_shear`: plane Couette flow.
* `poiseuille_isSteadyNavierStokes`, `poiseuille_wall`, `poiseuille_flowRate`: plane Poiseuille
  flow, `Q = G h³/(12μ)`.
* `hagen_isSteadyNavierStokes`, `hagen_wall`, `hagen_flowRate`: Hagen–Poiseuille flow,
  `Q = π G R⁴/(8μ)`.
* `dot_vecLap`: `v·Δv = Δ(|v|²/2) - |∇v|²`.
* `integral_dot_vecLap`: `∫ v·Δv = -∫ |∇v|²` for compactly supported `C²` fields.

## References

* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §§3.3, 4.2, 4.3.
* [LandauLifshitz1987] L. D. Landau, E. M. Lifshitz, *Fluid Mechanics*, 2nd ed., §§15–17.
-/

open MeasureTheory Real

noncomputable section

namespace ContinuumMechanics.Fluids

open Korn

variable {n : ℕ}

/-! ### Calculus in `ℝⁿ` -/

section Calculus

variable {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}

/-- Sum rule for `∂ⱼ` at a point. -/
theorem pd_fun_add (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    pd (fun y => f y + g y) j x = pd f j x + pd g j x := by
  simp [pd, fderiv_fun_add hf hg]

/-- Constant multiples commute with `∂ⱼ`. -/
theorem pd_const_mul (c : ℝ) (hf : DifferentiableAt ℝ f x) (j : Fin n) :
    pd (fun y => c * f y) j x = c * pd f j x := by
  simp [pd, fderiv_const_mul hf]

/-- Product rule for `∂ⱼ` at a point. -/
theorem pd_fun_mul (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    pd (fun y => f y * g y) j x = pd f j x * g x + f x * pd g j x := by
  simp [pd, fderiv_fun_mul hf hg]
  ring

end Calculus

/-! ### The viscous stress and the Navier–Stokes equations -/

/-- The vector Laplacian `(Δu)ᵢ = Δuᵢ`. -/
def vecLap (u : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lap (fun y => u y i) x

/-- The **viscous (Newtonian) stress** `σᵢⱼ = -p δᵢⱼ + μ(∂ⱼvᵢ + ∂ᵢvⱼ) = -p δᵢⱼ + 2μ Dᵢⱼ`. -/
def viscStress (μ : ℝ) (p : (Fin n → ℝ) → ℝ) (u : (Fin n → ℝ) → Fin n → ℝ) (i j : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  -(if i = j then p x else 0) + μ * (pd (fun y => u y i) j x + pd (fun y => u y j) i x)

/-- The divergence `(div σ)ᵢ = Σⱼ ∂ⱼσᵢⱼ` of a tensor field. -/
def divStress (σ : Fin n → Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, pd (σ i j) j x

section Stress

variable {μ : ℝ} {p : (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → Fin n → ℝ}

/-- `Σⱼ ∂ⱼ(∂ⱼuᵢ + ∂ᵢuⱼ) = Δuᵢ + ∂ᵢ(div u)` for a `C²` field. -/
theorem sum_pd_sym (hu : ContDiff ℝ 2 u) (i : Fin n) (x : Fin n → ℝ) :
    ∑ j, pd (fun y => pd (fun y => u y i) j y + pd (fun y => u y j) i y) j x =
      lap (fun y => u y i) x + pd (divergence u) i x := by
  have hc : ∀ k, ContDiff ℝ 2 (fun y => u y k) := contDiff_pi.1 hu
  have hd : ∀ k l, Differentiable ℝ (pd (fun y => u y k) l) := fun k l =>
    (contDiff_pd (hc k) l).differentiable one_ne_zero
  have hdiv : divergence u = fun y => ∑ k, pd (fun y => u y k) k y := rfl
  rw [hdiv, pd_sum _ (fun k => hd k k), lap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pd_fun_add (hd i j x) (hd j i x), pd_pd_comm (hc j) i j]

/-- The **divergence of the viscous stress**: `(div σ)ᵢ = -∂ᵢp + μΔvᵢ + μ∂ᵢ(div v)`. -/
theorem divStress_viscStress (hp : Differentiable ℝ p) (hu : ContDiff ℝ 2 u) (x : Fin n → ℝ)
    (i : Fin n) :
    divStress (viscStress μ p u) x i =
      -pd p i x + μ * lap (fun y => u y i) x + μ * pd (divergence u) i x := by
  have hc : ∀ k, ContDiff ℝ 2 (fun y => u y k) := contDiff_pi.1 hu
  have hd : ∀ k l, Differentiable ℝ (pd (fun y => u y k) l) := fun k l =>
    (contDiff_pd (hc k) l).differentiable one_ne_zero
  have hite : ∀ j, pd (fun y => if i = j then p y else 0) j x =
      if i = j then pd p j x else 0 := fun j => by
    split_ifs <;> simp [pd]
  have hsplit : ∀ j, pd (viscStress μ p u i j) j x =
      -(if i = j then pd p j x else 0) +
        μ * pd (fun y => pd (fun y => u y i) j y + pd (fun y => u y j) i y) j x := fun j => by
    have h1 : DifferentiableAt ℝ (fun y => if i = j then p y else 0) x := by
      split_ifs
      · exact hp x
      · exact differentiableAt_const _
    have h2 : DifferentiableAt ℝ
        (fun y => pd (fun y => u y i) j y + pd (fun y => u y j) i y) x :=
      (hd i j x).add (hd j i x)
    change pd (fun y => -(if i = j then p y else 0) + μ * (pd (fun y => u y i) j y +
      pd (fun y => u y j) i y)) j x = _
    rw [pd_fun_add (f := fun y => -(if i = j then p y else 0))
      (g := fun y => μ * (pd (fun y => u y i) j y + pd (fun y => u y j) i y)) h1.neg
      (h2.const_mul μ), pd_const_mul μ h2, ← hite]
    simp [pd]
  simp only [divStress, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, sum_pd_sym hu]
  simp [Finset.sum_ite_eq]
  ring

/-- For an incompressible `C²` flow, `div σ = -∇p + μΔv`. -/
theorem divStress_viscStress_of_incompressible (hp : Differentiable ℝ p) (hu : ContDiff ℝ 2 u)
    (hdiv : ∀ y, divergence u y = 0) (x : Fin n → ℝ) :
    divStress (viscStress μ p u) x = -grad p x + μ • vecLap u x := by
  have h0 : divergence u = fun _ => 0 := funext hdiv
  ext i
  rw [divStress_viscStress hp hu, h0]
  simp [grad, vecLap, pd]

end Stress

/-- The **incompressible Navier–Stokes equations** with constant density `ρ`, viscosity `μ`,
velocity `v`, pressure `p` and body force (per unit mass) `g`:
`ρ(∂ₜv + (v·∇)v) = -∇p + μΔv + ρg` and `div v = 0`. -/
structure IsNavierStokes (ρ μ : ℝ) (v : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (p : ℝ → (Fin n → ℝ) → ℝ) (g : ℝ → (Fin n → ℝ) → Fin n → ℝ) : Prop where
  /-- Balance of linear momentum. -/
  momentum : ∀ t x, ρ • accel v t x = -grad (p t) x + μ • vecLap (v t) x + ρ • g t x
  /-- Incompressibility. -/
  incompressible : ∀ t x, divergence (v t) x = 0

/-- The **steady incompressible Navier–Stokes equations**:
`ρ(v·∇)v = -∇p + μΔv + ρg` and `div v = 0`. -/
structure IsSteadyNavierStokes (ρ μ : ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (p : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin n → ℝ) : Prop where
  /-- Balance of linear momentum. -/
  momentum : ∀ x, ρ • convect v x = -grad p x + μ • vecLap v x + ρ • g x
  /-- Incompressibility. -/
  incompressible : ∀ x, divergence v x = 0

/-- A steady solution is a (time-independent) solution of the Navier–Stokes equations. -/
theorem IsSteadyNavierStokes.isNavierStokes {ρ μ : ℝ} {v : (Fin n → ℝ) → Fin n → ℝ}
    {p : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → Fin n → ℝ} (h : IsSteadyNavierStokes ρ μ v p g) :
    IsNavierStokes ρ μ (fun _ => v) (fun _ => p) (fun _ => g) where
  momentum t x := by
    rw [accel_eq, ← h.momentum x]
    simp only [dt, deriv_const']
    rw [show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl, zero_add]
  incompressible _ x := h.incompressible x

/-- Without viscosity the Navier–Stokes equations reduce to the Euler equations. -/
theorem isNavierStokes_zero_iff {ρ : ℝ} {v : ℝ → (Fin n → ℝ) → Fin n → ℝ}
    {p : ℝ → (Fin n → ℝ) → ℝ} {g : ℝ → (Fin n → ℝ) → Fin n → ℝ} :
    IsNavierStokes ρ 0 v p g ↔ IsIncompressibleEuler ρ v p g := by
  constructor
  · intro h
    exact ⟨fun t x => by simpa using h.momentum t x, h.incompressible⟩
  · intro h
    exact ⟨fun t x => by simpa using h.momentum t x, h.incompressible⟩

/-- **Stress form** of the Navier–Stokes equations: for a `C²` velocity and a differentiable
pressure, `ρ Dv/Dt = div σ + ρg` with the viscous stress `σ = -pI + 2μD(v)`. -/
theorem IsNavierStokes.momentum_stress {ρ μ : ℝ} {v : ℝ → (Fin n → ℝ) → Fin n → ℝ}
    {p : ℝ → (Fin n → ℝ) → ℝ} {g : ℝ → (Fin n → ℝ) → Fin n → ℝ} (h : IsNavierStokes ρ μ v p g)
    (hv : ∀ t, ContDiff ℝ 2 (v t)) (hp : ∀ t, Differentiable ℝ (p t)) (t : ℝ)
    (x : Fin n → ℝ) :
    ρ • accel v t x = divStress (viscStress μ (p t) (v t)) x + ρ • g t x := by
  rw [divStress_viscStress_of_incompressible (hp t) (hv t) (h.incompressible t), h.momentum]

/-! ### Plane Couette flow -/


section Couette

open Torsion

variable {ρ μ U h p₀ : ℝ}

/-- **Plane Couette flow** `v = (U y/h, 0, 0)` between a plate at rest at `y = 0` and a plate
moving with velocity `U` at `y = h`. -/
def couetteVel (U h : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![U / h * x 1, 0, 0]

/-- The velocity gradient of Couette flow: `∂ⱼvᵢ = U/h` for `(i, j) = (1, 2)`, else `0`. -/
theorem couette_pd (i j : Fin 3) :
    pd (fun y => couetteVel U h y i) j = fun _ => if i = 0 ∧ j = 1 then U / h else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp (disch := fun_prop) [couetteVel, pd_mul, pd_const, pd_coord]

/-- Plane Couette flow with constant pressure solves the steady Navier–Stokes equations without
body force. -/
theorem couette_isSteadyNavierStokes :
    IsSteadyNavierStokes ρ μ (couetteVel U h) (fun _ => p₀) 0 where
  momentum x := by
    ext i
    fin_cases i <;> simp (disch := fun_prop) [convect, vecLap, lap, grad, couetteVel,
      pd_mul, pd_const, pd_coord]
  incompressible x := by
    simp [divergence, couette_pd, Fin.sum_univ_three]

/-- **No slip** for Couette flow: the fluid is at rest on `y = 0` and moves with the upper plate
on `y = h`. -/
theorem couette_wall (hh : h ≠ 0) (x : Fin 3 → ℝ) :
    (x 1 = 0 → couetteVel U h x = 0) ∧ (x 1 = h → couetteVel U h x = ![U, 0, 0]) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · ext i; fin_cases i <;> simp [couetteVel, hx]
  · ext i; fin_cases i <;> simp [couetteVel, hx, hh]

/-- The **shear stress** of Couette flow is uniform, `σ₁₂ = μU/h`; in particular this is the
wall shear stress on both plates. -/
theorem couette_shear (x : Fin 3 → ℝ) :
    viscStress μ (fun _ => p₀) (couetteVel U h) 0 1 x = μ * U / h := by
  simp [viscStress, couette_pd]
  ring

end Couette

/-! ### Plane Poiseuille flow -/

section Poiseuille

open Torsion

variable {ρ μ G h p₀ : ℝ}

/-- **Plane Poiseuille flow** `v = (G/(2μ) y(h - y), 0, 0)` between fixed plates `y = 0` and
`y = h`, driven by the pressure gradient `-G`. -/
def poiseuilleVel (μ G h : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![G / (2 * μ) * (x 1 * (h - x 1)), 0, 0]

/-- The pressure `p = p₀ - G x` of plane Poiseuille flow. -/
def poiseuillePres (G p₀ : ℝ) : (Fin 3 → ℝ) → ℝ := fun x => p₀ - G * x 0

/-- Plane Poiseuille flow solves the steady Navier–Stokes equations without body force. -/
theorem poiseuille_isSteadyNavierStokes (hμ : μ ≠ 0) :
    IsSteadyNavierStokes ρ μ (poiseuilleVel μ G h) (poiseuillePres G p₀) 0 where
  momentum x := by
    have hP : poiseuillePres G p₀ = fun x => p₀ - G * x 0 := rfl
    ext i
    fin_cases i <;>
      simp (disch := fun_prop) [convect, vecLap, lap, grad, poiseuilleVel, hP,
        Fin.sum_univ_three, pd_mul, pd_const, pd_coord, pd_sub', pd_add', pd_neg']
    field_simp
    ring
  incompressible x := by
    simp (disch := fun_prop) [divergence, poiseuilleVel, Fin.sum_univ_three, pd_mul, pd_const,
      pd_coord, pd_sub']

/-- **No slip** for plane Poiseuille flow on both plates `y = 0` and `y = h`. -/
theorem poiseuille_wall (x : Fin 3 → ℝ) (hx : x 1 = 0 ∨ x 1 = h) : poiseuilleVel μ G h x = 0 := by
  ext i
  rcases hx with hx | hx <;> fin_cases i <;> simp [poiseuilleVel, hx]

/-- The **flow rate per unit width** `Q = ∫₀ʰ v₁ dy` of a plane parallel flow. -/
def planeFlowRate (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (h : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..h, v ![0, y, 0] 0

/-- **Flow rate of plane Poiseuille flow**: `Q = G h³/(12μ)`. -/
theorem poiseuille_flowRate (hμ : μ ≠ 0) :
    planeFlowRate (poiseuilleVel μ G h) h = G * h ^ 3 / (12 * μ) := by
  have e : (fun y : ℝ => y * (h - y)) = fun y => h * y - y ^ 2 := by funext y; ring
  have hi : ∫ y in (0 : ℝ)..h, y * (h - y) = h ^ 3 / 6 := by
    have i1 : IntervalIntegrable (fun y : ℝ => h * y) volume 0 h :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun y : ℝ => y ^ 2) volume 0 h :=
      (continuous_pow 2).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      integral_id, integral_pow]
    ring
  simp only [planeFlowRate, poiseuilleVel, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [intervalIntegral.integral_const_mul, hi]
  field_simp
  ring

end Poiseuille

/-! ### Hagen–Poiseuille flow in a circular pipe -/

section Hagen

open Torsion

variable {ρ μ G R p₀ : ℝ}

/-- **Hagen–Poiseuille flow** `v = (0, 0, G/(4μ)(R² - x² - y²))` in a pipe of radius `R` along
the `z`-axis. -/
def hagenVel (μ G R : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, 0, G / (4 * μ) * (R ^ 2 - x 0 ^ 2 - x 1 ^ 2)]

/-- The pressure `p = p₀ - G z` of Hagen–Poiseuille flow. -/
def hagenPres (G p₀ : ℝ) : (Fin 3 → ℝ) → ℝ := fun x => p₀ - G * x 2

/-- Hagen–Poiseuille flow solves the steady Navier–Stokes equations without body force. -/
theorem hagen_isSteadyNavierStokes (hμ : μ ≠ 0) :
    IsSteadyNavierStokes ρ μ (hagenVel μ G R) (hagenPres G p₀) 0 where
  momentum x := by
    have hP : hagenPres G p₀ = fun x => p₀ - G * x 2 := rfl
    ext i
    fin_cases i <;>
      simp (disch := fun_prop) [convect, vecLap, lap, grad, hagenVel, hP,
        Fin.sum_univ_three, pd_mul, pd_const, pd_coord, pd_sub', pd_sq, pd_neg']
    field_simp
    ring
  incompressible x := by
    simp (disch := fun_prop) [divergence, hagenVel, Fin.sum_univ_three, pd_mul, pd_const,
      pd_coord, pd_sub', pd_sq]

/-- **No slip** on the pipe wall `x² + y² = R²`. -/
theorem hagen_wall {x : Fin 3 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = R ^ 2) : hagenVel μ G R x = 0 := by
  have h0 : R ^ 2 - x 0 ^ 2 - x 1 ^ 2 = 0 := by linarith
  ext i
  fin_cases i <;> simp [hagenVel, h0]

/-- The **flow rate** `Q = ∫∫_Ω v₃` through a cross-section `Ω` of the plane `z = 0`. -/
def flowRate (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (Ω : Set (ℝ × ℝ)) : ℝ := ∫ q in Ω, v (pt q) 2

/-- `∫∫_{disk R} (R² - x² - y²) = π R⁴/2`, computed in polar coordinates. -/
theorem integral_disk_paraboloid (hR : 0 ≤ R) :
    ∫ q in disk R, (R ^ 2 - q.1 ^ 2 - q.2 ^ 2) = π * R ^ 4 / 2 := by
  rw [← integral_indicator (measurableSet_disk R), ← integral_comp_polarCoord_symm]
  have key : ∀ q ∈ polarCoord.target, q.1 • (disk R).indicator
      (fun q => R ^ 2 - q.1 ^ 2 - q.2 ^ 2) (polarCoord.symm q) =
      (Set.Iic R).indicator (fun r => R ^ 2 * r - r ^ 3) q.1 * (fun _ => (1 : ℝ)) q.2 :=
    fun q hq => by
    have h1 : 0 < q.1 := hq.1
    have hs : (q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2 = q.1 ^ 2 := by
      have := sin_sq_add_cos_sq q.2
      linear_combination q.1 ^ 2 * this
    by_cases h : q.1 ≤ R
    · have hd : polarCoord.symm q ∈ disk R := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs]
        exact pow_le_pow_left₀ h1.le h 2
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem (Set.mem_Iic.mpr h)]
      simp only [polarCoord_symm_apply, smul_eq_mul]
      linear_combination (-q.1) * hs
    · have hd : polarCoord.symm q ∉ disk R := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs, not_le]
        exact pow_lt_pow_left₀ (lt_of_not_ge h) hR two_ne_zero
      rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (by simpa using h)]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key]
  have hp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    ((Set.Iic R).indicator (fun r => R ^ 2 * r - r ^ 3)) (fun _ => (1 : ℝ)) (Set.Ioi 0)
    (Set.Ioo (-π) π)
  rw [← Measure.volume_eq_prod] at hp
  change ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π, _ = _
  rw [hp, setIntegral_indicator measurableSet_Iic,
    Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hR]
  have i1 : IntervalIntegrable (fun r : ℝ => R ^ 2 * r) volume 0 R :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r ^ 3) volume 0 R :=
    (continuous_pow 3).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo]
  rw [max_eq_left (by linarith [pi_pos])]
  ring

/-- **Hagen–Poiseuille law**: the flow rate through the pipe is `Q = π G R⁴/(8μ)`. -/
theorem hagen_flowRate (hμ : μ ≠ 0) (hR : 0 ≤ R) :
    flowRate (hagenVel μ G R) (disk R) = π * G * R ^ 4 / (8 * μ) := by
  have h : ∀ q : ℝ × ℝ, hagenVel μ G R (pt q) 2 = G / (4 * μ) * (R ^ 2 - q.1 ^ 2 - q.2 ^ 2) :=
    fun q => by simp [hagenVel, pt]
  simp only [flowRate, h]
  rw [integral_const_mul, integral_disk_paraboloid hR]
  field_simp
  ring

end Hagen

/-! ### Viscous dissipation -/

section Dissipation

variable {v : (Fin n → ℝ) → Fin n → ℝ}

/-- The **dissipation identity** `v·Δv = Δ(|v|²/2) - |∇v|²` for a `C²` velocity field, where
`|∇v|² = Σᵢⱼ (∂ⱼvᵢ)²`. Hence `v·(μΔv) = μ div ∇(|v|²/2) - μ|∇v|²`. -/
theorem dot_vecLap (hv : ContDiff ℝ 2 v) (x : Fin n → ℝ) :
    v x ⬝ᵥ vecLap v x = lap (kinetic v) x - gradSq (fun i y => v y i) x := by
  have hc : ∀ k, ContDiff ℝ 2 (fun y => v y k) := contDiff_pi.1 hv
  have hd1 : ∀ k, Differentiable ℝ (fun y => v y k) := fun k =>
    (hc k).differentiable two_ne_zero
  have hd : ∀ k l, Differentiable ℝ (pd (fun y => v y k) l) := fun k l =>
    (contDiff_pd (hc k) l).differentiable one_ne_zero
  have hk : ∀ j, pd (kinetic v) j = fun y => ∑ k, v y k * pd (fun y => v y k) j y := fun j =>
    funext fun y => pd_kinetic (hv.differentiable two_ne_zero y) j
  have hkk : ∀ j, pd (pd (kinetic v) j) j x = ∑ k, (pd (fun y => v y k) j x ^ 2 +
      v x k * pd (pd (fun y => v y k) j) j x) := fun j => by
    rw [hk, pd_sum (f := fun k y => v y k * pd (fun y => v y k) j y) _
      (fun k => (hd1 k).mul (hd k j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_fun_mul (hd1 k x) (hd k j x)]
    ring
  simp only [lap, hkk, gradSq, dotProduct, vecLap, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j k => pd (fun y => v y k) j x ^ 2),
    Finset.sum_comm (f := fun j k => v x k * pd (pd (fun y => v y k) j) j x)]
  ring

/-- **Viscous dissipation**: for a compactly supported `C²` velocity field,
`∫ v·Δv = -∫ |∇v|²`; the viscous force `μΔv` (`μ ≥ 0`) does negative work. -/
theorem integral_dot_vecLap (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ∫ x, v x ⬝ᵥ vecLap v x = -∫ x, gradSq (fun i y => v y i) x := by
  have hc2 : ∀ k, ContDiff ℝ 2 (fun y => v y k) := contDiff_pi.1 hv
  have hc1 : ∀ k, ContDiff ℝ 1 (fun y => v y k) := fun k => (hc2 k).of_le (by norm_num)
  have hs : ∀ k, HasCompactSupport (fun y => v y k) := fun k =>
    hc.comp_left (g := fun w : Fin n → ℝ => w k) rfl
  have cpd : ∀ i j, Continuous (pd (fun y => v y i) j) := fun i j => continuous_pd (hc1 i) j
  have i1 : ∀ i j, Integrable fun x => v x i * pd (pd (fun y => v y i) j) j x := fun i j =>
    ((hc1 i).continuous.mul (continuous_pd (contDiff_pd (hc2 i) j) j)
      ).integrable_of_hasCompactSupport (hs i).mul_right
  have i2 : ∀ i j, Integrable fun x => pd (fun y => v y i) j x ^ 2 := fun i j =>
    ((cpd i j).pow 2).integrable_of_hasCompactSupport (by
      simpa [sq] using (hasCompactSupport_pd (hs i) j).mul_right)
  simp only [dotProduct, vecLap, lap, Finset.mul_sum, gradSq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i1 i j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i2 i j,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => i1 i j, integral_finsetSum _ fun j _ => i2 i j,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_pd (hc1 i) (contDiff_pd (hc2 i) j) (hs i) j]
  simp [sq]

end Dissipation

end ContinuumMechanics.Fluids
