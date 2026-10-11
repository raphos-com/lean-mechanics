import ContinuumMechanics.Elastostatics.Variational
import ClassicalMechanics.Vector
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Ideal (inviscid) fluids

Eulerian description of an ideal fluid in `ℝⁿ = Fin n → ℝ`: a velocity field
`v : ℝ → ℝⁿ → ℝⁿ`, a pressure `p : ℝ → ℝⁿ → ℝ` and a constant density `ρ`. Spatial partial
derivatives are `Korn.pd`, time derivatives `dt f t x = ∂ₜf(t, x)`.

* **Material derivative** `Df/Dt = ∂ₜf + v·∇f` (`matDeriv`) and its chain rule along particle
  paths `ẋ = v(t, x)`: `d/dt f(t, x(t)) = (Df/Dt)(t, x(t))` (`hasDerivAt_matDeriv`).
* **Incompressible Euler equations** `ρ(∂ₜv + (v·∇)v) = -∇p + ρg`, `div v = 0`
  (`IsIncompressibleEuler`), the steady version with `g = -∇Φ` (`IsSteadyEuler`), and the
  **Lamb vector identity** `(v·∇)v = ∇(|v|²/2) - v × ω`, `ω = ∇ × v`, in `ℝ³`.
* **Bernoulli's theorem**: for steady flow the Bernoulli function `H = p/ρ + |v|²/2 + Φ`
  satisfies `v·∇H = 0` and is constant along streamlines; for irrotational steady flow in `ℝ³`
  it is constant everywhere.
* **Potential flow**: `v = ∇φ` is incompressible iff `Δφ = 0` and irrotational; with the
  unsteady Bernoulli pressure `p = ρ(-∂ₜφ - |∇φ|²/2 - Φ)` it solves the Euler equations.
* **Kelvin's circulation theorem**: the circulation around a closed material loop is conserved
  when `Dv/Dt = -∇h`, in particular for the incompressible Euler equations with conservative
  body force.

## Main results

* `hasDerivAt_matDeriv`: chain rule for the material derivative.
* `convect_eq_grad_kinetic_sub_cross`: `(u·∇)u = ∇(|u|²/2) - u × (∇ × u)`.
* `IsIncompressibleEuler.lamb`: the Lamb form of the Euler equations.
* `IsSteadyEuler.dirDeriv_bernoulli`, `IsSteadyEuler.bernoulli_streamline`: Bernoulli's theorem.
* `IsSteadyEuler.grad_bernoulli_eq_zero`, `IsSteadyEuler.bernoulli_const_of_irrotational`:
  Bernoulli's theorem for irrotational flow.
* `dt_pd_comm`: `∂ₜ∂ᵢφ = ∂ᵢ∂ₜφ` for jointly `C²` fields.
* `divergence_potVel`, `curl_potVel`, `isIncompressibleEuler_potential`: potential flow.
* `circulation_const`, `IsIncompressibleEuler.circulation_const`: Kelvin's circulation theorem.

## References

* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §§3.5, 5.1–5.3, 6.1.
* [ChorinMarsden1993] A. J. Chorin, J. E. Marsden, *A Mathematical Introduction to Fluid
  Mechanics*, 3rd ed., §§1.1–1.3, 2.1.
-/

open Matrix

noncomputable section

namespace ContinuumMechanics.Fluids

open Korn

variable {n : ℕ}

/-- The unit vector `eⱼ` of `ℝⁿ`. -/
abbrev e (j : Fin n) : Fin n → ℝ := Pi.single j 1

/-- A continuous linear form on `ℝⁿ` is determined by its values on the unit vectors:
`L y = Σⱼ yⱼ L eⱼ`. -/
theorem clm_apply_eq_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) (y : Fin n → ℝ) :
    L y = ∑ j, y j * L (e j) := by
  conv_lhs => rw [show y = ∑ j, y j • e j by ext k; simp [Pi.single_apply]]
  simp [map_sum, map_smul]

/-- `∂ⱼf(x)` read off from a Fréchet derivative. -/
theorem pd_eq {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) →L[ℝ] ℝ} {x : Fin n → ℝ}
    (hf : HasFDerivAt f f' x) (j : Fin n) : pd f j x = f' (e j) := by
  rw [pd, hf.fderiv]

/-- The time derivative `∂ₜf(t, x)` of an Eulerian scalar field. -/
def dt (f : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ := deriv (fun s => f s x) t

/-- The **material derivative** `Df/Dt = ∂ₜf + v·∇f` of a scalar field along the velocity
field `v`. -/
def matDeriv (v : ℝ → (Fin n → ℝ) → Fin n → ℝ) (f : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  dt f t x + ∑ j, v t x j * pd (f t) j x

section Joint

variable {f : ℝ → (Fin n → ℝ) → ℝ} {t : ℝ} {x : Fin n → ℝ}

/-- The spatial partial derivative from the joint derivative on `ℝ × ℝⁿ`. -/
theorem pd_eq_fderiv_uncurry
    (hf : DifferentiableAt ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, x)) (j : Fin n) :
    pd (f t) j x = fderiv ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, x) (0, e j) := by
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  exact (pd_eq (f := f t) h j).trans (by simp)

/-- The time derivative from the joint derivative on `ℝ × ℝⁿ`. -/
theorem dt_eq_fderiv_uncurry
    (hf : DifferentiableAt ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, x)) :
    dt f t x = fderiv ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, x) (1, 0) := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h.deriv

end Joint

/-- **Chain rule for the material derivative**: along a particle path `ẋ = v(t, x(t))`,
`d/dt f(t, x(t)) = (Df/Dt)(t, x(t))`. -/
theorem hasDerivAt_matDeriv {v : ℝ → (Fin n → ℝ) → Fin n → ℝ} {f : ℝ → (Fin n → ℝ) → ℝ}
    {X : ℝ → Fin n → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, X t))
    (hX : HasDerivAt X (v t (X t)) t) :
    HasDerivAt (fun s => f s (X s)) (matDeriv v f t (X t)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)
  set L := fderiv ℝ (fun q : ℝ × (Fin n → ℝ) => f q.1 q.2) (t, X t)
  refine h.congr_deriv ?_
  have hsplit : ((1 : ℝ), v t (X t)) = ((1 : ℝ), (0 : Fin n → ℝ)) + (0, v t (X t)) := by
    simp
  unfold matDeriv
  rw [dt_eq_fderiv_uncurry hf, hsplit, map_add]
  congr 1
  symm
  have := clm_apply_eq_sum (L.comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))) (v t (X t))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => by rw [pd_eq_fderiv_uncurry hf]

/-! ### Spatial vector calculus -/

/-- The gradient `∇f = (∂ⱼf)ⱼ`. -/
def grad (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => pd f j x

/-- The convective derivative `(u·∇)u`, with components `Σⱼ uⱼ ∂ⱼuᵢ`. -/
def convect (u : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, u x j * pd (fun y => u y i) j x

/-- The divergence `div u = Σᵢ ∂ᵢuᵢ` of a vector field. -/
def divergence (u : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, pd (fun y => u y i) i x

/-- The kinetic energy density per unit mass `|u|²/2`. -/
def kinetic (u : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : ℝ := (u x ⬝ᵥ u x) / 2

/-- The curl `ω = ∇ × u` of a vector field on `ℝ³` (the vorticity when `u` is a velocity). -/
def curl (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![pd (fun y => u y 2) 1 x - pd (fun y => u y 1) 2 x,
    pd (fun y => u y 0) 2 x - pd (fun y => u y 2) 0 x,
    pd (fun y => u y 1) 0 x - pd (fun y => u y 0) 1 x]

/-- The derivative of the kinetic energy density `|u|²/2`. -/
theorem hasFDerivAt_kinetic {u : (Fin n → ℝ) → Fin n → ℝ} {x : Fin n → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (kinetic u)
      ((1 / 2 : ℝ) •
        ∑ k, (u x k • fderiv ℝ (fun y => u y k) x + u x k • fderiv ℝ (fun y => u y k) x)) x := by
  have hk : ∀ k, HasFDerivAt (fun y => u y k) (fderiv ℝ (fun y => u y k) x) x :=
    fun k => (differentiableAt_pi.1 hu k).hasFDerivAt
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (hk k).mul (hk k)).const_mul
    (1 / 2 : ℝ)
  convert h using 1
  funext y
  simp only [kinetic, dotProduct, Pi.mul_apply]
  ring

/-- `∂ᵢ(|u|²/2) = Σₖ uₖ ∂ᵢuₖ`. -/
theorem pd_kinetic {u : (Fin n → ℝ) → Fin n → ℝ} {x : Fin n → ℝ} (hu : DifferentiableAt ℝ u x)
    (i : Fin n) : pd (kinetic u) i x = ∑ k, u x k * pd (fun y => u y k) i x := by
  rw [pd_eq (hasFDerivAt_kinetic hu)]
  simp only [pd, _root_.smul_apply, FunLike.coe_sum, Finset.sum_apply,
    _root_.add_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The **Lamb vector identity** `(u·∇)u = ∇(|u|²/2) - u × ω` with `ω = ∇ × u`, for a field
`u : ℝ³ → ℝ³` differentiable at `x`. -/
theorem convect_eq_grad_kinetic_sub_cross {u : (Fin 3 → ℝ) → Fin 3 → ℝ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    convect u x = grad (kinetic u) x - u x ⨯₃ curl u x := by
  ext i
  simp only [Pi.sub_apply, grad, pd_kinetic hu]
  fin_cases i <;>
    simp [convect, curl, cross_apply, Fin.sum_univ_three] <;> ring

/-- `div ∇f = Δf`. -/
theorem divergence_grad (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    divergence (grad f) x = lap f x := rfl

/-- `∇ × ∇f = 0` for `f` of class `C²` on `ℝ³`. -/
theorem curl_grad {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin 3 → ℝ) :
    curl (grad f) x = 0 := by
  have h := pd_pd_comm hf
  ext i
  fin_cases i <;> simp [curl, grad, h 1 2, h 0 2, h 0 1]

/-! ### The incompressible Euler equations -/

/-- The acceleration `Dv/Dt = ∂ₜv + (v·∇)v` of the fluid particles. -/
def accel (v : ℝ → (Fin n → ℝ) → Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => matDeriv v (fun s y => v s y i) t x

/-- The acceleration splits as `∂ₜv + (v·∇)v`. -/
theorem accel_eq (v : ℝ → (Fin n → ℝ) → Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    accel v t x = (fun i => dt (fun s y => v s y i) t x) + convect (v t) x := rfl

/-- The **incompressible Euler equations** with constant density `ρ`, velocity `v`, pressure `p`
and body force (per unit mass) `g`: `ρ(∂ₜv + (v·∇)v) = -∇p + ρg` and `div v = 0`. -/
structure IsIncompressibleEuler (ρ : ℝ) (v : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (p : ℝ → (Fin n → ℝ) → ℝ) (g : ℝ → (Fin n → ℝ) → Fin n → ℝ) : Prop where
  /-- Balance of linear momentum. -/
  momentum : ∀ t x, ρ • accel v t x = -grad (p t) x + ρ • g t x
  /-- Incompressibility. -/
  incompressible : ∀ t x, divergence (v t) x = 0

/-- **Lamb form** of the Euler equations in `ℝ³`:
`ρ(∂ₜv + ∇(|v|²/2) - v × ω) = -∇p + ρg`. -/
theorem IsIncompressibleEuler.lamb {ρ : ℝ} {v : ℝ → (Fin 3 → ℝ) → Fin 3 → ℝ}
    {p : ℝ → (Fin 3 → ℝ) → ℝ} {g : ℝ → (Fin 3 → ℝ) → Fin 3 → ℝ}
    (h : IsIncompressibleEuler ρ v p g) {t : ℝ} {x : Fin 3 → ℝ}
    (hv : DifferentiableAt ℝ (v t) x) :
    ρ • ((fun i => dt (fun s y => v s y i) t x) + grad (kinetic (v t)) x -
      v t x ⨯₃ curl (v t) x) = -grad (p t) x + ρ • g t x := by
  rw [← h.momentum t x, accel_eq, convect_eq_grad_kinetic_sub_cross hv, add_sub_assoc]

/-- The **steady incompressible Euler equations** with a conservative body force `g = -∇Φ`:
`ρ(v·∇)v = -∇p - ρ∇Φ` and `div v = 0`. -/
structure IsSteadyEuler (ρ : ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (p Φ : (Fin n → ℝ) → ℝ) :
    Prop where
  /-- Balance of linear momentum. -/
  momentum : ∀ x, ρ • convect v x = -grad p x - ρ • grad Φ x
  /-- Incompressibility. -/
  incompressible : ∀ x, divergence v x = 0

/-- Time-independent solutions of the Euler equations with `g = -∇Φ` are steady solutions. -/
theorem IsIncompressibleEuler.isSteadyEuler {ρ : ℝ} {v : (Fin n → ℝ) → Fin n → ℝ}
    {p Φ : (Fin n → ℝ) → ℝ}
    (h : IsIncompressibleEuler ρ (fun _ => v) (fun _ => p) (fun _ x => -grad Φ x)) :
    IsSteadyEuler ρ v p Φ where
  momentum x := by
    have hm := h.momentum 0 x
    rw [accel_eq] at hm
    simp only [dt, deriv_const', smul_neg] at hm
    rw [show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl, zero_add] at hm
    rw [hm, sub_eq_add_neg]
  incompressible x := h.incompressible 0 x

/-! ### Bernoulli's theorem -/

/-- The **Bernoulli function** `H = p/ρ + |v|²/2 + Φ`. -/
def bernoulli (ρ : ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (p Φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ℝ :=
  p x / ρ + kinetic v x + Φ x

section Bernoulli

variable {ρ : ℝ} {v : (Fin n → ℝ) → Fin n → ℝ} {p Φ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}

/-- The derivative of `p/ρ`. -/
theorem hasFDerivAt_div_const (hp : DifferentiableAt ℝ p x) :
    HasFDerivAt (fun y => p y / ρ) (ρ⁻¹ • fderiv ℝ p x) x := by
  simpa only [div_eq_mul_inv] using hp.hasFDerivAt.mul_const ρ⁻¹

/-- The Bernoulli function is differentiable where `v`, `p` and `Φ` are. -/
theorem differentiableAt_bernoulli (hv : DifferentiableAt ℝ v x) (hp : DifferentiableAt ℝ p x)
    (hΦ : DifferentiableAt ℝ Φ x) : DifferentiableAt ℝ (bernoulli ρ v p Φ) x :=
  ((hasFDerivAt_div_const hp).differentiableAt.add
    (hasFDerivAt_kinetic hv).differentiableAt).add hΦ

/-- `∂ᵢH = ∂ᵢp/ρ + Σₖ vₖ∂ᵢvₖ + ∂ᵢΦ`. -/
theorem pd_bernoulli (hv : DifferentiableAt ℝ v x) (hp : DifferentiableAt ℝ p x)
    (hΦ : DifferentiableAt ℝ Φ x) (i : Fin n) :
    pd (bernoulli ρ v p Φ) i x = pd p i x / ρ + pd (kinetic v) i x + pd Φ i x := by
  have h := ((hasFDerivAt_div_const (ρ := ρ) hp).add
    (hasFDerivAt_kinetic hv).differentiableAt.hasFDerivAt).add hΦ.hasFDerivAt
  rw [pd_eq (f := bernoulli ρ v p Φ) h]
  simp [pd, div_eq_inv_mul]

/-- The steady momentum balance: `∂ᵢp/ρ + ∂ᵢΦ = -((v·∇)v)ᵢ`. -/
theorem IsSteadyEuler.pd_pressure (h : IsSteadyEuler ρ v p Φ) (hρ : ρ ≠ 0) (x : Fin n → ℝ)
    (i : Fin n) : pd p i x / ρ + pd Φ i x = -convect v x i := by
  have hm := congrFun (h.momentum x) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply, grad] at hm
  field_simp
  linarith

/-- **Bernoulli's theorem** (differential form): in a steady flow of the incompressible Euler
equations with conservative body force, `v·∇H = 0` for the Bernoulli function
`H = p/ρ + |v|²/2 + Φ`. -/
theorem IsSteadyEuler.dirDeriv_bernoulli (h : IsSteadyEuler ρ v p Φ) (hρ : ρ ≠ 0)
    (hv : DifferentiableAt ℝ v x) (hp : DifferentiableAt ℝ p x) (hΦ : DifferentiableAt ℝ Φ x) :
    ∑ i, v x i * pd (bernoulli ρ v p Φ) i x = 0 := by
  calc ∑ i, v x i * pd (bernoulli ρ v p Φ) i x
      = ∑ i, ∑ k, (v x i * (v x k * pd (fun y => v y k) i x) -
          v x k * (v x i * pd (fun y => v y i) k x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : ∑ k, v x k * (v x i * pd (fun y => v y i) k x) = v x i * convect v x i := by
          simp only [convect, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [pd_bernoulli hv hp hΦ, pd_kinetic hv, Finset.sum_sub_distrib, ← Finset.mul_sum, hc]
        linear_combination (v x i) * h.pd_pressure hρ x i
    _ = 0 := by
        simp only [Finset.sum_sub_distrib]
        rw [sub_eq_zero, Finset.sum_comm]

/-- **Bernoulli's theorem**: in a steady flow of the incompressible Euler equations with
conservative body force, the Bernoulli function `H = p/ρ + |v|²/2 + Φ` is constant along every
streamline `ẋ = v(x)`. -/
theorem IsSteadyEuler.bernoulli_streamline (h : IsSteadyEuler ρ v p Φ) (hρ : ρ ≠ 0)
    (hv : Differentiable ℝ v) (hp : Differentiable ℝ p) (hΦ : Differentiable ℝ Φ)
    {X : ℝ → Fin n → ℝ} (hX : ∀ s, HasDerivAt X (v (X s)) s) (s s' : ℝ) :
    bernoulli ρ v p Φ (X s) = bernoulli ρ v p Φ (X s') := by
  refine ClassicalMechanics.eq_of_hasDerivAt_zero (F := fun s => bernoulli ρ v p Φ (X s))
    (fun s => ?_) s s'
  have hd := hasDerivAt_matDeriv (v := fun _ => v) (f := fun _ => bernoulli ρ v p Φ) (X := X)
    (t := s) ((differentiableAt_bernoulli (hv _) (hp _) (hΦ _)).comp (s, X s) differentiableAt_snd)
    (hX s)
  refine hd.congr_deriv ?_
  simp only [matDeriv, dt, deriv_const', zero_add]
  exact h.dirDeriv_bernoulli hρ (hv _) (hp _) (hΦ _)

/-- A linear form vanishing on all partial derivatives vanishes: `∇f(x) = 0 → Df(x) = 0`. -/
theorem fderiv_eq_zero_of_grad {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : grad f x = 0) :
    fderiv ℝ f x = 0 := by
  ext1 w
  rw [clm_apply_eq_sum, _root_.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := congrFun h j
  simp only [grad, pd, Pi.zero_apply] at hj
  rw [hj, mul_zero]

end Bernoulli

section Irrotational

variable {ρ : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {p Φ : (Fin 3 → ℝ) → ℝ}

/-- **Bernoulli's theorem for irrotational flow** (pointwise): where `ω = ∇ × v = 0`, the
gradient of the Bernoulli function vanishes. -/
theorem IsSteadyEuler.grad_bernoulli_eq_zero (h : IsSteadyEuler ρ v p Φ) (hρ : ρ ≠ 0)
    {x : Fin 3 → ℝ} (hv : DifferentiableAt ℝ v x) (hp : DifferentiableAt ℝ p x)
    (hΦ : DifferentiableAt ℝ Φ x) (hω : curl v x = 0) :
    grad (bernoulli ρ v p Φ) x = 0 := by
  ext i
  have hl := congrFun (convect_eq_grad_kinetic_sub_cross hv) i
  rw [hω, map_zero, sub_zero] at hl
  simp only [grad] at hl ⊢
  rw [pd_bernoulli hv hp hΦ, Pi.zero_apply]
  linear_combination h.pd_pressure hρ x i - hl

/-- **Bernoulli's theorem for irrotational flow**: in a steady irrotational flow of the
incompressible Euler equations with conservative body force, the Bernoulli function
`H = p/ρ + |v|²/2 + Φ` is constant in all of space. -/
theorem IsSteadyEuler.bernoulli_const_of_irrotational (h : IsSteadyEuler ρ v p Φ) (hρ : ρ ≠ 0)
    (hv : Differentiable ℝ v) (hp : Differentiable ℝ p) (hΦ : Differentiable ℝ Φ)
    (hω : ∀ x, curl v x = 0) (x y : Fin 3 → ℝ) :
    bernoulli ρ v p Φ x = bernoulli ρ v p Φ y :=
  is_const_of_fderiv_eq_zero (fun z => differentiableAt_bernoulli (hv z) (hp z) (hΦ z))
    (fun z => fderiv_eq_zero_of_grad
      (h.grad_bernoulli_eq_zero hρ (hv z) (hp z) (hΦ z) (hω z))) x y

end Irrotational

/-! ### Potential flow -/

/-- The velocity `v = ∇φ` of a potential flow with velocity potential `φ`. -/
def potVel (φ : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := grad (φ t) x

/-- The pressure given by the unsteady Bernoulli equation, `p = ρ(-∂ₜφ - |∇φ|²/2 - Φ)`. -/
def potPressure (ρ : ℝ) (φ : ℝ → (Fin n → ℝ) → ℝ) (Φ : (Fin n → ℝ) → ℝ) (t : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ρ * (-dt φ t x - kinetic (potVel φ t) x - Φ x)

section Potential

variable {φ : ℝ → (Fin n → ℝ) → ℝ}

/-- A jointly `C²` potential is `C²` in space at each time. -/
theorem contDiff_slice (hφ : ContDiff ℝ 2 (fun q : ℝ × (Fin n → ℝ) => φ q.1 q.2)) (t : ℝ) :
    ContDiff ℝ 2 (φ t) :=
  hφ.comp (contDiff_const.prodMk contDiff_id)

/-- The partial derivatives of `q ↦ Dψ(q) w` are the second derivatives of `ψ`. -/
theorem fderiv_fderiv_apply {ψ : ℝ × (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (w u q : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (fun q' : ℝ × (Fin n → ℝ) => fderiv ℝ ψ (q'.1, q'.2) w) q u =
      fderiv ℝ (fderiv ℝ ψ) q u w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) q :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero q
  change fderiv ℝ (fun q' => fderiv ℝ ψ q' w) q u = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **Mixed partials commute**: `∂ₜ∂ᵢφ = ∂ᵢ∂ₜφ` for a jointly `C²` field. -/
theorem dt_pd_comm (hφ : ContDiff ℝ 2 (fun q : ℝ × (Fin n → ℝ) => φ q.1 q.2)) (i : Fin n)
    (t : ℝ) (x : Fin n → ℝ) :
    dt (fun s y => pd (φ s) i y) t x = pd (dt φ t) i x := by
  set ψ := fun q : ℝ × (Fin n → ℝ) => φ q.1 q.2
  have hd : ∀ q, DifferentiableAt ℝ ψ q := fun q => hφ.differentiable (by norm_num) q
  have hD : Differentiable ℝ (fderiv ℝ ψ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hDw : ∀ w q,
      DifferentiableAt ℝ (fun q' : ℝ × (Fin n → ℝ) => fderiv ℝ ψ (q'.1, q'.2) w) q :=
    fun w q => (hD q).clm_apply (differentiableAt_const w)
  have h1 : (fun s y => pd (φ s) i y) = fun s y => fderiv ℝ ψ (s, y) (0, e i) := by
    funext s y; exact pd_eq_fderiv_uncurry (hd _) i
  have h2 : dt φ t = fun y => fderiv ℝ ψ (t, y) (1, 0) := by
    funext y; exact dt_eq_fderiv_uncurry (hd _)
  rw [h1, h2, dt_eq_fderiv_uncurry (hDw _ _),
    pd_eq_fderiv_uncurry (f := fun s y => fderiv ℝ ψ (s, y) (1, 0)) (hDw _ _),
    fderiv_fderiv_apply hφ, fderiv_fderiv_apply hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- A potential flow is incompressible iff its potential is harmonic: `div ∇φ = Δφ`. -/
theorem divergence_potVel (t : ℝ) (x : Fin n → ℝ) :
    divergence (potVel φ t) x = lap (φ t) x := rfl

/-- A potential flow in `ℝ³` is irrotational: `∇ × ∇φ = 0`. -/
theorem curl_potVel {φ : ℝ → (Fin 3 → ℝ) → ℝ} (hφ : ∀ t, ContDiff ℝ 2 (φ t)) (t : ℝ)
    (x : Fin 3 → ℝ) : curl (potVel φ t) x = 0 :=
  curl_grad (hφ t) x

/-- The velocity of a `C²` potential flow is differentiable. -/
theorem differentiable_potVel (hφ : ∀ t, ContDiff ℝ 2 (φ t)) (t : ℝ) :
    Differentiable ℝ (potVel φ t) :=
  differentiable_pi.2 fun k => (contDiff_pd (hφ t) k).differentiable one_ne_zero

/-- `∂ᵢ(|∇φ|²/2) = ((∇φ·∇)∇φ)ᵢ` for a `C²` potential. -/
theorem pd_kinetic_potVel (hφ : ∀ t, ContDiff ℝ 2 (φ t)) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    pd (kinetic (potVel φ t)) i x = convect (potVel φ t) x i := by
  rw [pd_kinetic (differentiable_potVel hφ t x)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [show pd (fun y => potVel φ t y j) i x = pd (fun y => potVel φ t y i) j x from
      congrFun (pd_pd_comm (hφ t) j i) x]

/-- **Potential flow solves the Euler equations**: if `φ` is jointly `C²` and harmonic in space,
then `v = ∇φ` together with the Bernoulli pressure `p = ρ(-∂ₜφ - |∇φ|²/2 - Φ)` solves the
incompressible Euler equations with body force `g = -∇Φ`. -/
theorem isIncompressibleEuler_potential {ρ : ℝ} {Φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 (fun q : ℝ × (Fin n → ℝ) => φ q.1 q.2)) (hlap : ∀ t x, lap (φ t) x = 0)
    (hΦ : Differentiable ℝ Φ) :
    IsIncompressibleEuler ρ (potVel φ) (potPressure ρ φ Φ) (fun _ x => -grad Φ x) where
  momentum t x := by
    have hs := contDiff_slice hφ
    set ψ := fun q : ℝ × (Fin n → ℝ) => φ q.1 q.2
    have hD : Differentiable ℝ (fderiv ℝ ψ) :=
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hdt : DifferentiableAt ℝ (dt φ t) x := by
      have h2 : dt φ t = fun y => fderiv ℝ ψ (t, y) (1, 0) := by
        funext y; exact dt_eq_fderiv_uncurry (hφ.differentiable (by norm_num) _)
      rw [h2]
      exact ((hD _).comp x (differentiableAt_const t |>.prodMk differentiableAt_id)).clm_apply
        (differentiableAt_const _)
    have hK := (hasFDerivAt_kinetic (differentiable_potVel hs t x))
    have hP := (((hdt.hasFDerivAt.neg).sub hK.differentiableAt.hasFDerivAt).sub
      (hΦ x).hasFDerivAt).const_mul ρ
    ext i
    have hp : pd (potPressure ρ φ Φ t) i x =
        ρ * (-pd (dt φ t) i x - pd (kinetic (potVel φ t)) i x - pd Φ i x) := by
      rw [pd_eq (f := potPressure ρ φ Φ t) hP]
      simp [pd]
    simp only [accel, matDeriv, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, grad, smul_eq_mul]
    rw [hp, pd_kinetic_potVel hs t x i]
    change ρ * (dt (fun s y => pd (φ s) i y) t x + convect (potVel φ t) x i) = _
    rw [dt_pd_comm hφ]
    ring
  incompressible t x := hlap t x

end Potential

/-! ### Kelvin's circulation theorem -/

/-- Product rule for the dot product of curves in `ℝⁿ`. -/
theorem hasDerivAt_dotProduct {f g : ℝ → Fin n → ℝ} {f' g' : Fin n → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hf' i).mul (hg' i)
  convert this using 1
  · ext s; simp [dotProduct]
  · simp [dotProduct, Finset.sum_add_distrib]

/-- Derivative of `τ ↦ D(γ(τ)) w` for a differentiable operator field `D` along a curve `γ`. -/
theorem hasDerivAt_clm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] E} {γ : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {τ : ℝ}
    (hD : DifferentiableAt ℝ D (γ τ)) (hγ : HasDerivAt γ d τ) (w : ℝ × ℝ) :
    HasDerivAt (fun σ => D (γ σ) w) (fderiv ℝ D (γ τ) d w) τ :=
  (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivAt τ
    (hD.hasFDerivAt.comp_hasDerivAt τ hγ)

/-- The **circulation** `Γ(t) = ∮ v · dx = ∫₀¹ v(t, C(t, s)) · ∂ₛC(t, s) ds` of the velocity
around the loop `C(t, ·)`. -/
def circulation (v : ℝ → (Fin n → ℝ) → Fin n → ℝ) (C : ℝ → ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, v t (C t s) ⬝ᵥ deriv (C t) s

section Kelvin

variable {v : ℝ → (Fin n → ℝ) → Fin n → ℝ} {h : ℝ → (Fin n → ℝ) → ℝ} {C : ℝ → ℝ → Fin n → ℝ}

/-- The key identity behind Kelvin's theorem: for a material loop `C` of a flow whose
acceleration is a gradient, `Dv/Dt = -∇h`, the time derivative of the circulation integrand
`v(t, C(t,s)) · ∂ₛC(t,s)` equals the `s`-derivative of `-h + |v|²/2` evaluated on the loop. -/
theorem kelvin_integrand
    (hv : ContDiff ℝ 1 (fun q : ℝ × (Fin n → ℝ) => v q.1 q.2))
    (hC : ContDiff ℝ 2 (fun q : ℝ × ℝ => C q.1 q.2)) (hh : ∀ t, Differentiable ℝ (h t))
    (hmat : ∀ t s, HasDerivAt (fun τ => C τ s) (v t (C t s)) t)
    (hacc : ∀ t x, accel v t x = -grad (h t) x) (t s : ℝ) :
    ∃ a, HasDerivAt (fun τ => v τ (C τ s) ⬝ᵥ deriv (C τ) s) a t ∧
      HasDerivAt (fun σ => -h t (C t σ) + (v t (C t σ) ⬝ᵥ v t (C t σ)) / 2) a s := by
  set C' := fun q : ℝ × ℝ => C q.1 q.2
  have hC1 : ∀ q, DifferentiableAt ℝ C' q := fun q => hC.differentiable (by norm_num) q
  have hD : Differentiable ℝ (fderiv ℝ C') :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hvd : ∀ q, DifferentiableAt ℝ (fun q : ℝ × (Fin n → ℝ) => v q.1 q.2) q :=
    fun q => hv.differentiable one_ne_zero q
  have hs : ∀ τ σ, HasDerivAt (C τ) (fderiv ℝ C' (τ, σ) (0, 1)) σ := fun τ σ =>
    (hC1 (τ, σ)).hasFDerivAt.comp_hasDerivAt σ ((hasDerivAt_const σ τ).prodMk (hasDerivAt_id σ))
  have ht : ∀ τ σ, fderiv ℝ C' (τ, σ) (1, 0) = v τ (C τ σ) := fun τ σ => by
    have h0 := (hC1 (τ, σ)).hasFDerivAt.comp_hasDerivAt τ
        ((hasDerivAt_id' τ).prodMk (hasDerivAt_const τ σ))
    exact h0.unique (hmat τ σ)
  have hds : ∀ τ, deriv (C τ) s = fderiv ℝ C' (τ, s) (0, 1) := fun τ => (hs τ s).deriv
  set c' := fderiv ℝ C' (t, s) (0, 1)
  have hvt : Differentiable ℝ (v t) := fun x =>
    (hvd (t, x)).comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x).differentiableAt
  set W := fderiv ℝ (v t) (C t s) c'
  have hW : HasDerivAt (fun σ => v t (C t σ)) W s :=
    (hvt _).hasFDerivAt.comp_hasDerivAt s (hs t s)
  have hcW : HasDerivAt (fun τ => deriv (C τ) s) W t := by
    have h1 := hasDerivAt_clm_comp (γ := fun τ => (τ, s)) (hD (t, s))
      ((hasDerivAt_id' t).prodMk (hasDerivAt_const t s)) (0, 1)
    have h2 := hasDerivAt_clm_comp (γ := fun σ => (t, σ)) (hD (t, s))
      ((hasDerivAt_const s t).prodMk (hasDerivAt_id' s)) (1, 0)
    simp only [ht] at h2
    have hsym := (hC.contDiffAt (x := (t, s))).isSymmSndFDerivAt (by simp) (1, 0) (0, 1)
    rw [show (fun τ => deriv (C τ) s) = fun τ => fderiv ℝ C' (τ, s) (0, 1) from funext hds]
    refine h1.congr_deriv ?_
    rw [hW.unique h2]
    exact hsym
  have hva : HasDerivAt (fun τ => v τ (C τ s)) (accel v t (C t s)) t :=
    hasDerivAt_pi.2 fun i => hasDerivAt_matDeriv (f := fun τ y => v τ y i)
      (differentiableAt_pi.1 (hvd _) i) (hmat t s)
  refine ⟨_, hasDerivAt_dotProduct hva hcW, ?_⟩
  have hhs : HasDerivAt (fun σ => h t (C t σ)) (fderiv ℝ (h t) (C t s) c') s :=
    (hh t _).hasFDerivAt.comp_hasDerivAt s (hs t s)
  have hk := (hasDerivAt_dotProduct hW hW).div_const 2
  refine (hhs.neg.add hk).congr_deriv ?_
  rw [hds t, hacc, clm_apply_eq_sum]
  have e1 : ∑ i, W i * v t (C t s) i = ∑ i, v t (C t s) i * W i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∑ j, c' j * pd (h t) j (C t s) = ∑ j, pd (h t) j (C t s) * c' j :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [dotProduct, grad, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, e1]
  change -∑ j, c' j * pd (h t) j (C t s) + _ = -∑ x, pd (h t) x (C t s) * c' x + _
  rw [e2]
  ring

/-- **Kelvin's circulation theorem**: if the acceleration of the flow is a gradient,
`Dv/Dt = -∇h` (ideal barotropic flow with conservative body force), then the circulation
`Γ(t) = ∮_{C(t)} v · dx` around a closed material loop `C(t, ·)` (`∂ₜC = v(t, C)`,
`C(t, 0) = C(t, 1)`) is independent of time. -/
theorem circulation_const
    (hv : ContDiff ℝ 1 (fun q : ℝ × (Fin n → ℝ) => v q.1 q.2))
    (hC : ContDiff ℝ 2 (fun q : ℝ × ℝ => C q.1 q.2)) (hh : ∀ t, Differentiable ℝ (h t))
    (hmat : ∀ t s, HasDerivAt (fun τ => C τ s) (v t (C t s)) t)
    (hacc : ∀ t x, accel v t x = -grad (h t) x) (hclosed : ∀ t, C t 0 = C t 1) (t t' : ℝ) :
    circulation v C t = circulation v C t' := by
  set G := fun q : ℝ × ℝ => v q.1 (C q.1 q.2) ⬝ᵥ deriv (C q.1) q.2
  set C' := fun q : ℝ × ℝ => C q.1 q.2
  have hds : G = fun q => v q.1 (C' q) ⬝ᵥ fderiv ℝ C' q (0, 1) := by
    funext q
    have h0 := (hC.differentiable (by norm_num) q).hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id' q.2))
    have h1 : deriv (C q.1) q.2 = fderiv ℝ C' q (0, 1) := h0.deriv
    simp only [G]
    rw [h1]
  have hG : ContDiff ℝ 1 G := by
    have hA : ContDiff ℝ 1 fun q : ℝ × ℝ => v q.1 (C' q) :=
      hv.comp (contDiff_fst.prodMk (hC.of_le (by norm_num)))
    have hB : ContDiff ℝ 1 fun q : ℝ × ℝ => fderiv ℝ C' q (0, 1) :=
      (hC.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    rw [hds]
    simp only [dotProduct]
    exact ContDiff.sum fun i _ => (contDiff_pi.1 hA i).mul (contDiff_pi.1 hB i)
  have hGd : ∀ τ σ, HasDerivAt (fun τ' => G (τ', σ)) (fderiv ℝ G (τ, σ) (1, 0)) τ :=
    fun τ σ => by
      have h0 := (hG.differentiable one_ne_zero (τ, σ)).hasFDerivAt.comp_hasDerivAt τ
        ((hasDerivAt_id' τ).prodMk (hasDerivAt_const τ σ))
      exact h0
  have key : ∀ τ σ, HasDerivAt (fun σ' => -h τ (C τ σ') + (v τ (C τ σ') ⬝ᵥ v τ (C τ σ')) / 2)
      (fderiv ℝ G (τ, σ) (1, 0)) σ := fun τ σ => by
    obtain ⟨a, ha1, ha2⟩ := kelvin_integrand hv hC hh hmat hacc τ σ
    rwa [ha1.unique (hGd τ σ)] at ha2
  have hcont : Continuous fun q => fderiv ℝ G q (1, 0) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ClassicalMechanics.eq_of_hasDerivAt_zero (fun τ => ?_) t t'
  obtain ⟨M, hM⟩ := ((isCompact_closedBall τ 1).prod (isCompact_uIcc (a := (0 : ℝ)) (b := 1))
    ).exists_bound_of_continuousOn hcont.continuousOn
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (F := fun τ' σ => G (τ', σ))
    (F' := fun τ' σ => fderiv ℝ G (τ', σ) (1, 0))
    (x₀ := τ) (bound := fun _ => M) (Metric.closedBall_mem_nhds τ one_pos)
    (Filter.Eventually.of_forall fun τ' =>
      (hG.continuous.comp (Continuous.prodMk_right τ')).aestronglyMeasurable)
    ((hG.continuous.comp (Continuous.prodMk_right τ)).intervalIntegrable 0 1)
    (hcont.comp (Continuous.prodMk_right τ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun σ hσ τ' hτ' =>
      hM (τ', σ) ⟨hτ', Set.uIoc_subset_uIcc hσ⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun σ _ τ' _ => hGd τ' σ)
  refine hd.2.congr_deriv ?_
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => key τ σ)
    ((hcont.comp (Continuous.prodMk_right τ)).intervalIntegrable 0 1), hclosed τ, sub_self]

/-- **Kelvin's circulation theorem** for the incompressible Euler equations with conservative
body force `g = -∇Φ`: the circulation around a closed material loop is conserved. -/
theorem IsIncompressibleEuler.circulation_const {ρ : ℝ} {p : ℝ → (Fin n → ℝ) → ℝ}
    {Φ : (Fin n → ℝ) → ℝ} (hE : IsIncompressibleEuler ρ v p (fun _ x => -grad Φ x))
    (hρ : ρ ≠ 0) (hv : ContDiff ℝ 1 (fun q : ℝ × (Fin n → ℝ) => v q.1 q.2))
    (hp : ∀ t, Differentiable ℝ (p t)) (hΦ : Differentiable ℝ Φ)
    (hC : ContDiff ℝ 2 (fun q : ℝ × ℝ => C q.1 q.2))
    (hmat : ∀ t s, HasDerivAt (fun τ => C τ s) (v t (C t s)) t)
    (hclosed : ∀ t, C t 0 = C t 1) (t t' : ℝ) :
    circulation v C t = circulation v C t' := by
  refine Fluids.circulation_const (h := fun t y => p t y / ρ + Φ y) hv hC
    (fun t => fun y => (hasFDerivAt_div_const (hp t y)).differentiableAt.add (hΦ y)) hmat
    (fun t x => ?_) hclosed t t'
  have hm := hE.momentum t x
  have hd := (hasFDerivAt_div_const (ρ := ρ) (hp t x)).add (hΦ x).hasFDerivAt
  ext i
  have hi := congrFun hm i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.neg_apply, grad] at hi ⊢
  rw [pd_eq (f := fun y => p t y / ρ + Φ y) hd]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change accel v t x i = -(ρ⁻¹ * pd (p t) i x + pd Φ i x)
  field_simp
  linarith

end Kelvin

end ContinuumMechanics.Fluids
