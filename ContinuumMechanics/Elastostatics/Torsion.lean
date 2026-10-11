import ContinuumMechanics.Elastostatics.NavierLame
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Saint-Venant torsion of prismatic bars

A prismatic bar with axis `x₃` (here the coordinate `x 2`; `x₁, x₂` are `x 0, x 1`), twisted at
rate `α`, has the **Saint-Venant displacement**

`u = (-α x₂ x₃, α x₁ x₃, α ψ(x₁, x₂))`,

with a **warping function** `ψ` independent of `x₃` (hypothesis `pd ψ 2 = 0`).

* **Strains** (`strain_disp_*`): `ε₁₁ = ε₂₂ = ε₃₃ = ε₁₂ = 0`, `ε₁₃ = (α/2)(∂₁ψ - x₂)`,
  `ε₂₃ = (α/2)(∂₂ψ + x₁)`; the motion is isochoric, `div u = 0` (`div_disp`).
* **Navier–Lamé** (`res_disp_*`, `res_disp_eq_zero_iff`, `isStationary_disp_iff`): the residual of
  the Navier–Lamé equations is `(0, 0, -μ α Δψ)`, so for `μ α ≠ 0` the equations without body
  force hold iff the warping function is **harmonic**.
* **Prandtl stress function** (`prandtl_equilibrium`, `prandtl_compat`): shear stresses
  `τ₁₃ = ∂₂Φ`, `τ₂₃ = -∂₁Φ` satisfy `∂₁τ₁₃ + ∂₂τ₂₃ = 0` identically, and if they derive from a
  warping function (`τ₁₃ = μα(∂₁ψ - x₂)`, `τ₂₃ = μα(∂₂ψ + x₁)`) then `ΔΦ = -2μα`.
* **Circular shaft** (`circ_*`, `polarMoment_disk`, `torque_circ`): `ψ = 0`,
  `Φ = -(μα/2)(x₁² + x₂² - R²)`, and the torque is `T = μ α π R⁴ / 2 = μ J α`.
* **Elliptic bar** (`ellip_*`, `torque_ellip`): `ψ = -((a² - b²)/(a² + b²)) x₁ x₂`,
  `Φ = c (x₁²/a² + x₂²/b² - 1)` with `c = -μα a²b²/(a² + b²)`, and
  `T = μ α π a³ b³ / (a² + b²)`.

The disk integral is computed in polar coordinates (`integral_comp_polarCoord_symm`); the ellipse
is reduced to the unit disk by the scaling `(x₁, x₂) ↦ (a x₁, b x₂)`.

## Main results

* `res_disp_eq_zero_iff`: Navier–Lamé for the Saint-Venant field `⇔ Δψ = 0`.
* `prandtl_equilibrium`, `prandtl_compat`: Prandtl's stress function and `ΔΦ = -2μα`.
* `torque_circ`: `T = μ α π R⁴ / 2` for the circular shaft.
* `torque_ellip`: `T = μ α π a³ b³ / (a² + b²)` for the elliptic bar.

## References

* [Timoshenko1970] S. P. Timoshenko, J. N. Goodier, *Theory of Elasticity*, Ch. 10.
* [Sokolnikoff1956] I. S. Sokolnikoff, *Mathematical Theory of Elasticity*, Ch. 4.
-/

open MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Torsion

open Korn NavierLame

/-! ### Partial derivatives of elementary functions -/

section Calculus

variable {f g : (Fin 3 → ℝ) → ℝ}

/-- `∂ⱼ xₖ = δⱼₖ`. -/
theorem pd_coord (k j : Fin 3) :
    pd (fun x : Fin 3 → ℝ => x k) j = fun _ => if j = k then 1 else 0 := by
  funext x
  rw [pd, (hasFDerivAt_apply k x).fderiv]
  by_cases h : j = k <;> simp [h]

/-- The derivative of a constant vanishes. -/
theorem pd_const (c : ℝ) (j : Fin 3) : pd (fun _ : Fin 3 → ℝ => c) j = fun _ => 0 := by
  funext x; simp [pd]

/-- Product rule. -/
theorem pd_mul (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3) :
    pd (fun y => f y * g y) j = fun x => pd f j x * g x + f x * pd g j x := by
  funext x; simp [pd, fderiv_fun_mul (hf x) (hg x)]; ring

/-- Sum rule. -/
theorem pd_add' (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3) :
    pd (fun y => f y + g y) j = fun x => pd f j x + pd g j x := by
  funext x; simp [pd, fderiv_fun_add (hf x) (hg x)]

/-- Difference rule. -/
theorem pd_sub' (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3) :
    pd (fun y => f y - g y) j = fun x => pd f j x - pd g j x := by
  funext x; simp [pd, fderiv_fun_sub (hf x) (hg x)]

/-- Negation rule. -/
theorem pd_neg' (j : Fin 3) : pd (fun y => -f y) j = fun x => -pd f j x := by
  funext x; simp [pd]

/-- Square rule. -/
theorem pd_sq (hf : Differentiable ℝ f) (j : Fin 3) :
    pd (fun y => f y ^ 2) j = fun x => 2 * f x * pd f j x := by
  simp only [pow_two]
  rw [pd_mul hf hf]
  funext x; ring

/-- Partial derivatives of a `C²` function are differentiable. -/
theorem differentiable_pd (hf : ContDiff ℝ 2 f) (j : Fin 3) : Differentiable ℝ (pd f j) :=
  (contDiff_pd hf j).differentiable one_ne_zero

end Calculus

/-- The planar Laplacian `Δ₂f = ∂₁∂₁f + ∂₂∂₂f` in the cross-section variables. -/
def planeLap (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ := pd (pd f 0) 0 x + pd (pd f 1) 1 x

/-- For `f` independent of `x₃`, the Laplacian is the planar Laplacian. -/
theorem lap_eq_planeLap {f : (Fin 3 → ℝ) → ℝ} (hf : ∀ x, pd f 2 x = 0) (x : Fin 3 → ℝ) :
    lap f x = planeLap f x := by
  have h : pd f 2 = fun _ => 0 := funext hf
  simp [lap, planeLap, Fin.sum_univ_three, h, pd_const]

/-! ### The Saint-Venant displacement field -/

/-- The **Saint-Venant torsion displacement** `u = (-α x₂ x₃, α x₁ x₃, α ψ)` with twist rate `α`
and warping function `ψ`. -/
def disp (α : ℝ) (ψ : (Fin 3 → ℝ) → ℝ) : Fin 3 → (Fin 3 → ℝ) → ℝ :=
  ![fun x => -(α * x 1 * x 2), fun x => α * x 0 * x 2, fun x => α * ψ x]

variable {α : ℝ} {ψ : (Fin 3 → ℝ) → ℝ}

/-- The Saint-Venant displacement is as smooth as the warping function. -/
theorem contDiff_disp {k : WithTop ℕ∞} (hψ : ContDiff ℝ k ψ) (i : Fin 3) :
    ContDiff ℝ k (disp α ψ i) := by
  fin_cases i
  · change ContDiff ℝ k fun x : Fin 3 → ℝ => -(α * x 1 * x 2)
    fun_prop
  · change ContDiff ℝ k fun x : Fin 3 → ℝ => α * x 0 * x 2
    fun_prop
  · change ContDiff ℝ k fun x : Fin 3 → ℝ => α * ψ x
    fun_prop

section Strain

variable (hψ : Differentiable ℝ ψ) (hψ2 : ∀ x, pd ψ 2 x = 0)

/-- `ε₁₁ = ε₂₂ = 0`: no in-plane normal strain. -/
theorem strain_disp_00 (x : Fin 3 → ℝ) : strain (disp α ψ) 0 0 x = 0 := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_coord, pd_const, pd_neg']

/-- `ε₂₂ = 0`. -/
theorem strain_disp_11 (x : Fin 3 → ℝ) : strain (disp α ψ) 1 1 x = 0 := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_coord, pd_const]

include hψ hψ2 in
/-- `ε₃₃ = 0`, since `ψ` does not depend on `x₃`. -/
theorem strain_disp_22 (x : Fin 3 → ℝ) : strain (disp α ψ) 2 2 x = 0 := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_const, hψ2]

/-- `ε₁₂ = 0`: cross-sections rotate rigidly in their plane. -/
theorem strain_disp_01 (x : Fin 3 → ℝ) : strain (disp α ψ) 0 1 x = 0 := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_coord, pd_const, pd_neg']

include hψ in
/-- `ε₁₃ = (α/2)(∂₁ψ - x₂)`. -/
theorem strain_disp_02 (x : Fin 3 → ℝ) :
    strain (disp α ψ) 0 2 x = α / 2 * (pd ψ 0 x - x 1) := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_coord, pd_const, pd_neg']
  ring

include hψ in
/-- `ε₂₃ = (α/2)(∂₂ψ + x₁)`. -/
theorem strain_disp_12 (x : Fin 3 → ℝ) :
    strain (disp α ψ) 1 2 x = α / 2 * (pd ψ 1 x + x 0) := by
  simp (disch := fun_prop) [strain, disp, pd_mul, pd_coord, pd_const]
  ring

include hψ hψ2 in
/-- The torsion field is **isochoric**: `div u = 0`. -/
theorem div_disp (x : Fin 3 → ℝ) : div (disp α ψ) x = 0 := by
  simp (disch := fun_prop) [div, Fin.sum_univ_three, disp, pd_mul, pd_coord, pd_const, pd_neg',
    hψ2]

end Strain

section NavierLame

variable (hψ : ContDiff ℝ 3 ψ) (hψ2 : ∀ x, pd ψ 2 x = 0)

/-- `Δu₁ = 0`. -/
theorem lap_disp_0 (x : Fin 3 → ℝ) : lap (disp α ψ 0) x = 0 := by
  simp (disch := fun_prop) [lap, Fin.sum_univ_three, disp, pd_mul, pd_coord, pd_const, pd_neg']

/-- `Δu₂ = 0`. -/
theorem lap_disp_1 (x : Fin 3 → ℝ) : lap (disp α ψ 1) x = 0 := by
  simp (disch := fun_prop) [lap, Fin.sum_univ_three, disp, pd_mul, pd_coord, pd_const]

include hψ in
/-- `Δu₃ = α Δψ`. -/
theorem lap_disp_2 (x : Fin 3 → ℝ) : lap (disp α ψ 2) x = α * lap ψ x := by
  have h2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have h1 : Differentiable ℝ ψ := h2.differentiable (by norm_num)
  have d : ∀ j, Differentiable ℝ (pd ψ j) := differentiable_pd h2
  simp (disch := fun_prop) [lap, Fin.sum_univ_three, disp, pd_mul, pd_const, mul_add]

include hψ hψ2

/-- The residual `-(μ Δu + (λ + μ) ∇ div u)` of the Navier–Lamé equations, first component. -/
theorem res_disp_0 (lam μ : ℝ) (x : Fin 3 → ℝ) : res lam μ (disp α ψ) 0 x = 0 := by
  have hd : div (disp α ψ) = fun _ => 0 := funext (div_disp (hψ.differentiable (by simp)) hψ2)
  rw [res_eq (contDiff_disp hψ), hd, pd_const]
  simp [lap_disp_0]

/-- Second component of the Navier–Lamé residual. -/
theorem res_disp_1 (lam μ : ℝ) (x : Fin 3 → ℝ) : res lam μ (disp α ψ) 1 x = 0 := by
  have hd : div (disp α ψ) = fun _ => 0 := funext (div_disp (hψ.differentiable (by simp)) hψ2)
  rw [res_eq (contDiff_disp hψ), hd, pd_const]
  simp [lap_disp_1]

/-- Third component of the Navier–Lamé residual: `R₃ = -μ α Δψ`. -/
theorem res_disp_2 (lam μ : ℝ) (x : Fin 3 → ℝ) :
    res lam μ (disp α ψ) 2 x = -(μ * α * lap ψ x) := by
  have hd : div (disp α ψ) = fun _ => 0 := funext (div_disp (hψ.differentiable (by simp)) hψ2)
  rw [res_eq (contDiff_disp hψ), hd, pd_const]
  simp [lap_disp_2 hψ, mul_assoc]

/-- **Saint-Venant torsion**: for `μ α ≠ 0`, the Saint-Venant field satisfies the Navier–Lamé
equations without body force iff the warping function is harmonic, `Δψ = 0`. -/
theorem res_disp_eq_zero_iff (lam μ : ℝ) (hμ : μ ≠ 0) (hα : α ≠ 0) :
    (∀ i x, res lam μ (disp α ψ) i x = 0) ↔ ∀ x, planeLap ψ x = 0 := by
  constructor
  · intro h x
    have := h 2 x
    rw [res_disp_2 hψ hψ2, neg_eq_zero, lap_eq_planeLap hψ2] at this
    simpa [hμ, hα] using this
  · intro h i x
    fin_cases i
    · exact res_disp_0 hψ hψ2 lam μ x
    · exact res_disp_1 hψ hψ2 lam μ x
    · simp [res_disp_2 hψ hψ2, lap_eq_planeLap hψ2, h x]

/-- **Variational form**: on an open set `U`, the Saint-Venant field is a stationary point of the
elastic energy without body force iff the warping function is harmonic in `U`. -/
theorem isStationary_disp_iff (lam μ : ℝ) (hμ : μ ≠ 0) (hα : α ≠ 0) {U : Set (Fin 3 → ℝ)}
    (hU : IsOpen U) :
    IsStationary lam μ (disp α ψ) 0 U ↔ ∀ x ∈ U, planeLap ψ x = 0 := by
  rw [isStationary_iff (b := 0) (fun i => contDiff_disp (hψ.of_le (by norm_num)) i)
    (fun _ => continuous_const) hU]
  constructor
  · intro h x hx
    have := h 2 x hx
    simp only [Pi.zero_apply] at this
    rw [res_disp_2 hψ hψ2, neg_eq_zero, lap_eq_planeLap hψ2] at this
    simpa [hμ, hα] using this
  · intro h i x hx
    fin_cases i
    · exact res_disp_0 hψ hψ2 lam μ x
    · exact res_disp_1 hψ hψ2 lam μ x
    · simp [res_disp_2 hψ hψ2, lap_eq_planeLap hψ2, h x hx]

end NavierLame

/-! ### Prandtl's stress function -/

section Prandtl

variable {Φ : (Fin 3 → ℝ) → ℝ}

/-- **Equilibrium**: the shear stresses `τ₁₃ = ∂₂Φ`, `τ₂₃ = -∂₁Φ` derived from a `C²` Prandtl
stress function satisfy `∂₁τ₁₃ + ∂₂τ₂₃ = 0` identically. -/
theorem prandtl_equilibrium (hΦ : ContDiff ℝ 2 Φ) (x : Fin 3 → ℝ) :
    pd (pd Φ 1) 0 x + pd (fun y => -pd Φ 0 y) 1 x = 0 := by
  rw [pd_neg', pd_pd_comm hΦ 1 0]
  ring

/-- **Compatibility**: if the Prandtl stresses agree with those of a warping function,
`τ₁₃ = μα(∂₁ψ - x₂)` and `τ₂₃ = μα(∂₂ψ + x₁)`, then `ΔΦ = -2μα`. -/
theorem prandtl_compat {μ : ℝ} (hψ : ContDiff ℝ 2 ψ)
    (h13 : ∀ x, pd Φ 1 x = μ * α * (pd ψ 0 x - x 1))
    (h23 : ∀ x, -pd Φ 0 x = μ * α * (pd ψ 1 x + x 0)) (x : Fin 3 → ℝ) :
    planeLap Φ x = -2 * μ * α := by
  have e0 : pd Φ 0 = fun x => -(μ * α * (pd ψ 1 x + x 0)) := funext fun x => by
    rw [← h23, neg_neg]
  have e1 : pd Φ 1 = fun x => μ * α * (pd ψ 0 x - x 1) := funext h13
  have d : ∀ j, Differentiable ℝ (pd ψ j) := differentiable_pd hψ
  simp (disch := fun_prop) [planeLap, e0, e1, pd_mul, pd_const, pd_neg', pd_add', pd_sub',
    pd_coord, pd_pd_comm hψ 1 0]
  ring

end Prandtl

/-! ### Torque -/

/-- The point `(p₁, p₂, 0)` of the cross-section `x₃ = 0`. -/
def pt (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, p.2, 0]

/-- The **torque** `T = ∫∫_Ω (x₁ τ₂₃ - x₂ τ₁₃)` of the shear stresses over a cross-section `Ω`. -/
def torque (τ₁₃ τ₂₃ : (Fin 3 → ℝ) → ℝ) (Ω : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in Ω, (p.1 * τ₂₃ (pt p) - p.2 * τ₁₃ (pt p))

/-- The **polar moment of area** `J = ∫∫_Ω (x₁² + x₂²)`. -/
def polarMoment (Ω : Set (ℝ × ℝ)) : ℝ := ∫ p in Ω, (p.1 ^ 2 + p.2 ^ 2)

/-- The disk `x₁² + x₂² ≤ R²`. -/
def disk (R : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2}

/-- The disk is measurable (it is closed). -/
theorem measurableSet_disk (R : ℝ) : MeasurableSet (disk R) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- The **polar moment of the disk**: `J = π R⁴ / 2`, computed in polar coordinates. -/
theorem polarMoment_disk {R : ℝ} (hR : 0 ≤ R) : polarMoment (disk R) = π * R ^ 4 / 2 := by
  rw [polarMoment, ← integral_indicator (measurableSet_disk R),
    ← integral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target, p.1 • (disk R).indicator (fun p => p.1 ^ 2 + p.2 ^ 2)
      (polarCoord.symm p) = (Set.Iic R).indicator (fun r => r ^ 3) p.1 * (fun _ => (1 : ℝ)) p.2 :=
    fun p hp => by
    have h1 : 0 < p.1 := hp.1
    have hs : (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2 := by
      have := sin_sq_add_cos_sq p.2
      linear_combination p.1 ^ 2 * this
    by_cases h : p.1 ≤ R
    · have hd : polarCoord.symm p ∈ disk R := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs]
        exact pow_le_pow_left₀ h1.le h 2
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem (Set.mem_Iic.mpr h)]
      simp only [polarCoord_symm_apply, hs, smul_eq_mul]
      ring
    · have hd : polarCoord.symm p ∉ disk R := by
        simp only [disk, polarCoord_symm_apply, Set.mem_ofPred_eq, hs, not_le]
        exact pow_lt_pow_left₀ (lt_of_not_ge h) hR two_ne_zero
      rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (by simpa using h)]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key]
  have hp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    ((Set.Iic R).indicator (fun r => r ^ 3)) (fun _ => (1 : ℝ)) (Set.Ioi 0) (Set.Ioo (-π) π)
  rw [← Measure.volume_eq_prod] at hp
  change ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π, _ = _
  rw [hp, setIntegral_indicator measurableSet_Iic,
    Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hR]
  simp only [integral_pow, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo]
  rw [max_eq_left (by linarith [pi_pos])]
  ring

/-! ### The circular shaft -/

section Circular

variable {μ R : ℝ}

/-- The zero warping function is harmonic. -/
theorem planeLap_zero (x : Fin 3 → ℝ) : planeLap (fun _ => 0) x = 0 := by
  simp [planeLap, pd_const]

/-- Prandtl's stress function of the circular shaft, `Φ = -(μα/2)(x₁² + x₂² - R²)`. -/
def circPhi (μ α R : ℝ) : (Fin 3 → ℝ) → ℝ := fun x => -(μ * α / 2) * (x 0 ^ 2 + x 1 ^ 2 - R ^ 2)

/-- `τ₁₃ = ∂₂Φ = μα(∂₁ψ - x₂)` with `ψ = 0`. -/
theorem circ_tau13 (x : Fin 3 → ℝ) :
    pd (circPhi μ α R) 1 x = μ * α * (pd (fun _ => (0 : ℝ)) 0 x - x 1) := by
  unfold circPhi
  simp (disch := fun_prop) [pd_mul, pd_const, pd_sq, pd_sub', pd_add', pd_coord,
    pd_neg']
  ring

/-- `τ₂₃ = -∂₁Φ = μα(∂₂ψ + x₁)` with `ψ = 0`. -/
theorem circ_tau23 (x : Fin 3 → ℝ) :
    -pd (circPhi μ α R) 0 x = μ * α * (pd (fun _ => (0 : ℝ)) 1 x + x 0) := by
  unfold circPhi
  simp (disch := fun_prop) [pd_mul, pd_const, pd_sq, pd_sub', pd_add', pd_coord,
    pd_neg']
  ring

/-- `ΔΦ = -2μα` for the circular shaft. -/
theorem circ_planeLap (x : Fin 3 → ℝ) : planeLap (circPhi μ α R) x = -2 * μ * α :=
  prandtl_compat contDiff_const circ_tau13 circ_tau23 x

/-- `Φ` vanishes on the lateral boundary `x₁² + x₂² = R²` (traction-free surface). -/
theorem circ_boundary {x : Fin 3 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = R ^ 2) :
    circPhi μ α R x = 0 := by
  simp [circPhi, hx]

/-- **Torque of the circular shaft**: `T = μ α π R⁴ / 2`. -/
theorem torque_circ (hR : 0 ≤ R) :
    torque (pd (circPhi μ α R) 1) (fun x => -pd (circPhi μ α R) 0 x) (disk R) =
      μ * α * (π * R ^ 4 / 2) := by
  rw [← polarMoment_disk hR, polarMoment, ← integral_const_mul, torque]
  congr 1
  funext p
  simp only [circ_tau13, circ_tau23, pd_const, pt]
  simp
  ring

/-- **Coulomb's torsion formula** `T = μ J α`, with `J = π R⁴ / 2` the polar moment. -/
theorem torque_circ_eq (hR : 0 ≤ R) :
    torque (pd (circPhi μ α R) 1) (fun x => -pd (circPhi μ α R) 0 x) (disk R) =
      μ * polarMoment (disk R) * α := by
  rw [torque_circ hR, polarMoment_disk hR]
  ring

end Circular

/-! ### The elliptic bar -/

section Elliptic

/-- Integrals over `ℝ²` under the scaling `(q₁, q₂) ↦ (a q₁, b q₂)`. -/
theorem integral_comp_scale {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) : ∫ q : ℝ × ℝ, g (a * q.1, b * q.2) = |a * b|⁻¹ * ∫ p, g p := by
  have hL : Measurable (Prod.map (a * ·) (b * ·) : ℝ × ℝ → ℝ × ℝ) :=
    (measurable_const_mul a).prodMap (measurable_const_mul b)
  have hmap : Measure.map (Prod.map (a * ·) (b * ·)) (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal |a⁻¹| • ENNReal.ofReal |b⁻¹| • (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (measurable_const_mul a)
      (measurable_const_mul b), Real.map_volume_mul_left ha, Real.map_volume_mul_left hb,
      Measure.prod_smul_left, Measure.prod_smul_right]
  have e := integral_map (μ := volume) hL.aemeasurable (f := g) hg.aestronglyMeasurable
  rw [hmap, integral_smul_measure, integral_smul_measure] at e
  change ∫ q, g (Prod.map (a * ·) (b * ·) q) = _
  rw [← e, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _),
    smul_eq_mul, smul_eq_mul, abs_mul, mul_inv, abs_inv, abs_inv, mul_assoc]

/-- The ellipse `x₁²/a² + x₂²/b² ≤ 1`. -/
def ellipse (a b : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

variable {μ a b : ℝ}

/-- Set integrals over the ellipse reduce to the unit disk. -/
theorem setIntegral_ellipse (ha : 0 < a) (hb : 0 < b) {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ∫ p in ellipse a b, F p = a * b * ∫ q in disk 1, F (a * q.1, b * q.2) := by
  have hE : MeasurableSet (ellipse a b) :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [← integral_indicator hE, ← integral_indicator (measurableSet_disk 1)]
  have hi : ∀ q : ℝ × ℝ, (ellipse a b).indicator F (a * q.1, b * q.2) =
      (disk 1).indicator (fun q => F (a * q.1, b * q.2)) q := fun q => by
    have hm : ((a * q.1, b * q.2) ∈ ellipse a b) ↔ q ∈ disk 1 := by
      simp only [ellipse, disk, Set.mem_ofPred_eq, mul_pow, one_pow]
      rw [mul_div_cancel_left₀ _ (by positivity), mul_div_cancel_left₀ _ (by positivity)]
    by_cases h : q ∈ disk 1
    · rw [Set.indicator_of_mem (hm.mpr h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (mt hm.mp h), Set.indicator_of_notMem h]
  have := integral_comp_scale ha.ne' hb.ne' (hF.measurable.indicator hE)
  simp only [hi] at this
  rw [this, abs_of_pos (mul_pos ha hb), ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The warping function of the elliptic bar, `ψ = -((a² - b²)/(a² + b²)) x₁ x₂`. -/
def ellipPsi (a b : ℝ) : (Fin 3 → ℝ) → ℝ :=
  fun x => -((a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2)) * (x 0 * x 1)

/-- The elliptic warping function is harmonic. -/
theorem ellip_harmonic (x : Fin 3 → ℝ) : planeLap (ellipPsi a b) x = 0 := by
  unfold ellipPsi
  simp (disch := fun_prop) [planeLap, pd_mul, pd_const, pd_coord, pd_neg']

/-- Prandtl's stress function of the elliptic bar,
`Φ = c (x₁²/a² + x₂²/b² - 1)` with `c = -μα a²b²/(a² + b²)`. -/
def ellipPhi (μ α a b : ℝ) : (Fin 3 → ℝ) → ℝ := fun x =>
  -(μ * α * a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) * (x 0 ^ 2 / a ^ 2 + x 1 ^ 2 / b ^ 2 - 1)

/-- `τ₁₃ = ∂₂Φ = μα(∂₁ψ - x₂)`. -/
theorem ellip_tau13 (ha : a ≠ 0) (hb : b ≠ 0) (x : Fin 3 → ℝ) :
    pd (ellipPhi μ α a b) 1 x = μ * α * (pd (ellipPsi a b) 0 x - x 1) := by
  have h : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  unfold ellipPhi ellipPsi
  simp (disch := fun_prop) [pd_mul, pd_const, pd_sq, pd_sub', pd_add',
    pd_coord, pd_neg', div_eq_mul_inv]
  field_simp
  ring

/-- `τ₂₃ = -∂₁Φ = μα(∂₂ψ + x₁)`. -/
theorem ellip_tau23 (ha : a ≠ 0) (hb : b ≠ 0) (x : Fin 3 → ℝ) :
    -pd (ellipPhi μ α a b) 0 x = μ * α * (pd (ellipPsi a b) 1 x + x 0) := by
  have h : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  unfold ellipPhi ellipPsi
  simp (disch := fun_prop) [pd_mul, pd_const, pd_sq, pd_sub', pd_add',
    pd_coord, pd_neg', div_eq_mul_inv]
  field_simp
  ring

/-- `ΔΦ = -2μα` for the elliptic bar. -/
theorem ellip_planeLap (ha : a ≠ 0) (hb : b ≠ 0) (x : Fin 3 → ℝ) :
    planeLap (ellipPhi μ α a b) x = -2 * μ * α :=
  prandtl_compat (by unfold ellipPsi; fun_prop) (ellip_tau13 ha hb) (ellip_tau23 ha hb) x

/-- `Φ` vanishes on the lateral boundary `x₁²/a² + x₂²/b² = 1`. -/
theorem ellip_boundary {x : Fin 3 → ℝ} (hx : x 0 ^ 2 / a ^ 2 + x 1 ^ 2 / b ^ 2 = 1) :
    ellipPhi μ α a b x = 0 := by
  simp [ellipPhi, hx]

/-- **Torque of the elliptic bar**: `T = μ α π a³ b³ / (a² + b²)`. -/
theorem torque_ellip (ha : 0 < a) (hb : 0 < b) :
    torque (pd (ellipPhi μ α a b) 1) (fun x => -pd (ellipPhi μ α a b) 0 x) (ellipse a b) =
      μ * α * π * a ^ 3 * b ^ 3 / (a ^ 2 + b ^ 2) := by
  have h : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hτ : ∀ p : ℝ × ℝ, p.1 * -pd (ellipPhi μ α a b) 0 (pt p) -
      p.2 * pd (ellipPhi μ α a b) 1 (pt p) =
        2 * μ * α / (a ^ 2 + b ^ 2) * (b ^ 2 * p.1 ^ 2 + a ^ 2 * p.2 ^ 2) := fun p => by
    rw [ellip_tau13 ha.ne' hb.ne', ellip_tau23 ha.ne' hb.ne']
    unfold ellipPsi
    simp (disch := fun_prop) [pd_mul, pd_const, pd_coord, pd_neg', pt]
    field_simp
    ring
  rw [torque]
  simp only [hτ]
  rw [setIntegral_ellipse ha hb (by fun_prop), integral_const_mul]
  have hJ : ∫ q in disk 1, (b ^ 2 * (a * q.1) ^ 2 + a ^ 2 * (b * q.2) ^ 2) =
      a ^ 2 * b ^ 2 * (π * 1 ^ 4 / 2) := by
    rw [← polarMoment_disk zero_le_one, polarMoment, ← integral_const_mul]
    congr 1; funext q; ring
  rw [hJ]
  field_simp

end Elliptic

end ContinuumMechanics.Torsion
