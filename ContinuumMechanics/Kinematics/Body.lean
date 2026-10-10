import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import ContinuumMechanics.Kinematics.Observer

/-!
# Bodies and deformations

The reference configuration of a body is an open set `Ω ⊆ E` ([Gurtin1981], §5). A
**deformation** is a `C¹` map `φ : E → E` whose gradient `F = ∇φ` has positive determinant on `Ω`
(local orientation preservation; [Ciarlet1988], §1.4). Since `Ω` is open, `fderiv` (rather than
`fderivWithin`) is used throughout.

## Main definitions

* `Deformation Ω`, its gradient `F x = ∇φ(x)`, Jacobian `J = det F`, displacement `u = φ - id`.
* `Deformation.changeOfObserver`: `φ* = c + Q φ` for a rotation `Q`.

## Main results

* `Lin.isUnit_iff_det_ne_zero`: a tensor is invertible iff its determinant is nonzero.
* `Deformation.isUnit_grad`: the deformation gradient is invertible on `Ω`.
* `Deformation.grad_displacement`: `∇u = F - I`.
* `Deformation.grad_changeOfObserver`: `F* = Q F`, hence `C* = C` and `B* = Q B Qᵀ`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§5–6.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §1.4.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- A tensor is invertible iff its determinant is nonzero. -/
theorem isUnit_iff_det_ne_zero {F : Lin E} : IsUnit F ↔ F.det ≠ 0 := by
  refine ⟨det_ne_zero_of_isUnit, fun h => ?_⟩
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det (F : E →ₗ[ℝ] E)).mpr (isUnit_iff_ne_zero.mpr h)
  let G : Lin E := LinearMap.toContinuousLinearMap (↑u⁻¹ : E →ₗ[ℝ] E)
  have h1 : F * G = 1 := by
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_mul, ← hu]
    exact u.mul_inv
  exact ⟨⟨F, G, h1, mul_eq_one_comm.mp h1⟩, rfl⟩

end Lin

/-- A **deformation** of the body occupying the open set `Ω`: a `C¹` map with positive Jacobian
on `Ω`. [Gurtin1981], §5; [Ciarlet1988], §1.4. -/
structure Deformation (Ω : Set E) where
  /-- The deformation map `φ`. -/
  toFun : E → E
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 1 toFun Ω
  det_pos : ∀ x ∈ Ω, 0 < (fderiv ℝ toFun x).det

namespace Deformation

variable {Ω : Set E} (φ : Deformation Ω)

instance : CoeFun (Deformation Ω) fun _ => E → E := ⟨Deformation.toFun⟩

/-- The **deformation gradient** `F = ∇φ`. [Gurtin1981], §5. -/
noncomputable def grad (x : E) : Lin E := fderiv ℝ φ x

/-- The **Jacobian** `J = det F`. -/
noncomputable def jac (x : E) : ℝ := (φ.grad x).det

/-- The **displacement** `u = φ - id`. [Gurtin1981], §5. -/
def displacement : E → E := fun x => φ x - x

omit [FiniteDimensional ℝ E] in
theorem differentiableAt {x : E} (hx : x ∈ Ω) : DifferentiableAt ℝ φ x :=
  (φ.contDiffOn.contDiffAt (φ.isOpen.mem_nhds hx)).differentiableAt (by norm_num)

omit [FiniteDimensional ℝ E] in
theorem jac_pos {x : E} (hx : x ∈ Ω) : 0 < φ.jac x := φ.det_pos x hx

theorem isUnit_grad {x : E} (hx : x ∈ Ω) : IsUnit (φ.grad x) :=
  Lin.isUnit_iff_det_ne_zero.mpr (φ.det_pos x hx).ne'

omit [FiniteDimensional ℝ E] in
/-- `∇u = F - I`. [Gurtin1981], §5. -/
theorem grad_displacement {x : E} (hx : x ∈ Ω) :
    fderiv ℝ φ.displacement x = φ.grad x - 1 := by
  change fderiv ℝ (fun y => φ y - y) x = _
  rw [fderiv_fun_sub (φ.differentiableAt hx) differentiableAt_fun_id, fderiv_fun_id]
  rfl

/-- **Change of observer** `φ* = c + Q φ` for a tensor `Q` with `det Q = 1` (in applications
`Q` is a rotation, `Q ∈ Orth E`). [Gurtin1981], §18. -/
noncomputable def changeOfObserver (c : E) {Q : Lin E} (hdet : Q.det = 1) :
    Deformation Ω where
  toFun x := c + Q (φ x)
  isOpen := φ.isOpen
  contDiffOn := contDiffOn_const.add (Q.contDiff.comp_contDiffOn φ.contDiffOn)
  det_pos x hx := by
    have h : fderiv ℝ (fun y => c + Q (φ y)) x = Q * φ.grad x := by
      rw [fderiv_const_add, fderiv_fun_comp x Q.differentiableAt (φ.differentiableAt hx),
        ContinuousLinearMap.fderiv]
      rfl
    rw [h, Lin.det_mul, hdet, one_mul]
    exact φ.det_pos x hx

omit [FiniteDimensional ℝ E] in
/-- Under a change of observer, `F* = Q F`. [Gurtin1981], §18. -/
theorem grad_changeOfObserver (c : E) {Q : Lin E} (hdet : Q.det = 1) {x : E}
    (hx : x ∈ Ω) : (φ.changeOfObserver c hdet).grad x = Q * φ.grad x := by
  change fderiv ℝ (fun y => c + Q (φ y)) x = _
  rw [fderiv_const_add, fderiv_fun_comp x Q.differentiableAt (φ.differentiableAt hx),
    ContinuousLinearMap.fderiv]
  rfl

/-- The right Cauchy–Green tensor is observer-invariant: `C* = C`. -/
theorem rightCG_changeOfObserver (c : E) {Q : Lin E} (hQ : Q ∈ Orth E) (hdet : Q.det = 1)
    {x : E} (hx : x ∈ Ω) :
    Lin.rightCG ((φ.changeOfObserver c hdet).grad x) = Lin.rightCG (φ.grad x) := by
  rw [φ.grad_changeOfObserver c hdet hx, Lin.rightCG_orth_mul _ hQ]

/-- The left Cauchy–Green tensor is objective: `B* = Q B Qᵀ`. -/
theorem leftCG_changeOfObserver (c : E) {Q : Lin E} (hdet : Q.det = 1)
    {x : E} (hx : x ∈ Ω) :
    Lin.leftCG ((φ.changeOfObserver c hdet).grad x) = Q * Lin.leftCG (φ.grad x) * Qᵀ := by
  rw [φ.grad_changeOfObserver c hdet hx, Lin.leftCG_orth_mul]

end Deformation

section Examples

/-- The identity is a deformation of any open body, with `F = I`. -/
noncomputable example {Ω : Set E} (hΩ : IsOpen Ω) : Deformation Ω where
  toFun := id
  isOpen := hΩ
  contDiffOn := contDiff_id.contDiffOn
  det_pos x _ := by rw [fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id]; norm_num

end Examples

end ContinuumMechanics
