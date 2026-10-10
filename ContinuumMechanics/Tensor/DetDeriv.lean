import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import ContinuumMechanics.Tensor.Contraction

/-!
# Derivative of the determinant (Jacobi's formula)

The determinant is a smooth function on `Lin E`, and its derivative is given by **Jacobi's
formula** ([Gurtin1981], §1.4; [Ciarlet1988], §1.2):

* at the identity, `D det(I)[H] = tr H`;
* at an invertible `F`, `D det(F)[H] = det F · tr(F⁻¹ H) = (det F) F⁻ᵀ : H`.

This is the formula `∂J/∂F = J F⁻ᵀ` used throughout finite elasticity. Mathlib does not provide
it (upstream candidate).

## Main results

* `Lin.contDiff_det`: `det` is smooth.
* `Lin.hasFDerivAt_det_one`: `D det(I) = tr`.
* `Lin.hasFDerivAt_det`: Jacobi's formula at an invertible tensor.
* `Lin.det_mul_tr_inverse_mul`: `det F · tr(F⁻¹ H) = (det F · F⁻ᵀ) : H`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.4.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §1.2.
-/

open Module Polynomial
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The trace as a continuous linear functional. -/
noncomputable def trCLM : Lin E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap tr

@[simp] theorem trCLM_apply (A : Lin E) : trCLM A = tr A := rfl

omit [FiniteDimensional ℝ E] in
/-- In an orthonormal basis the determinant is a polynomial in the entries
`⟪bᵢ, A bⱼ⟫`. -/
theorem det_eq_sum_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E)
    (A : Lin E) :
    A.det = ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) *
      ∏ i, ((innerSL ℝ (b (σ i))).comp (ContinuousLinearMap.apply ℝ E (b i))) A := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b.toBasis, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_coe]

/-- The determinant is smooth on `Lin E`. -/
theorem contDiff_det : ContDiff ℝ ⊤ (fun A : Lin E => A.det) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have h : (fun A : Lin E => A.det) = fun A => ∑ σ : Equiv.Perm (Fin (finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) *
        ∏ i, ((innerSL ℝ (b (σ i))).comp (ContinuousLinearMap.apply ℝ E (b i))) A :=
    funext (det_eq_sum_perm b)
  rw [h]
  fun_prop

theorem differentiable_det : Differentiable ℝ (fun A : Lin E => A.det) :=
  contDiff_det.differentiable (by simp)

/-- `det (I + t H)` is `1 + (tr H) t + O(t²)`, as an explicit polynomial identity. -/
theorem det_one_add_smul (H : Lin E) : ∃ p : ℝ[X], ∀ t : ℝ,
    (1 + t • H).det = 1 + tr H * t + p.eval t * t ^ 2 := by
  classical
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let M := LinearMap.toMatrix b b (H : E →ₗ[ℝ] E)
  refine ⟨(Matrix.det (1 + (X : ℝ[X]) • M.map C)).divX.divX, fun t => ?_⟩
  have e : (1 + t • H).det = Matrix.det (1 + t • M) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, map_add, map_smul]
    congr
    exact LinearMap.toMatrix_one b
  rw [e, Matrix.det_one_add_smul, tr_apply, LinearMap.trace_eq_matrix_trace ℝ b]

/-- **Jacobi's formula at the identity**: `D det(I) = tr`. -/
theorem hasFDerivAt_det_one : HasFDerivAt (fun A : Lin E => A.det) (trCLM : Lin E →L[ℝ] ℝ) 1 := by
  have hd := (differentiable_det (E := E) 1).hasFDerivAt
  convert hd using 1
  ext H
  obtain ⟨p, hp⟩ := det_one_add_smul H
  -- the derivative of `t ↦ det (I + t H)` at `0`, computed in two ways
  have h1 : HasDerivAt (fun t : ℝ => (1 + t • H).det)
      (fderiv ℝ (fun A : Lin E => A.det) 1 H) 0 := by
    have hl : HasDerivAt (fun t : ℝ => (1 : Lin E) + t • H) H 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : Lin E)
    exact hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun t : ℝ => (1 + t • H).det) (tr H) 0 := by
    have hp' : HasDerivAt (fun t : ℝ => 1 + tr H * t + p.eval t * t ^ 2)
        (0 + tr H * 1 + ((derivative p).eval 0 * 0 ^ 2 + p.eval 0 * (2 * 0 ^ 1))) 0 :=
      ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).const_mul (tr H))).add
        ((p.hasDerivAt 0).mul (by simpa using hasDerivAt_pow 2 (0 : ℝ)))
    simp only [zero_add, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, pow_one, add_zero] at hp'
    exact hp'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hp t)
  rw [trCLM_apply]
  exact h2.unique h1

/-- **Jacobi's formula**: at an invertible `F`, `D det(F)[H] = det F · tr(F⁻¹ H)`.
[Gurtin1981], §1.4. -/
theorem hasFDerivAt_det {F : Lin E} (hF : IsUnit F) :
    HasFDerivAt (fun A : Lin E => A.det)
      (F.det • (trCLM.comp (ContinuousLinearMap.mul ℝ (Lin E) F⁻¹ʳ))) F := by
  have hdet : ∀ A : Lin E, A.det = F.det * (F⁻¹ʳ * A).det := fun A => by
    rw [det_mul, ← mul_assoc, ← det_mul, Ring.mul_inverse_cancel _ hF, det_one, one_mul]
  have hL : HasFDerivAt (fun A : Lin E => F⁻¹ʳ * A) (ContinuousLinearMap.mul ℝ (Lin E) F⁻¹ʳ) F :=
    (ContinuousLinearMap.mul ℝ (Lin E) F⁻¹ʳ).hasFDerivAt
  have h1 : F⁻¹ʳ * F = 1 := Ring.inverse_mul_cancel _ hF
  have hd1 : HasFDerivAt (fun A : Lin E => A.det) (trCLM : Lin E →L[ℝ] ℝ) (F⁻¹ʳ * F) := by
    rw [h1]; exact hasFDerivAt_det_one
  have := (hd1.comp F hL).const_mul F.det
  rw [show (fun A : Lin E => A.det) = fun A => F.det * (F⁻¹ʳ * A).det from funext hdet]
  exact this

theorem fderiv_det_apply {F : Lin E} (hF : IsUnit F) (H : Lin E) :
    fderiv ℝ (fun A : Lin E => A.det) F H = F.det * tr (F⁻¹ʳ * H) := by
  rw [(hasFDerivAt_det hF).fderiv]
  simp

/-- `det F · tr(F⁻¹ H) = (det F · F⁻ᵀ) : H`, i.e. `∂J/∂F = J F⁻ᵀ`. -/
theorem det_mul_tr_inverse_mul (F H : Lin E) :
    F.det * tr (F⁻¹ʳ * H) = (F.det • (F⁻¹ʳ)ᵀ) ⊡ H := by
  rw [map_smul, LinearMap.smul_apply, dcontr_apply, transpose_transpose, smul_eq_mul]

end Lin

end ContinuumMechanics
