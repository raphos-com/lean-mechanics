import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import ContinuumMechanics.Tensor.Contraction

/-!
# Principal invariants and the Cayley–Hamilton theorem

The **principal invariants** of a tensor `A` are
`I₁(A) = tr A`, `I₂(A) = ½((tr A)² - tr A²)`, `I₃(A) = det A` ([Gurtin1981], §1.3).
They are defined in every dimension; in dimension three they are the coefficients of the
characteristic polynomial:
`charpoly A = X³ - I₁ X² + I₂ X - I₃`, and the Cayley–Hamilton theorem
(Mathlib's `LinearMap.aeval_self_charpoly`) takes the classical form
`A³ - I₁ A² + I₂ A - I₃ I = 0`.

## Main results

* `Matrix.charpoly_fin_three`: the characteristic polynomial of a `3 × 3` matrix.
* `Lin.charpoly_eq_of_finrank_eq_three`: `charpoly A = X³ - I₁ X² + I₂ X - I₃` when `dim E = 3`.
* `Lin.cayley_hamilton`: `A³ - I₁ A² + I₂ A - I₃ I = 0` when `dim E = 3`.
* `Lin.I₁_conj`, `Lin.I₂_conj`, `Lin.I₃_conj`: invariance under `A ↦ Q A Qᵀ`, `Q` orthogonal
  (stated for `Qᵀ Q = 1`).

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.3.
-/

open Polynomial Module
open scoped InnerProductSpace ContinuumMechanics

/-- The characteristic polynomial of a `3 × 3` matrix: `X³ - (tr M) X² + m₂ X - det M`, where
`m₂` is the sum of the principal `2 × 2` minors. -/
theorem Matrix.charpoly_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2
      + C (M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0
          + M 1 1 * M 2 2 - M 1 2 * M 2 1) * X - C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.det_fin_three, Matrix.trace_fin_three]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq,
    ite_true, ite_false, zero_sub]
  simp only [map_sub, map_add, map_mul]
  ring

/-- Over a field of characteristic zero, the sum of principal `2 × 2` minors of a `3 × 3` matrix
is `½((tr M)² - tr M²)`. -/
theorem Matrix.sum_minors_fin_three (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0
      + M 1 1 * M 2 2 - M 1 2 * M 2 1 = (M.trace ^ 2 - (M * M).trace) / 2 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **first principal invariant** `I₁(A) = tr A`. [Gurtin1981], §1.3. -/
noncomputable def I₁ (A : Lin E) : ℝ := tr A

/-- The **second principal invariant** `I₂(A) = ½((tr A)² - tr A²)`. [Gurtin1981], §1.3. -/
noncomputable def I₂ (A : Lin E) : ℝ := ((tr A) ^ 2 - tr (A * A)) / 2

/-- The **third principal invariant** `I₃(A) = det A`. [Gurtin1981], §1.3. -/
noncomputable def I₃ (A : Lin E) : ℝ := A.det

section Conj

variable [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- `I₁` is invariant under `A ↦ Q A Qᵀ` for orthogonal `Q`. -/
theorem I₁_conj {Q : Lin E} (hQ : Qᵀ * Q = 1) (A : Lin E) : I₁ (Q * A * Qᵀ) = I₁ A := by
  rw [I₁, I₁, tr_mul_comm, ← mul_assoc, hQ, one_mul]

omit [FiniteDimensional ℝ E] in
/-- `I₂` is invariant under `A ↦ Q A Qᵀ` for orthogonal `Q`. -/
theorem I₂_conj {Q : Lin E} (hQ : Qᵀ * Q = 1) (A : Lin E) : I₂ (Q * A * Qᵀ) = I₂ A := by
  have h : Q * A * Qᵀ * (Q * A * Qᵀ) = Q * (A * A) * Qᵀ := by
    calc Q * A * Qᵀ * (Q * A * Qᵀ) = Q * A * (Qᵀ * Q) * A * Qᵀ := by simp only [mul_assoc]
      _ = Q * (A * A) * Qᵀ := by rw [hQ, mul_one, mul_assoc Q A A]
  have h₁ := I₁_conj hQ A
  have h₂ := I₁_conj hQ (A * A)
  rw [I₁] at h₁ h₂
  rw [I₂, I₂, h, h₁, h₂]
  rfl

/-- `I₃` is invariant under `A ↦ Q A Qᵀ` for orthogonal `Q`. -/
theorem I₃_conj {Q : Lin E} (hQ : Qᵀ * Q = 1) (A : Lin E) : I₃ (Q * A * Qᵀ) = I₃ A := by
  have h := congrArg ContinuousLinearMap.det hQ
  rw [det_mul, det_transpose, det_one] at h
  rw [I₃, I₃, det_mul, det_mul, det_transpose]
  linear_combination A.det * h

end Conj

section Dim3

variable [Fact (finrank ℝ E = 3)]

/-- An orthonormal basis of `E` indexed by `Fin 3`. -/
noncomputable def basis3 : OrthonormalBasis (Fin 3) ℝ E :=
  (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)

/-- The matrix of `A` in `basis3`. -/
noncomputable def toMatrix3 (A : Lin E) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix basis3.toBasis basis3.toBasis (A : E →ₗ[ℝ] E)

theorem tr_eq_trace_toMatrix3 (A : Lin E) : tr A = (toMatrix3 A).trace :=
  LinearMap.trace_eq_matrix_trace ℝ basis3.toBasis _

theorem det_eq_det_toMatrix3 (A : Lin E) : A.det = (toMatrix3 A).det :=
  (LinearMap.det_toMatrix basis3.toBasis _).symm

theorem toMatrix3_mul (A B : Lin E) : toMatrix3 (A * B) = toMatrix3 A * toMatrix3 B := by
  rw [toMatrix3, toMatrix3, toMatrix3, ContinuousLinearMap.toLinearMap_mul,
    LinearMap.toMatrix_mul]

/-- In dimension three, `charpoly A = X³ - I₁ X² + I₂ X - I₃`. [Gurtin1981], §1.3. -/
theorem charpoly_eq_of_finrank_eq_three (A : Lin E) :
    (A : E →ₗ[ℝ] E).charpoly = X ^ 3 - C (I₁ A) * X ^ 2 + C (I₂ A) * X - C (I₃ A) := by
  rw [← LinearMap.charpoly_toMatrix _ basis3.toBasis]
  change (toMatrix3 A).charpoly = _
  rw [Matrix.charpoly_fin_three, Matrix.sum_minors_fin_three, I₁, I₂, I₃,
    tr_eq_trace_toMatrix3, tr_eq_trace_toMatrix3, toMatrix3_mul, det_eq_det_toMatrix3]

/-- The **Cayley–Hamilton theorem** in invariant form: `A³ - I₁ A² + I₂ A - I₃ I = 0`
in dimension three. Obtained from Mathlib's `LinearMap.aeval_self_charpoly`.
[Gurtin1981], §1.3. -/
theorem cayley_hamilton (A : Lin E) :
    A * A * A - I₁ A • (A * A) + I₂ A • A - I₃ A • (1 : Lin E) = 0 := by
  have h := LinearMap.aeval_self_charpoly (A : E →ₗ[ℝ] E)
  rw [charpoly_eq_of_finrank_eq_three] at h
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  apply ContinuousLinearMap.coe_injective
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_zero]
  rw [← h]
  simp only [smul_mul_assoc, one_mul, pow_succ, pow_zero, ContinuousLinearMap.one_def,
    ContinuousLinearMap.coe_id]
  rfl

end Dim3

end Lin

section Examples

open Lin

example [CompleteSpace E] (A : Lin E) : I₂ A = (I₁ A ^ 2 - I₁ (A * A)) / 2 := rfl

/-- In dimension three, `A³ = I₁ A² - I₂ A + I₃ I`. -/
example [Fact (finrank ℝ E = 3)] (A : Lin E) :
    A * A * A = I₁ A • (A * A) - I₂ A • A + I₃ A • (1 : Lin E) := by
  have := cayley_hamilton A
  rw [← sub_eq_zero, ← this]
  abel

end Examples

end ContinuumMechanics
