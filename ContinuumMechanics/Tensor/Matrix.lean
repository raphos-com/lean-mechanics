import Mathlib.Analysis.CStarAlgebra.Matrix
import ContinuumMechanics.Tensor.Invariants

/-!
# Matrix bridge

Concrete computations use `3 × 3` real matrices: `Matrix.toEuclideanCLM` is a star-algebra
isomorphism `Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Lin (EuclideanSpace ℝ (Fin 3))` (the standard basis
of `ℝ³` is orthonormal). Under it trace, determinant and transpose correspond, so the principal
invariants of a matrix-given tensor can be evaluated with `norm_num`.

This file is for examples and computation only; the theory is coordinate-free.
-/

open scoped ContinuumMechanics

namespace ContinuumMechanics

/-- `ℝ³` with its Euclidean inner product. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The tensor on `ℝ³` with matrix `M` in the standard basis. -/
noncomputable def ofMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) : Lin R3 :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) M

namespace ofMatrix

variable (M N : Matrix (Fin 3) (Fin 3) ℝ)

theorem coe_eq : (ofMatrix M : R3 →ₗ[ℝ] R3) =
    Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis M := rfl

@[simp] theorem tr : Lin.tr (ofMatrix M) = M.trace := by
  rw [Lin.tr_apply, coe_eq, Matrix.trace_toLin_eq]

@[simp] theorem det : (ofMatrix M).det = M.det := by
  rw [ContinuousLinearMap.det, coe_eq, LinearMap.det_toLin]

@[simp] theorem mul : ofMatrix (M * N) = ofMatrix M * ofMatrix N := map_mul _ M N

@[simp] theorem transpose : ofMatrix M.transpose = (ofMatrix M)ᵀ := by
  rw [ofMatrix, ofMatrix, ← map_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

@[simp] theorem one : ofMatrix 1 = 1 := map_one _

@[simp] theorem I₁ : Lin.I₁ (ofMatrix M) = M.trace := tr M

@[simp] theorem I₂ : Lin.I₂ (ofMatrix M) = (M.trace ^ 2 - (M * M).trace) / 2 := by
  rw [Lin.I₂, tr, ← mul, tr]

@[simp] theorem I₃ : Lin.I₃ (ofMatrix M) = M.det := det M

end ofMatrix

section Examples

/-- The principal invariants of `diag(1, 2, 3)`: `I₁ = 6`, `I₂ = 11`, `I₃ = 6`. -/
example : Lin.I₁ (ofMatrix !![1, 0, 0; 0, 2, 0; 0, 0, 3]) = 6 ∧
    Lin.I₂ (ofMatrix !![1, 0, 0; 0, 2, 0; 0, 0, 3]) = 11 ∧
    Lin.I₃ (ofMatrix !![1, 0, 0; 0, 2, 0; 0, 0, 3]) = 6 := by
  simp [Matrix.trace_fin_three, Matrix.det_fin_three]
  norm_num

/-- A simple shear `F = I + γ e₁ ⊗ e₂` is isochoric: `det F = 1`. -/
example (γ : ℝ) : (ofMatrix !![1, γ, 0; 0, 1, 0; 0, 0, 1]).det = 1 := by
  simp [Matrix.det_fin_three]

/-- The right Cauchy–Green tensor of a simple shear has `I₁ = 3 + γ²`. -/
example (γ : ℝ) :
    Lin.I₁ ((ofMatrix !![1, γ, 0; 0, 1, 0; 0, 0, 1])ᵀ * ofMatrix !![1, γ, 0; 0, 1, 0; 0, 0, 1]) =
      3 + γ ^ 2 := by
  rw [← ofMatrix.transpose, ← ofMatrix.mul, ofMatrix.I₁]
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  ring

end Examples

end ContinuumMechanics
