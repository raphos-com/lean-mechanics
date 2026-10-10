import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Transfer
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import ContinuumMechanics.Tensor.SymSkew

/-!
# Positive tensors and square roots

Mathlib provides the continuous functional calculus (CFC) for complex operators and for real
matrices, but not for operators on a *real* inner product space. For finite-dimensional `E` we
transfer the matrix CFC to `Lin E` along the star-algebra isomorphism given by an orthonormal
basis (`ContinuousFunctionalCalculus.transfer`). This makes the whole CFC API available on
`Lin E`: in particular `CFC.sqrt`, the unique positive square root, used for the stretch tensors
`U = √(FᵀF)`, `V = √(FFᵀ)` of the polar decomposition.

The order on `Lin E` is Mathlib's Loewner order: `0 ≤ A ↔ A.IsPositive`, i.e. `A` is symmetric
and `A v · v ≥ 0` for all `v`. **Positive definite** tensors (Gurtin's `Psym`) are those with
`IsStrictlyPositive A`, i.e. `0 ≤ A` and `A` invertible.

## Main definitions

* `Lin.matrixStarAlgEquiv`: `Matrix (Fin d) (Fin d) ℝ ≃⋆ₐ[ℝ] Lin E` from an orthonormal basis.
* instance `ContinuousFunctionalCalculus ℝ (Lin E) IsSelfAdjoint` (global, see `ROADMAP.md`).
* instance `StarOrderedRing (Lin E)`.

## Main results

* `Lin.nonneg_iff`: `0 ≤ A ↔ Aᵀ = A ∧ ∀ v, 0 ≤ A v · v`.
* `Lin.sqrt_mul_sqrt`, `Lin.sqrt_nonneg`, `Lin.sqrt_unique`: existence and uniqueness of the
  positive square root. [Gurtin1981], §1.4, Square-root theorem.
* `Lin.transpose_mul_self_nonneg`, `Lin.isStrictlyPositive_transpose_mul_self`:
  `FᵀF ≥ 0`, and `FᵀF` is positive definite for invertible `F`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.4.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics NNReal

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The star-algebra isomorphism between `d × d` real matrices (`d = dim E`) and `Lin E` induced
by `stdOrthonormalBasis`. -/
noncomputable def matrixStarAlgEquiv :
    Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ ≃⋆ₐ[ℝ] Lin E :=
  (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℝ E)).symm.trans
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }

theorem continuous_matrixStarAlgEquiv : Continuous (matrixStarAlgEquiv (E := E)) :=
  (matrixStarAlgEquiv (E := E)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

-- upstream candidate
/-- The **continuous functional calculus** for symmetric tensors on a finite-dimensional real
inner product space, transferred from real matrices. -/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (Lin E) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.transfer matrixStarAlgEquiv continuous_matrixStarAlgEquiv
    fun M => ⟨fun h => h.map _, fun h => by
      simpa using h.map (matrixStarAlgEquiv (E := E)).symm⟩

-- upstream candidate
instance instStarOrderedRing : StarOrderedRing (Lin E) :=
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- `0 ≤ A` (Loewner order) iff `A` is symmetric and `A v · v ≥ 0` for all `v`. -/
theorem nonneg_iff {A : Lin E} : 0 ≤ A ↔ Aᵀ = A ∧ ∀ v, 0 ≤ ⟪A v, v⟫_ℝ := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff',
    transpose_eq_adjoint]
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]

theorem mem_sym_of_nonneg {A : Lin E} (hA : 0 ≤ A) : A ∈ Sym E :=
  mem_sym_iff.mpr (nonneg_iff.mp hA).1

/-- `Fᵀ F` is positive semidefinite. -/
theorem transpose_mul_self_nonneg (F : Lin E) : 0 ≤ Fᵀ * F := star_mul_self_nonneg F

/-- `F Fᵀ` is positive semidefinite. -/
theorem mul_transpose_self_nonneg (F : Lin E) : 0 ≤ F * Fᵀ := mul_star_self_nonneg F

/-- For invertible `F`, `Fᵀ F` is positive definite. -/
theorem isStrictlyPositive_transpose_mul_self {F : Lin E} (hF : IsUnit F) :
    IsStrictlyPositive (Fᵀ * F) :=
  ⟨transpose_mul_self_nonneg F, hF.star.mul hF⟩

/-- For invertible `F`, `F Fᵀ` is positive definite. -/
theorem isStrictlyPositive_mul_transpose_self {F : Lin E} (hF : IsUnit F) :
    IsStrictlyPositive (F * Fᵀ) :=
  ⟨mul_transpose_self_nonneg F, hF.mul hF.star⟩

/-! ### Square roots -/

/-- **Square-root theorem** (existence): `√A √A = A` for `A ≥ 0`. [Gurtin1981], §1.4. -/
theorem sqrt_mul_sqrt {A : Lin E} (hA : 0 ≤ A) : CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA

/-- The square root is positive semidefinite. -/
theorem sqrt_nonneg (A : Lin E) : 0 ≤ CFC.sqrt A := CFC.sqrt_nonneg A

/-- The square root is symmetric. -/
theorem sqrt_mem_sym (A : Lin E) : CFC.sqrt A ∈ Sym E := mem_sym_of_nonneg (sqrt_nonneg A)

/-- **Square-root theorem** (uniqueness): if `B ≥ 0` and `B B = A`, then `B = √A`.
[Gurtin1981], §1.4. -/
theorem sqrt_unique {A B : Lin E} (hB : 0 ≤ B) (h : B * B = A) : CFC.sqrt A = B :=
  CFC.sqrt_unique h hB

/-- The square root of a positive definite tensor is positive definite. -/
theorem isStrictlyPositive_sqrt {A : Lin E} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (CFC.sqrt A) :=
  IsStrictlyPositive.sqrt A hA

end Lin

section Examples

open Lin

example : CFC.sqrt (1 : Lin E) = 1 := CFC.sqrt_one

/-- `√(4 I) = 2 I`. -/
example : CFC.sqrt ((4 : ℝ) • (1 : Lin E)) = (2 : ℝ) • 1 := by
  apply sqrt_unique
  · exact smul_nonneg (by norm_num) zero_le_one
  · rw [smul_mul_smul_comm, one_mul]; norm_num

end Examples

end ContinuumMechanics
