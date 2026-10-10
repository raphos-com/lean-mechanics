import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Topology.Algebra.Module.Determinant
import ContinuumMechanics.Basic.Notation

/-!
# Second-order tensors

A *second-order tensor* on a real inner product space `E` is a linear map `E → E`
([Gurtin1981], §1.2). We model it as Mathlib's `E →L[ℝ] E` through the abbreviation
`Lin E`, so all of Mathlib's structure applies unchanged: the ring structure
(product = composition, `1` = identity), the star structure (`star A = Aᵀ` is the
Hilbert adjoint), the determinant `ContinuousLinearMap.det`.

## Main definitions

* `ContinuumMechanics.Lin E`: second-order tensors on `E`.
* `ContinuumMechanics.Lin.tr`: the trace, as a linear functional.
* `ContinuumMechanics.dyad a b` (notation `a ⊗ b`): the dyadic (tensor) product,
  `(a ⊗ b) v = ⟪b, v⟫ a`.

## Main results

* `Lin.tr_transpose`, `Lin.det_transpose`: `tr Aᵀ = tr A`, `det Aᵀ = det A`.
* `Lin.tr_mul_comm`: `tr (A B) = tr (B A)`.
* Algebra of dyads: transpose, products, trace.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Lin E`, the space of **second-order tensors** on `E`: (continuous) linear maps `E → E`.
In finite dimension every linear map is continuous, so this is Gurtin's `Lin`.
[Gurtin1981], §1.2. -/
abbrev Lin := E →L[ℝ] E

variable {E}

namespace Lin

/-- Application of a product of tensors: `(A B) v = A (B v)`. -/
@[simp] theorem mul_apply (A B : Lin E) (v : E) : (A * B) v = A (B v) := rfl

section Transpose

variable [CompleteSpace E]

/-- The transpose `Aᵀ` is the adjoint. [Gurtin1981], §1.2. -/
theorem transpose_eq_adjoint (A : Lin E) : Aᵀ = ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.star_eq_adjoint A

/-- Defining property of the transpose: `Aᵀ u · v = u · A v`. [Gurtin1981], §1.2. -/
theorem inner_transpose_left (A : Lin E) (u v : E) : ⟪Aᵀ u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left A v u

/-- Defining property of the transpose: `u · Aᵀ v = A u · v`. [Gurtin1981], §1.2. -/
theorem inner_transpose_right (A : Lin E) (u v : E) : ⟪u, Aᵀ v⟫_ℝ = ⟪A u, v⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_right A u v

theorem transpose_transpose (A : Lin E) : Aᵀᵀ = A := star_star A

theorem transpose_mul (A B : Lin E) : (A * B)ᵀ = Bᵀ * Aᵀ := star_mul A B

theorem transpose_one : (1 : Lin E)ᵀ = 1 := star_one _

theorem transpose_add (A B : Lin E) : (A + B)ᵀ = Aᵀ + Bᵀ := star_add A B

theorem transpose_smul (c : ℝ) (A : Lin E) : (c • A)ᵀ = c • Aᵀ := by
  rw [star_smul, star_trivial]

/-- Uniqueness of the transpose: if `B u · v = u · A v` for all `u v`, then `B = Aᵀ`. -/
theorem eq_transpose_of_inner {A B : Lin E} (h : ∀ u v, ⟪B u, v⟫_ℝ = ⟪u, A v⟫_ℝ) : B = Aᵀ := by
  rw [transpose_eq_adjoint]
  exact ContinuousLinearMap.eq_adjoint_iff B A |>.mpr fun u v => h u v

end Transpose

section Trace

/-- The **trace** of a second-order tensor, as a linear functional on `Lin E`.
It is Mathlib's `LinearMap.trace` applied to the underlying linear map. [Gurtin1981], §1.2. -/
noncomputable def tr : Lin E →ₗ[ℝ] ℝ :=
  (LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)

theorem tr_apply (A : Lin E) : tr A = LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) := rfl

/-- The trace in an orthonormal basis: `tr A = ∑ᵢ eᵢ · A eᵢ`. -/
theorem tr_eq_sum_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A : Lin E) :
    tr A = ∑ i, ⟪b i, A (b i)⟫_ℝ :=
  LinearMap.trace_eq_sum_inner _ b

/-- Cyclicity of the trace: `tr (A B) = tr (B A)`. -/
theorem tr_mul_comm (A B : Lin E) : tr (A * B) = tr (B * A) := by
  simp only [tr_apply, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.trace_mul_comm ℝ _ _

variable [FiniteDimensional ℝ E]

@[simp]
theorem tr_one : tr (1 : Lin E) = Module.finrank ℝ E := by
  rw [tr_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.trace_id]

/-- `tr Aᵀ = tr A`. [Gurtin1981], §1.2. -/
@[simp]
theorem tr_transpose (A : Lin E) : tr Aᵀ = tr A := by
  let b := stdOrthonormalBasis ℝ E
  rw [tr_eq_sum_inner b, tr_eq_sum_inner b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_transpose_right, real_inner_comm]

end Trace

section Det

@[simp]
theorem det_one : (1 : Lin E).det = 1 := by
  simp [ContinuousLinearMap.det]

theorem det_mul (A B : Lin E) : (A * B).det = A.det * B.det := by
  simp [ContinuousLinearMap.det]

variable [FiniteDimensional ℝ E]

/-- `det Aᵀ = det A`. [Gurtin1981], §1.2. -/
@[simp]
theorem det_transpose (A : Lin E) : (Aᵀ).det = A.det := by
  let b := (stdOrthonormalBasis ℝ E)
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, transpose_eq_adjoint,
    ← ContinuousLinearMap.adjoint_toLinearMap, ← LinearMap.det_toMatrix b.toBasis,
    ← LinearMap.det_toMatrix b.toBasis (A : E →ₗ[ℝ] E), LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose, star_trivial]

end Det

end Lin

section Dyad

/-- The **dyadic product** `a ⊗ b` of two vectors: the tensor `v ↦ (b · v) a`.
[Gurtin1981], §1.2. -/
noncomputable def dyad (a b : E) : Lin E :=
  (innerSL ℝ b).smulRight a

@[inherit_doc] scoped infixl:70 " ⊗ " => dyad

@[simp]
theorem dyad_apply (a b v : E) : (a ⊗ b) v = ⟪b, v⟫_ℝ • a := rfl

/-- `(a ⊗ b) (c ⊗ d) = (b · c) a ⊗ d`. [Gurtin1981], §1.2. -/
theorem dyad_mul_dyad (a b c d : E) : (a ⊗ b) * (c ⊗ d) = ⟪b, c⟫_ℝ • (a ⊗ d) := by
  ext v
  simp [smul_smul, mul_comm]

/-- `A (a ⊗ b) = (A a) ⊗ b`. [Gurtin1981], §1.2. -/
theorem mul_dyad (A : Lin E) (a b : E) : A * (a ⊗ b) = (A a) ⊗ b := by
  ext v
  simp

/-- `tr (a ⊗ b) = a · b`. [Gurtin1981], §1.2. -/
@[simp]
theorem tr_dyad [FiniteDimensional ℝ E] (a b : E) : Lin.tr (a ⊗ b) = ⟪a, b⟫_ℝ := by
  have : ((a ⊗ b : Lin E) : E →ₗ[ℝ] E) = ((innerSL ℝ b : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ).smulRight a := by
    ext v; simp
  rw [Lin.tr_apply, this, LinearMap.trace_smulRight]
  simp [real_inner_comm]

variable [CompleteSpace E]

/-- `(a ⊗ b)ᵀ = b ⊗ a`. [Gurtin1981], §1.2. -/
theorem dyad_transpose (a b : E) : (a ⊗ b)ᵀ = b ⊗ a := by
  symm
  refine Lin.eq_transpose_of_inner fun u v => ?_
  simp [inner_smul_left, inner_smul_right, real_inner_comm, mul_comm]

/-- `(a ⊗ b) A = a ⊗ (Aᵀ b)`. [Gurtin1981], §1.2. -/
theorem dyad_mul (A : Lin E) (a b : E) : (a ⊗ b) * A = a ⊗ (Aᵀ b) := by
  ext v
  simp [Lin.inner_transpose_left]

end Dyad

section Examples

variable [CompleteSpace E] [FiniteDimensional ℝ E]

example (A B : Lin E) : Lin.tr ((A * B)ᵀ) = Lin.tr (A * B) := Lin.tr_transpose _

example (a b : E) : ((a ⊗ b) * (a ⊗ b)) = ⟪b, a⟫_ℝ • (a ⊗ b) := dyad_mul_dyad a b a b

/-- In `ℝ³` the identity has trace `3`. -/
example : Lin.tr (1 : Lin (EuclideanSpace ℝ (Fin 3))) = 3 := by simp

end Examples

end ContinuumMechanics
