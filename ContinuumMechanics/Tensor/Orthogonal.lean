import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ContinuumMechanics.Tensor.SymSkew

/-!
# Orthogonal tensors and rotations

An **orthogonal tensor** is a tensor `Q` with `Qᵀ Q = Q Qᵀ = I`, equivalently a linear map
preserving inner products ([Gurtin1981], §1.2). Since the transpose is the star operation on
`Lin E`, the orthogonal group `Orth E` is Mathlib's `unitary (Lin E)`. A **rotation** is an
orthogonal tensor with `det Q = 1`; the rotations form the subgroup `Rot E` of `Orth E`
(Gurtin's `Orth⁺`).

## Main results

* `Lin.mul_eq_one_comm`: in finite dimension, `A B = I ↔ B A = I`.
* `Lin.mem_orth_iff`: `Q ∈ Orth E ↔ Qᵀ Q = I` (one-sided suffices).
* `Lin.mem_orth_iff_inner`: `Q ∈ Orth E ↔ ∀ u v, Q u · Q v = u · v`.
* `Lin.det_eq_one_or_neg_one_of_mem_orth`: `det Q = ±1`.
* `Lin.mem_rot_iff`: `Q ∈ Rot E ↔ det Q = 1`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- `Orth E`, the **orthogonal group**: tensors with `Qᵀ Q = Q Qᵀ = I`. This is Mathlib's
`unitary (Lin E)`, since `Qᵀ = star Q`. [Gurtin1981], §1.2. -/
noncomputable abbrev Orth : Submonoid (Lin E) := unitary (Lin E)

namespace Lin

/-- In finite dimension a one-sided inverse of a tensor is two-sided. -/
theorem mul_eq_one_comm {A B : Lin E} : A * B = 1 ↔ B * A = 1 := by
  have key : ∀ {A B : Lin E}, A * B = 1 → B * A = 1 := fun {A B} h => by
    have h' : (A : E →ₗ[ℝ] E) * (B : E →ₗ[ℝ] E) = 1 := by
      rw [← ContinuousLinearMap.toLinearMap_mul, h]; rfl
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_mul, _root_.mul_eq_one_comm.mp h']
    rfl
  exact ⟨key, key⟩

/-- `Q` is orthogonal iff `Qᵀ Q = I`. [Gurtin1981], §1.2. -/
theorem mem_orth_iff {Q : Lin E} : Q ∈ Orth E ↔ Qᵀ * Q = 1 := by
  rw [Unitary.mem_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, mul_eq_one_comm.mp h⟩⟩

theorem transpose_mul_self_of_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) : Qᵀ * Q = 1 :=
  Unitary.star_mul_self_of_mem hQ

theorem mul_transpose_self_of_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) : Q * Qᵀ = 1 :=
  Unitary.mul_star_self_of_mem hQ

theorem transpose_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) : Qᵀ ∈ Orth E :=
  Unitary.star_mem hQ

/-- `Q` is orthogonal iff it preserves inner products. [Gurtin1981], §1.2. -/
theorem mem_orth_iff_inner {Q : Lin E} : Q ∈ Orth E ↔ ∀ u v, ⟪Q u, Q v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [mem_orth_iff]
  constructor
  · intro h u v
    rw [← inner_transpose_left, show Qᵀ (Q u) = (Qᵀ * Q) u from rfl, h,
      one_apply_eq_self]
  · intro h
    refine ContinuousLinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
    rw [show (Qᵀ * Q) u = Qᵀ (Q u) from rfl, inner_transpose_left, h,
      one_apply_eq_self]

/-- Orthogonal tensors preserve lengths. -/
theorem norm_apply_of_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) (u : E) : ‖Q u‖ = ‖u‖ := by
  have h := mem_orth_iff_inner.mp hQ u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- `(det Q)² = 1` for orthogonal `Q`. -/
theorem det_sq_of_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) : Q.det ^ 2 = 1 := by
  have h := congrArg ContinuousLinearMap.det (transpose_mul_self_of_mem_orth hQ)
  rw [det_mul, det_transpose, det_one] at h
  rw [sq, h]

/-- An orthogonal tensor has determinant `±1`. [Gurtin1981], §1.2. -/
theorem det_eq_one_or_neg_one_of_mem_orth {Q : Lin E} (hQ : Q ∈ Orth E) :
    Q.det = 1 ∨ Q.det = -1 := by
  have h : (Q.det - 1) * (Q.det + 1) = 0 := by linear_combination det_sq_of_mem_orth hQ
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

/-- Conjugation by an orthogonal tensor preserves symmetry. -/
theorem conj_mem_sym {Q S : Lin E} (hS : S ∈ Sym E) : Q * S * Qᵀ ∈ Sym E := by
  rw [mem_sym_iff, transpose_mul, transpose_mul, transpose_transpose, mem_sym_iff.mp hS,
    mul_assoc]

/-- Conjugation by an orthogonal tensor preserves skewness. -/
theorem conj_mem_skw {Q W : Lin E} (hW : W ∈ Skw E) : Q * W * Qᵀ ∈ Skw E := by
  rw [mem_skw_iff, transpose_mul, transpose_mul, transpose_transpose, mem_skw_iff.mp hW,
    neg_mul, mul_neg, mul_assoc]

/-- The determinant, as a monoid homomorphism on the orthogonal group. -/
noncomputable def detOrth : Orth E →* ℝ :=
  LinearMap.det.comp
    ((ContinuousLinearMap.toLinearMapRingHom : Lin E →+* E →ₗ[ℝ] E).toMonoidHom.comp
      (Orth E).subtype)

end Lin

variable (E) in
/-- `Rot E`, the **rotation group** `Orth⁺`: orthogonal tensors with `det Q = 1`, as a subgroup
of `Orth E`. [Gurtin1981], §1.2. -/
noncomputable def Rot : Subgroup (Orth E) := Lin.detOrth.ker

namespace Lin

theorem mem_rot_iff {Q : Orth E} : Q ∈ Rot E ↔ (Q : Lin E).det = 1 := MonoidHom.mem_ker

end Lin

section Examples

open Lin

example : (1 : Lin E) ∈ Orth E := one_mem _

/-- `-I` is orthogonal. -/
example : (-1 : Lin E) ∈ Orth E := by
  rw [mem_orth_iff, star_neg, star_one, neg_mul_neg, one_mul]

/-- In dimension three, `-I` is not a rotation: `det (-I) = -1`. -/
example (h : finrank ℝ E = 3) : (-1 : Lin E).det = -1 := by
  rw [ContinuousLinearMap.det, ← neg_one_smul ℝ (1 : Lin E), ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, h]
  norm_num

end Examples

end ContinuumMechanics
