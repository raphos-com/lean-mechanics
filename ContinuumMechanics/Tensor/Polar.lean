import ContinuumMechanics.Tensor.Orthogonal
import ContinuumMechanics.Tensor.Positive

/-!
# The polar decomposition

Every invertible tensor `F` admits unique decompositions `F = R U = V R` with `R` orthogonal and
`U`, `V` symmetric positive definite: `U = √(FᵀF)` (the **right stretch**), `V = √(FFᵀ)` (the
**left stretch**), `R = F U⁻¹` (the **rotation**), and `V = R U Rᵀ`. Moreover `R` is a rotation
(`det R = 1`) iff `det F > 0`. ([Gurtin1981], §1.4, Polar decomposition theorem.)

Inverses are Mathlib's `Ring.inverse` (notation `A⁻¹ʳ`), which is a two-sided inverse on units.

## Main results

* `Lin.polarRotation_mem_orth`, `Lin.polarRotation_mul_rightStretch`,
  `Lin.leftStretch_mul_polarRotation`: existence of `F = R U = V R`.
* `Lin.leftStretch_eq`: `V = R U Rᵀ`.
* `Lin.polar_right_unique`, `Lin.polar_left_unique`: uniqueness.
* `Lin.det_polarRotation_eq_one_iff`: `det R = 1 ↔ det F > 0`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.4.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The determinant as a monoid homomorphism on `Lin E`. -/
noncomputable def detHom : Lin E →* ℝ :=
  LinearMap.det.comp (ContinuousLinearMap.toLinearMapRingHom : Lin E →+* E →ₗ[ℝ] E).toMonoidHom

omit [FiniteDimensional ℝ E] in
theorem detHom_apply (A : Lin E) : detHom A = A.det := rfl

omit [FiniteDimensional ℝ E] in
theorem det_ne_zero_of_isUnit {A : Lin E} (hA : IsUnit A) : A.det ≠ 0 :=
  (hA.map detHom).ne_zero

/-- A positive semidefinite tensor has nonnegative determinant. -/
theorem det_nonneg_of_nonneg {A : Lin E} (hA : 0 ≤ A) : 0 ≤ A.det := by
  rw [← sqrt_mul_sqrt hA, det_mul]
  exact mul_self_nonneg _

/-- A positive definite tensor has positive determinant. -/
theorem det_pos_of_isStrictlyPositive {A : Lin E} (hA : IsStrictlyPositive A) : 0 < A.det :=
  (det_nonneg_of_nonneg hA.nonneg).lt_of_ne (det_ne_zero_of_isUnit hA.isUnit).symm

theorem transpose_inverse_of_mem_sym {A : Lin E} (hA : A ∈ Sym E) : (A⁻¹ʳ)ᵀ = A⁻¹ʳ := by
  rw [← Ring.inverse_star, mem_sym_iff.mp hA]

/-- The **right stretch tensor** `U = √(FᵀF)`. [Gurtin1981], §1.4. -/
noncomputable def rightStretch (F : Lin E) : Lin E := CFC.sqrt (Fᵀ * F)

/-- The **left stretch tensor** `V = √(FFᵀ)`. [Gurtin1981], §1.4. -/
noncomputable def leftStretch (F : Lin E) : Lin E := CFC.sqrt (F * Fᵀ)

/-- The **rotation** `R = F U⁻¹` of the polar decomposition. [Gurtin1981], §1.4. -/
noncomputable def polarRotation (F : Lin E) : Lin E := F * (rightStretch F)⁻¹ʳ

theorem rightStretch_nonneg (F : Lin E) : 0 ≤ rightStretch F := sqrt_nonneg _

theorem leftStretch_nonneg (F : Lin E) : 0 ≤ leftStretch F := sqrt_nonneg _

theorem rightStretch_mul_self (F : Lin E) : rightStretch F * rightStretch F = Fᵀ * F :=
  sqrt_mul_sqrt (transpose_mul_self_nonneg F)

theorem leftStretch_mul_self (F : Lin E) : leftStretch F * leftStretch F = F * Fᵀ :=
  sqrt_mul_sqrt (mul_transpose_self_nonneg F)

theorem transpose_rightStretch (F : Lin E) : (rightStretch F)ᵀ = rightStretch F :=
  mem_sym_iff.mp (sqrt_mem_sym _)

theorem transpose_leftStretch (F : Lin E) : (leftStretch F)ᵀ = leftStretch F :=
  mem_sym_iff.mp (sqrt_mem_sym _)

variable {F : Lin E}

theorem isStrictlyPositive_rightStretch (hF : IsUnit F) : IsStrictlyPositive (rightStretch F) :=
  isStrictlyPositive_sqrt (isStrictlyPositive_transpose_mul_self hF)

theorem isStrictlyPositive_leftStretch (hF : IsUnit F) : IsStrictlyPositive (leftStretch F) :=
  isStrictlyPositive_sqrt (isStrictlyPositive_mul_transpose_self hF)

/-- **Polar decomposition**: `F = R U`. [Gurtin1981], §1.4. -/
theorem polarRotation_mul_rightStretch (hF : IsUnit F) :
    polarRotation F * rightStretch F = F := by
  rw [polarRotation, mul_assoc, Ring.inverse_mul_cancel _
    (isStrictlyPositive_rightStretch hF).isUnit, mul_one]

/-- The rotation `R = F U⁻¹` is orthogonal. [Gurtin1981], §1.4. -/
theorem polarRotation_mem_orth (hF : IsUnit F) : polarRotation F ∈ Orth E := by
  set U := rightStretch F
  have hU : IsUnit U := (isStrictlyPositive_rightStretch hF).isUnit
  have hUi : (U⁻¹ʳ)ᵀ = U⁻¹ʳ := transpose_inverse_of_mem_sym (sqrt_mem_sym _)
  have hUU : U * U = Fᵀ * F := rightStretch_mul_self F
  rw [mem_orth_iff, polarRotation, transpose_mul, hUi]
  calc U⁻¹ʳ * Fᵀ * (F * U⁻¹ʳ) = U⁻¹ʳ * (Fᵀ * F) * U⁻¹ʳ := by simp only [mul_assoc]
    _ = (U⁻¹ʳ * U) * (U * U⁻¹ʳ) := by rw [← hUU]; simp only [mul_assoc]
    _ = 1 := by rw [Ring.inverse_mul_cancel _ hU, Ring.mul_inverse_cancel _ hU, one_mul]

/-- The left stretch is `V = R U Rᵀ`. [Gurtin1981], §1.4. -/
theorem leftStretch_eq (hF : IsUnit F) :
    leftStretch F = polarRotation F * rightStretch F * (polarRotation F)ᵀ := by
  set R := polarRotation F
  set U := rightStretch F
  have hR : Rᵀ * R = 1 := transpose_mul_self_of_mem_orth (polarRotation_mem_orth hF)
  have hRU : R * U = F := polarRotation_mul_rightStretch hF
  have hUs : Uᵀ = U := transpose_rightStretch F
  apply sqrt_unique (star_right_conjugate_nonneg (rightStretch_nonneg F) R)
  calc R * U * Rᵀ * (R * U * Rᵀ) = R * U * (Rᵀ * R) * U * Rᵀ := by simp only [mul_assoc]
    _ = R * U * (R * U)ᵀ := by
      rw [hR, transpose_mul, hUs]; simp only [mul_one, mul_assoc]
    _ = F * Fᵀ := by rw [hRU]

/-- **Polar decomposition**: `F = V R`. [Gurtin1981], §1.4. -/
theorem leftStretch_mul_polarRotation (hF : IsUnit F) :
    leftStretch F * polarRotation F = F := by
  have hR : (polarRotation F)ᵀ * polarRotation F = 1 :=
    transpose_mul_self_of_mem_orth (polarRotation_mem_orth hF)
  rw [leftStretch_eq hF, mul_assoc, hR, mul_one, polarRotation_mul_rightStretch hF]

/-- **Uniqueness of the right polar decomposition**: if `F = Q W` with `Q` orthogonal and
`W ≥ 0`, then `W = U` and `Q = R`. [Gurtin1981], §1.4. -/
theorem polar_right_unique (hF : IsUnit F) {Q W : Lin E} (hQ : Q ∈ Orth E) (hW : 0 ≤ W)
    (h : Q * W = F) : W = rightStretch F ∧ Q = polarRotation F := by
  have hWs : Wᵀ = W := (nonneg_iff.mp hW).1
  have hWU : rightStretch F = W := by
    apply sqrt_unique hW
    rw [← h, transpose_mul, hWs]
    calc W * W = W * (Qᵀ * Q) * W := by rw [transpose_mul_self_of_mem_orth hQ, mul_one]
      _ = W * Qᵀ * (Q * W) := by simp only [mul_assoc]
  refine ⟨hWU.symm, ?_⟩
  have hU : IsUnit W := hWU ▸ (isStrictlyPositive_rightStretch hF).isUnit
  rw [polarRotation]
  calc Q = Q * (W * W⁻¹ʳ) := by rw [Ring.mul_inverse_cancel _ hU, mul_one]
    _ = F * (rightStretch F)⁻¹ʳ := by rw [hWU, ← mul_assoc, h]

/-- **Uniqueness of the left polar decomposition**: if `F = W Q` with `Q` orthogonal and
`W ≥ 0`, then `W = V` and `Q = R`. [Gurtin1981], §1.4. -/
theorem polar_left_unique (hF : IsUnit F) {Q W : Lin E} (hQ : Q ∈ Orth E) (hW : 0 ≤ W)
    (h : W * Q = F) : W = leftStretch F ∧ Q = polarRotation F := by
  have hWs : Wᵀ = W := (nonneg_iff.mp hW).1
  have hWV : leftStretch F = W := by
    apply sqrt_unique hW
    rw [← h, transpose_mul, hWs]
    calc W * W = W * (Q * Qᵀ) * W := by rw [mul_transpose_self_of_mem_orth hQ, mul_one]
      _ = W * Q * (Qᵀ * W) := by simp only [mul_assoc]
  refine ⟨hWV.symm, ?_⟩
  have hV : IsUnit W := hWV ▸ (isStrictlyPositive_leftStretch hF).isUnit
  calc Q = W⁻¹ʳ * (W * Q) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hV, one_mul]
    _ = W⁻¹ʳ * (W * polarRotation F) := by
        rw [h, ← hWV, leftStretch_mul_polarRotation hF]
    _ = polarRotation F := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hV, one_mul]

/-- The rotation of the polar decomposition is a proper rotation (`det R = 1`) iff
`det F > 0`. [Gurtin1981], §1.4. -/
theorem det_polarRotation_eq_one_iff (hF : IsUnit F) : (polarRotation F).det = 1 ↔ 0 < F.det := by
  have hU := det_pos_of_isStrictlyPositive (isStrictlyPositive_rightStretch hF)
  have hdet : F.det = (polarRotation F).det * (rightStretch F).det := by
    rw [← det_mul, polarRotation_mul_rightStretch hF]
  constructor
  · intro h
    rw [hdet, h, one_mul]
    exact hU
  · intro h
    rcases det_eq_one_or_neg_one_of_mem_orth (polarRotation_mem_orth hF) with h' | h'
    · exact h'
    · rw [hdet, h'] at h
      linarith

end Lin

section Examples

open Lin

/-- The polar decomposition of the identity is trivial. -/
example : rightStretch (1 : Lin E) = 1 := by
  rw [rightStretch, transpose_one, one_mul, CFC.sqrt_one]

/-- For orthogonal `Q`, the polar decomposition is `Q = Q · I`. -/
example {Q : Lin E} (hQ : Q ∈ Orth E) : rightStretch Q = 1 ∧ polarRotation Q = Q := by
  have hF : IsUnit Q := (Unitary.toUnits ⟨Q, hQ⟩).isUnit
  obtain ⟨h₁, h₂⟩ := polar_right_unique hF hQ zero_le_one (mul_one Q)
  exact ⟨h₁.symm, h₂.symm⟩

end Examples

end ContinuumMechanics
