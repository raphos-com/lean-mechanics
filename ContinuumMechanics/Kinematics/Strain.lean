import ContinuumMechanics.Tensor.Polar

/-!
# Finite strain measures

Pointwise strain measures of a deformation gradient `F` ([Gurtin1981], §§6–7; [Ciarlet1988],
§1.8):

* right Cauchy–Green tensor `C = Fᵀ F`, left Cauchy–Green tensor `B = F Fᵀ`;
* Green–Lagrange strain `E = ½ (C - I)`, Almansi strain `e = ½ (I - B⁻¹)`.

These are statements about a single tensor `F : Lin E`; fields are obtained by evaluating at
`F = ∇φ(x)` (see `Kinematics/Body.lean`).

## Main results

* `Lin.rightCG_eq_sq_rightStretch`, `Lin.leftCG_eq_sq_leftStretch`: `C = U²`, `B = V²`.
* `Lin.isStrictlyPositive_rightCG`, `Lin.isStrictlyPositive_leftCG` for invertible `F`.
* `Lin.greenLagrange_eq_transpose_almansi`: `E = Fᵀ e F` (pull-back of the Almansi strain).
* `Lin.rightCG_eq_one_iff`: `C = I` iff `F` is orthogonal (a rigid deformation gradient).

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§6–7.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §1.8.
-/

open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **right Cauchy–Green tensor** `C = Fᵀ F`. [Gurtin1981], §6. -/
noncomputable def rightCG (F : Lin E) : Lin E := Fᵀ * F

/-- The **left Cauchy–Green tensor** `B = F Fᵀ`. [Gurtin1981], §6. -/
noncomputable def leftCG (F : Lin E) : Lin E := F * Fᵀ

/-- The **Green–Lagrange (Green–St. Venant) strain** `E = ½ (C - I)`. [Ciarlet1988], §1.8. -/
noncomputable def greenLagrange (F : Lin E) : Lin E := (2⁻¹ : ℝ) • (rightCG F - 1)

/-- The **Almansi (Euler–Almansi) strain** `e = ½ (I - B⁻¹)`. -/
noncomputable def almansi (F : Lin E) : Lin E := (2⁻¹ : ℝ) • (1 - (leftCG F)⁻¹ʳ)

theorem rightCG_nonneg (F : Lin E) : 0 ≤ rightCG F := transpose_mul_self_nonneg F

theorem leftCG_nonneg (F : Lin E) : 0 ≤ leftCG F := mul_transpose_self_nonneg F

theorem rightCG_mem_sym (F : Lin E) : rightCG F ∈ Sym E := mem_sym_of_nonneg (rightCG_nonneg F)

theorem leftCG_mem_sym (F : Lin E) : leftCG F ∈ Sym E := mem_sym_of_nonneg (leftCG_nonneg F)

theorem greenLagrange_mem_sym (F : Lin E) : greenLagrange F ∈ Sym E :=
  (Sym E).smul_mem _ ((Sym E).sub_mem (rightCG_mem_sym F) (mem_sym_iff.mpr transpose_one))

theorem isStrictlyPositive_rightCG {F : Lin E} (hF : IsUnit F) : IsStrictlyPositive (rightCG F) :=
  isStrictlyPositive_transpose_mul_self hF

theorem isStrictlyPositive_leftCG {F : Lin E} (hF : IsUnit F) : IsStrictlyPositive (leftCG F) :=
  isStrictlyPositive_mul_transpose_self hF

/-- `C = U²` with `U` the right stretch. [Gurtin1981], §6. -/
theorem rightCG_eq_sq_rightStretch (F : Lin E) : rightCG F = rightStretch F * rightStretch F :=
  (rightStretch_mul_self F).symm

/-- `B = V²` with `V` the left stretch. [Gurtin1981], §6. -/
theorem leftCG_eq_sq_leftStretch (F : Lin E) : leftCG F = leftStretch F * leftStretch F :=
  (leftStretch_mul_self F).symm

/-- `det C = (det F)²`. -/
theorem det_rightCG (F : Lin E) : (rightCG F).det = F.det ^ 2 := by
  rw [rightCG, det_mul, det_transpose, sq]

/-- `C = I` iff `F` is orthogonal. [Gurtin1981], §6. -/
theorem rightCG_eq_one_iff {F : Lin E} : rightCG F = 1 ↔ F ∈ Orth E := by
  rw [rightCG, mem_orth_iff]

/-- The Green–Lagrange strain vanishes iff `F` is orthogonal. -/
theorem greenLagrange_eq_zero_iff {F : Lin E} : greenLagrange F = 0 ↔ F ∈ Orth E := by
  rw [greenLagrange, smul_eq_zero, sub_eq_zero, rightCG_eq_one_iff]
  norm_num

/-- `E = Fᵀ e F`: the Green–Lagrange strain is the pull-back of the Almansi strain.
[Ciarlet1988], §1.8. -/
theorem greenLagrange_eq_transpose_almansi {F : Lin E} (hF : IsUnit F) :
    greenLagrange F = Fᵀ * almansi F * F := by
  have hFt : IsUnit Fᵀ := hF.star
  have hB : (leftCG F)⁻¹ʳ = (Fᵀ)⁻¹ʳ * F⁻¹ʳ := by
    rw [leftCG]
    obtain ⟨u, rfl⟩ := hF
    obtain ⟨v, hv⟩ := hFt
    rw [← hv, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit,
      mul_inv_rev, Units.val_mul]
  rw [greenLagrange, almansi, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hB,
    rightCG]
  congr 2
  symm
  calc Fᵀ * ((Fᵀ)⁻¹ʳ * F⁻¹ʳ) * F = (Fᵀ * (Fᵀ)⁻¹ʳ) * (F⁻¹ʳ * F) := by simp only [mul_assoc]
    _ = 1 := by rw [Ring.mul_inverse_cancel _ hFt, Ring.inverse_mul_cancel _ hF, one_mul]

end Lin

section Examples

open Lin

/-- A rigid rotation produces no strain. -/
example {Q : Lin E} (hQ : Q ∈ Orth E) : greenLagrange Q = 0 := greenLagrange_eq_zero_iff.mpr hQ

/-- A uniform dilatation `F = λ I` has `E = ½ (λ² - 1) I`. -/
example (lam : ℝ) : greenLagrange (lam • (1 : Lin E)) = (2⁻¹ * (lam ^ 2 - 1)) • (1 : Lin E) := by
  rw [greenLagrange, rightCG, transpose_smul, transpose_one, smul_mul_smul_comm, one_mul]
  module

end Examples

end ContinuumMechanics
