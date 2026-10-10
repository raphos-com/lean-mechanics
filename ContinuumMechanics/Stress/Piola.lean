import ContinuumMechanics.Kinematics.Body

/-!
# Piola–Kirchhoff stresses

Given the Cauchy stress `σ` (spatial, force per deformed area) and an invertible deformation
gradient `F` with `J = det F`, the **first Piola–Kirchhoff stress** is `P = J σ F⁻ᵀ` (force per
reference area) and the **second Piola–Kirchhoff stress** is `S = F⁻¹ P = J F⁻¹ σ F⁻ᵀ`
([Gurtin1981], §§24–25; [Ciarlet1988], §2.5).

## Main results

* `Lin.cauchy_of_firstPK`, `Lin.firstPK_eq_mul_secondPK`, `Lin.cauchy_of_secondPK`:
  the conversions `σ = J⁻¹ P Fᵀ`, `P = F S`, `σ = J⁻¹ F S Fᵀ`.
* `Lin.secondPK_mem_sym_iff`, `Lin.firstPK_mul_transpose_mem_sym_iff`:
  `σ` symmetric ⇔ `S` symmetric ⇔ `P Fᵀ` symmetric.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§24–25.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §2.5.
-/

open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **first Piola–Kirchhoff stress** `P = J σ F⁻ᵀ`. [Gurtin1981], §24. -/
noncomputable def firstPK (F σ : Lin E) : Lin E := F.det • (σ * (F⁻¹ʳ)ᵀ)

/-- The **second Piola–Kirchhoff stress** `S = F⁻¹ P = J F⁻¹ σ F⁻ᵀ`. [Gurtin1981], §25. -/
noncomputable def secondPK (F σ : Lin E) : Lin E := F⁻¹ʳ * firstPK F σ

variable {F : Lin E} (hF : IsUnit F) (σ : Lin E)
include hF

theorem transpose_inverse_mul_transpose : (F⁻¹ʳ)ᵀ * Fᵀ = 1 := by
  rw [← transpose_mul, Ring.mul_inverse_cancel _ hF, transpose_one]

theorem transpose_mul_transpose_inverse : Fᵀ * (F⁻¹ʳ)ᵀ = 1 := by
  rw [← transpose_mul, Ring.inverse_mul_cancel _ hF, transpose_one]

/-- `P = F S`. [Gurtin1981], §25. -/
theorem firstPK_eq_mul_secondPK : firstPK F σ = F * secondPK F σ := by
  rw [secondPK, ← mul_assoc, Ring.mul_inverse_cancel _ hF, one_mul]

/-- `σ = J⁻¹ P Fᵀ`. [Gurtin1981], §24. -/
theorem cauchy_of_firstPK : σ = F.det⁻¹ • (firstPK F σ * Fᵀ) := by
  have hJ : F.det ≠ 0 := det_ne_zero_of_isUnit hF
  rw [firstPK, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hJ, one_smul, mul_assoc,
    transpose_inverse_mul_transpose hF, mul_one]

/-- `σ = J⁻¹ F S Fᵀ`. [Gurtin1981], §25. -/
theorem cauchy_of_secondPK : σ = F.det⁻¹ • (F * secondPK F σ * Fᵀ) := by
  rw [← firstPK_eq_mul_secondPK hF]
  exact cauchy_of_firstPK hF σ

omit hF in
/-- `S = J F⁻¹ σ F⁻ᵀ`. -/
theorem secondPK_eq : secondPK F σ = F.det • (F⁻¹ʳ * σ * (F⁻¹ʳ)ᵀ) := by
  rw [secondPK, firstPK, mul_smul_comm, mul_assoc]

/-- `σ` is symmetric iff `S` is. [Gurtin1981], §25. -/
theorem secondPK_mem_sym_iff : secondPK F σ ∈ Sym E ↔ σ ∈ Sym E := by
  have hJ : F.det ≠ 0 := det_ne_zero_of_isUnit hF
  rw [secondPK_eq (F := F) σ, mem_sym_iff, mem_sym_iff, transpose_smul, transpose_mul,
    transpose_mul,
    transpose_transpose]
  constructor
  · intro h
    have h' := smul_right_injective _ hJ h
    have := congrArg (fun X => F * X * Fᵀ) h'
    have e1 : F * (F⁻¹ʳ * (σᵀ * (F⁻¹ʳ)ᵀ)) * Fᵀ = σᵀ := by
      calc F * (F⁻¹ʳ * (σᵀ * (F⁻¹ʳ)ᵀ)) * Fᵀ = (F * F⁻¹ʳ) * σᵀ * ((F⁻¹ʳ)ᵀ * Fᵀ) := by
            simp only [mul_assoc]
        _ = σᵀ := by rw [Ring.mul_inverse_cancel _ hF, transpose_inverse_mul_transpose hF,
            one_mul, mul_one]
    have e2 : F * (F⁻¹ʳ * σ * (F⁻¹ʳ)ᵀ) * Fᵀ = σ := by
      calc F * (F⁻¹ʳ * σ * (F⁻¹ʳ)ᵀ) * Fᵀ = (F * F⁻¹ʳ) * σ * ((F⁻¹ʳ)ᵀ * Fᵀ) := by
            simp only [mul_assoc]
        _ = σ := by rw [Ring.mul_inverse_cancel _ hF, transpose_inverse_mul_transpose hF,
            one_mul, mul_one]
    rw [e1, e2] at this
    exact this
  · intro h
    rw [h, mul_assoc]

/-- `σ` is symmetric iff `P Fᵀ` is (the referential form of the balance of angular momentum).
[Gurtin1981], §24. -/
theorem firstPK_mul_transpose_mem_sym_iff : firstPK F σ * Fᵀ ∈ Sym E ↔ σ ∈ Sym E := by
  have hJ : F.det ≠ 0 := det_ne_zero_of_isUnit hF
  have e : firstPK F σ * Fᵀ = F.det • σ := by
    rw [firstPK, smul_mul_assoc, mul_assoc, transpose_inverse_mul_transpose hF, mul_one]
  rw [e, mem_sym_iff, mem_sym_iff, transpose_smul]
  exact ⟨fun h => smul_right_injective _ hJ h, fun h => by rw [h]⟩

end Lin

section Examples

open Lin

/-- With no deformation, all three stress measures coincide. -/
example (σ : Lin E) : firstPK 1 σ = σ ∧ secondPK 1 σ = σ := by
  have h1 : (1 : Lin E)⁻¹ʳ = 1 := Ring.inverse_one (Lin E)
  refine ⟨?_, ?_⟩ <;> simp [firstPK, secondPK, h1]

end Examples

end ContinuumMechanics
