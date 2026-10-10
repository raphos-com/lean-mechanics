import ContinuumMechanics.Tensor.Contraction

/-!
# Spherical and deviatoric parts

For a tensor `A` on a space of dimension `d = finrank ℝ E ≥ 1`, the **spherical part** is
`sph A = (tr A / d) I` and the **deviatoric part** is `dev A = A - sph A`
([Gurtin1981], §1.2; [Ciarlet1988], §3.8).

## Main results

* `Lin.sph_add_dev`: `A = sph A + dev A`.
* `Lin.tr_dev`: the deviator is traceless.
* `Lin.sph_dcontr_dev`: spherical and deviatoric tensors are orthogonal.
* `Lin.dev_mem_sym`: the deviator of a symmetric tensor is symmetric.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §3.8.
-/

open scoped InnerProductSpace ContinuumMechanics
open Module

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **spherical part** `sph A = (tr A / d) I`, `d = dim E`, as a linear map. -/
noncomputable def sph : Lin E →ₗ[ℝ] Lin E :=
  (finrank ℝ E : ℝ)⁻¹ • tr.smulRight (1 : Lin E)

/-- The **deviatoric part** `dev A = A - sph A`, as a linear map. -/
noncomputable def dev : Lin E →ₗ[ℝ] Lin E := LinearMap.id - sph

omit [FiniteDimensional ℝ E] in
theorem sph_apply (A : Lin E) : sph A = (tr A / finrank ℝ E) • (1 : Lin E) := by
  simp [sph, smul_smul, div_eq_inv_mul]

omit [FiniteDimensional ℝ E] in
theorem dev_apply (A : Lin E) : dev A = A - sph A := rfl

omit [FiniteDimensional ℝ E] in
/-- `A = sph A + dev A`. -/
@[simp]
theorem sph_add_dev (A : Lin E) : sph A + dev A = A := by
  rw [dev_apply, add_sub_cancel]

theorem sph_mem_sym (A : Lin E) : sph A ∈ Sym E := by
  rw [mem_sym_iff, sph_apply, transpose_smul, transpose_one]

theorem dev_mem_sym {A : Lin E} (hA : A ∈ Sym E) : dev A ∈ Sym E :=
  (Sym E).sub_mem hA (sph_mem_sym A)

variable [Nontrivial E]

@[simp]
theorem tr_sph (A : Lin E) : tr (sph A) = tr A := by
  have : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  rw [sph_apply, map_smul, tr_one, smul_eq_mul, div_mul_cancel₀ _ this]

/-- The deviator is traceless. -/
@[simp]
theorem tr_dev (A : Lin E) : tr (dev A) = 0 := by
  rw [dev_apply, map_sub, tr_sph, sub_self]

@[simp]
theorem sph_sph (A : Lin E) : sph (sph A) = sph A := by
  rw [sph_apply (sph A), tr_sph, sph_apply]

@[simp]
theorem sph_dev (A : Lin E) : sph (dev A) = 0 := by
  rw [sph_apply, tr_dev, zero_div, zero_smul]

@[simp]
theorem dev_dev (A : Lin E) : dev (dev A) = dev A := by
  rw [dev_apply (dev A), sph_dev, sub_zero]

@[simp]
theorem dev_sph (A : Lin E) : dev (sph A) = 0 := by
  rw [dev_apply, sph_sph, sub_self]

/-- Spherical and deviatoric tensors are orthogonal: `sph A : dev B = 0`. -/
theorem sph_dcontr_dev (A B : Lin E) : sph A ⊡ dev B = 0 := by
  rw [sph_apply, map_smul, LinearMap.smul_apply, one_dcontr, tr_dev, smul_zero]

/-- A tensor is deviatoric iff it is traceless. -/
theorem dev_eq_self_iff {A : Lin E} : dev A = A ↔ tr A = 0 := by
  refine ⟨fun h => h ▸ tr_dev A, fun h => ?_⟩
  rw [dev_apply, sph_apply, h, zero_div, zero_smul, sub_zero]

end Lin

section Examples

open Lin

/-- In `ℝ³`, `sph A = (tr A / 3) I`. -/
example (A : Lin (EuclideanSpace ℝ (Fin 3))) : sph A = (tr A / 3) • (1 : Lin _) := by
  simp [sph_apply]

example [Nontrivial E] (A : Lin E) : A ⊡ A = sph A ⊡ sph A + dev A ⊡ dev A := by
  conv_lhs => rw [← sph_add_dev A]
  simp only [map_add, LinearMap.add_apply, sph_dcontr_dev, dcontr_comm (dev A) (sph A)]
  ring

end Examples

end ContinuumMechanics
