import Mathlib.Analysis.InnerProductSpace.Spectrum
import ContinuumMechanics.Tensor.Invariants
import ContinuumMechanics.Tensor.Positive

/-!
# Spectral decomposition of symmetric tensors

Every symmetric tensor `S` has an orthonormal basis of eigenvectors `(eᵢ)` with real eigenvalues
`(λᵢ)`, and `S = ∑ᵢ λᵢ eᵢ ⊗ eᵢ` (the **spectral theorem**, [Gurtin1981], §1.3). We use Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis` and `eigenvalues` (sorted in decreasing order).

## Main results

* `Lin.spectral_decomposition`: `S = ∑ᵢ λᵢ eᵢ ⊗ eᵢ`.
* `Lin.tr_eq_sum_eigenvalues`, `Lin.det_eq_prod_eigenvalues`, `Lin.I₂_eq_eigenvalues`:
  the principal invariants in terms of the eigenvalues.
* `Lin.nonneg_iff_eigenvalues_nonneg`: `S ≥ 0` iff all eigenvalues are `≥ 0`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.3.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

variable {S : Lin E}

theorem isSymmetric_of_mem_sym (hS : S ∈ Sym E) : (S : E →ₗ[ℝ] E).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS

/-- The **principal values** (eigenvalues) of a symmetric tensor, in decreasing order.
[Gurtin1981], §1.3. -/
noncomputable def eigenvalues (hS : S ∈ Sym E) : Fin (finrank ℝ E) → ℝ :=
  (isSymmetric_of_mem_sym hS).eigenvalues rfl

/-- An orthonormal basis of **principal directions** (eigenvectors) of a symmetric tensor.
[Gurtin1981], §1.3. -/
noncomputable def eigenbasis (hS : S ∈ Sym E) : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  (isSymmetric_of_mem_sym hS).eigenvectorBasis rfl

@[simp]
theorem apply_eigenbasis (hS : S ∈ Sym E) (i : Fin (finrank ℝ E)) :
    S (eigenbasis hS i) = eigenvalues hS i • eigenbasis hS i := by
  have := (isSymmetric_of_mem_sym hS).apply_eigenvectorBasis rfl i
  simp only [RCLike.ofReal_real_eq_id, id] at this
  exact this

/-- The **spectral theorem**: `S = ∑ᵢ λᵢ eᵢ ⊗ eᵢ`. [Gurtin1981], §1.3. -/
theorem spectral_decomposition (hS : S ∈ Sym E) :
    S = ∑ i, eigenvalues hS i • (eigenbasis hS i ⊗ eigenbasis hS i) := by
  set b := eigenbasis hS
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    sum_apply, smul_apply, dyad_apply,
    orthonormal_iff_ite.mp b.orthonormal, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact apply_eigenbasis hS j

/-- The quadratic form of a symmetric tensor: `S v · v = ∑ᵢ λᵢ (eᵢ · v)²`. -/
theorem inner_apply_self_eq_sum (hS : S ∈ Sym E) (v : E) :
    ⟪S v, v⟫_ℝ = ∑ i, eigenvalues hS i * ⟪eigenbasis hS i, v⟫_ℝ ^ 2 := by
  conv_lhs => rw [spectral_decomposition hS]
  simp only [sum_apply, smul_apply, dyad_apply,
    sum_inner, inner_smul_left, RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `tr S = ∑ᵢ λᵢ`. [Gurtin1981], §1.3. -/
theorem tr_eq_sum_eigenvalues (hS : S ∈ Sym E) : tr S = ∑ i, eigenvalues hS i := by
  rw [tr_eq_sum_inner (eigenbasis hS)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_eigenbasis, inner_smul_right, real_inner_self_eq_norm_sq,
    (eigenbasis hS).orthonormal.1 i]
  ring

/-- `tr S² = ∑ᵢ λᵢ²`. -/
theorem tr_mul_self_eq_sum_eigenvalues (hS : S ∈ Sym E) :
    tr (S * S) = ∑ i, eigenvalues hS i ^ 2 := by
  rw [tr_eq_sum_inner (eigenbasis hS)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, apply_eigenbasis, map_smul,
    apply_eigenbasis, smul_smul, inner_smul_right, real_inner_self_eq_norm_sq,
    (eigenbasis hS).orthonormal.1 i]
  ring

/-- `det S = ∏ᵢ λᵢ`. [Gurtin1981], §1.3. -/
theorem det_eq_prod_eigenvalues (hS : S ∈ Sym E) : S.det = ∏ i, eigenvalues hS i := by
  have := (isSymmetric_of_mem_sym hS).det_eq_prod_eigenvalues rfl
  simpa [eigenvalues] using this

/-- `I₂(S) = ½((∑ λᵢ)² - ∑ λᵢ²)`, i.e. the sum of the pairwise products of the eigenvalues.
[Gurtin1981], §1.3. -/
theorem I₂_eq_eigenvalues (hS : S ∈ Sym E) :
    I₂ S = ((∑ i, eigenvalues hS i) ^ 2 - ∑ i, eigenvalues hS i ^ 2) / 2 := by
  rw [I₂, tr_eq_sum_eigenvalues hS, tr_mul_self_eq_sum_eigenvalues hS]

/-- A symmetric tensor is positive semidefinite iff all its eigenvalues are nonnegative.
[Gurtin1981], §1.3. -/
theorem nonneg_iff_eigenvalues_nonneg (hS : S ∈ Sym E) :
    0 ≤ S ↔ ∀ i, 0 ≤ eigenvalues hS i := by
  rw [nonneg_iff]
  constructor
  · intro h i
    have := h.2 (eigenbasis hS i)
    rwa [apply_eigenbasis, inner_smul_left, real_inner_self_eq_norm_sq,
      (eigenbasis hS).orthonormal.1 i, RCLike.conj_to_real, one_pow, mul_one] at this
  · intro h
    refine ⟨mem_sym_iff.mp hS, fun v => ?_⟩
    rw [inner_apply_self_eq_sum hS]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

end Lin

section Examples

open Lin

/-- The identity has all principal values equal to one. -/
example (h : (1 : Lin E) ∈ Sym E) (i : Fin (finrank ℝ E)) : eigenvalues h i = 1 := by
  have h1 := apply_eigenbasis h i
  rw [one_apply_eq_self] at h1
  have h2 : (eigenvalues h i - 1) • eigenbasis h i = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 ((eigenbasis h).orthonormal.ne_zero i)

end Examples

end ContinuumMechanics
