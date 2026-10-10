import Mathlib.Algebra.Star.Module
import ContinuumMechanics.Tensor.Second

/-!
# Symmetric and skew tensors

`Sym E` and `Skw E` are the symmetric (`Aᵀ = A`) and skew (`Aᵀ = -A`) tensors, i.e.
Mathlib's `selfAdjoint.submodule` and `skewAdjoint.submodule` of `Lin E`. The symmetric and skew
parts `sym A = ½(A + Aᵀ)`, `skw A = ½(A - Aᵀ)` are Mathlib's `selfAdjointPart` and
`skewAdjointPart`, composed with the inclusion into `Lin E`.

## Main results

* `Lin.sym_add_skw`: `A = sym A + skw A`.
* `Lin.isCompl_sym_skw`: `Lin E = Sym E ⊕ Skw E` (as complementary submodules).
* `Lin.eq_sym_and_eq_skw_of_add`: uniqueness of the decomposition.
* `Lin.tr_eq_zero_of_mem_skw`: skew tensors are traceless.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `Sym E`, the **symmetric tensors** `Aᵀ = A`, as a submodule of `Lin E`.
This is Mathlib's `selfAdjoint.submodule`. [Gurtin1981], §1.2. -/
noncomputable abbrev Sym : Submodule ℝ (Lin E) := selfAdjoint.submodule ℝ (Lin E)

/-- `Skw E`, the **skew tensors** `Aᵀ = -A`, as a submodule of `Lin E`.
This is Mathlib's `skewAdjoint.submodule`. [Gurtin1981], §1.2. -/
noncomputable abbrev Skw : Submodule ℝ (Lin E) := skewAdjoint.submodule ℝ (Lin E)

variable {E}

namespace Lin

theorem mem_sym_iff {A : Lin E} : A ∈ Sym E ↔ Aᵀ = A := selfAdjoint.mem_iff

theorem mem_skw_iff {A : Lin E} : A ∈ Skw E ↔ Aᵀ = -A := skewAdjoint.mem_iff

/-- The **symmetric part** `sym A = ½(A + Aᵀ)`, as a linear map `Lin E → Lin E`.
[Gurtin1981], §1.2. -/
noncomputable def sym : Lin E →ₗ[ℝ] Lin E where
  toFun A := (selfAdjointPart ℝ A : Lin E)
  map_add' A B := by rw [map_add]; rfl
  map_smul' c A := by rw [map_smul]; rfl

/-- The **skew part** `skw A = ½(A - Aᵀ)`, as a linear map `Lin E → Lin E`.
[Gurtin1981], §1.2. -/
noncomputable def skw : Lin E →ₗ[ℝ] Lin E where
  toFun A := (skewAdjointPart ℝ A : Lin E)
  map_add' A B := by rw [map_add]; rfl
  map_smul' c A := by rw [map_smul]; rfl

theorem sym_apply (A : Lin E) : sym A = (2⁻¹ : ℝ) • (A + Aᵀ) := by
  change (selfAdjointPart ℝ A : Lin E) = _
  rw [selfAdjointPart_apply_coe, invOf_eq_inv]

theorem skw_apply (A : Lin E) : skw A = (2⁻¹ : ℝ) • (A - Aᵀ) := by
  change (skewAdjointPart ℝ A : Lin E) = _
  rw [skewAdjointPart_apply_coe, invOf_eq_inv]

theorem sym_mem (A : Lin E) : sym A ∈ Sym E := (selfAdjointPart ℝ A).2

theorem skw_mem (A : Lin E) : skw A ∈ Skw E := (skewAdjointPart ℝ A).2

@[simp]
theorem transpose_sym (A : Lin E) : (sym A)ᵀ = sym A := mem_sym_iff.mp (sym_mem A)

@[simp]
theorem transpose_skw (A : Lin E) : (skw A)ᵀ = -skw A := mem_skw_iff.mp (skw_mem A)

/-- **Additive decomposition** `A = sym A + skw A`. [Gurtin1981], §1.2. -/
@[simp]
theorem sym_add_skw (A : Lin E) : sym A + skw A = A :=
  StarModule.selfAdjointPart_add_skewAdjointPart ℝ A

theorem sym_eq_self_of_mem {A : Lin E} (hA : A ∈ Sym E) : sym A = A :=
  IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hA

theorem skw_eq_zero_of_mem_sym {A : Lin E} (hA : A ∈ Sym E) : skw A = 0 := by
  rw [skw_apply, mem_sym_iff.mp hA, sub_self, smul_zero]

theorem skw_eq_self_of_mem {A : Lin E} (hA : A ∈ Skw E) : skw A = A := by
  rw [skw_apply, mem_skw_iff.mp hA, sub_neg_eq_add, ← two_smul ℝ A, smul_smul]
  norm_num

theorem sym_eq_zero_of_mem_skw {A : Lin E} (hA : A ∈ Skw E) : sym A = 0 := by
  rw [sym_apply, mem_skw_iff.mp hA, add_neg_cancel, smul_zero]

theorem sym_eq_self_iff {A : Lin E} : sym A = A ↔ A ∈ Sym E :=
  ⟨fun h => h ▸ sym_mem A, sym_eq_self_of_mem⟩

theorem skw_eq_self_iff {A : Lin E} : skw A = A ↔ A ∈ Skw E :=
  ⟨fun h => h ▸ skw_mem A, skw_eq_self_of_mem⟩

@[simp] theorem sym_sym (A : Lin E) : sym (sym A) = sym A := sym_eq_self_of_mem (sym_mem A)

@[simp] theorem skw_skw (A : Lin E) : skw (skw A) = skw A := skw_eq_self_of_mem (skw_mem A)

@[simp] theorem sym_skw (A : Lin E) : sym (skw A) = 0 := sym_eq_zero_of_mem_skw (skw_mem A)

@[simp] theorem skw_sym (A : Lin E) : skw (sym A) = 0 := skw_eq_zero_of_mem_sym (sym_mem A)

@[simp] theorem sym_transpose (A : Lin E) : sym Aᵀ = sym A := by
  rw [sym_apply, sym_apply, transpose_transpose, add_comm]

@[simp] theorem skw_transpose (A : Lin E) : skw Aᵀ = -skw A := by
  rw [skw_apply, skw_apply, transpose_transpose, ← smul_neg, neg_sub]

/-- A tensor that is both symmetric and skew is zero. -/
theorem eq_zero_of_mem_sym_of_mem_skw {A : Lin E} (h₁ : A ∈ Sym E) (h₂ : A ∈ Skw E) : A = 0 := by
  rw [← sym_eq_self_of_mem h₁, sym_eq_zero_of_mem_skw h₂]

/-- `Lin E = Sym E ⊕ Skw E`: the symmetric and skew tensors are complementary submodules.
[Gurtin1981], §1.2. -/
theorem isCompl_sym_skw : IsCompl (Sym E) (Skw E) := by
  refine ⟨Submodule.disjoint_def.mpr fun A h₁ h₂ => eq_zero_of_mem_sym_of_mem_skw h₁ h₂, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro A _
  rw [← sym_add_skw A]
  exact Submodule.add_mem_sup (sym_mem A) (skw_mem A)

/-- **Uniqueness of the additive decomposition**: if `A = S + W` with `S` symmetric and `W` skew,
then `S = sym A` and `W = skw A`. [Gurtin1981], §1.2. -/
theorem eq_sym_and_eq_skw_of_add {A S W : Lin E} (hS : S ∈ Sym E) (hW : W ∈ Skw E)
    (h : A = S + W) : S = sym A ∧ W = skw A := by
  subst h
  simp [map_add, sym_eq_self_of_mem hS, sym_eq_zero_of_mem_skw hW, skw_eq_zero_of_mem_sym hS,
    skw_eq_self_of_mem hW]

/-- For a skew `W`, `v · W v = 0`. [Gurtin1981], §1.2. -/
theorem inner_self_apply_eq_zero_of_mem_skw {W : Lin E} (hW : W ∈ Skw E) (v : E) :
    ⟪v, W v⟫_ℝ = 0 := by
  have h : ⟪v, W v⟫_ℝ = -⟪v, W v⟫_ℝ := by
    calc ⟪v, W v⟫_ℝ = ⟪Wᵀ v, v⟫_ℝ := (inner_transpose_left W v v).symm
      _ = -⟪v, W v⟫_ℝ := by rw [mem_skw_iff.mp hW]; simp [real_inner_comm]
  linarith

section Trace

variable [FiniteDimensional ℝ E]

/-- Skew tensors are traceless. -/
theorem tr_eq_zero_of_mem_skw {W : Lin E} (hW : W ∈ Skw E) : tr W = 0 := by
  have h := tr_transpose W
  rw [mem_skw_iff.mp hW, map_neg] at h
  linarith

@[simp] theorem tr_skw (A : Lin E) : tr (skw A) = 0 := tr_eq_zero_of_mem_skw (skw_mem A)

@[simp] theorem tr_sym (A : Lin E) : tr (sym A) = tr A := by
  have h := congrArg tr (sym_add_skw A)
  rwa [map_add, tr_skw, add_zero] at h

end Trace

end Lin

/-- `sym (a ⊗ b) = ½ (a ⊗ b + b ⊗ a)`. -/
theorem sym_dyad (a b : E) : Lin.sym (a ⊗ b) = (2⁻¹ : ℝ) • (a ⊗ b + b ⊗ a) := by
  rw [Lin.sym_apply, dyad_transpose]

section Examples

example (a : E) : a ⊗ a ∈ Sym E := Lin.mem_sym_iff.mpr (dyad_transpose a a)

example (A : Lin E) : A - Aᵀ ∈ Skw E := by
  rw [Lin.mem_skw_iff, star_sub, Lin.transpose_transpose, neg_sub]

end Examples

end ContinuumMechanics
