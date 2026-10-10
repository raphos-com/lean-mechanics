import ContinuumMechanics.Tensor.SymSkew

/-!
# Double contraction and the Frobenius inner product

The **double contraction** (scalar product of tensors) is `A : B = tr (Aᵀ B)`
([Gurtin1981], §1.2), written `A ⊡ B` here since `:` is reserved in Lean.

`Lin E` already carries Mathlib's *operator* norm, so the Frobenius inner product cannot be an
instance on `Lin E` itself without creating a second, incompatible norm. We therefore provide

* `Lin.dcontr`, the double contraction as a bilinear map, with its algebraic API; and
* `Frob E`, a type synonym of `Lin E` carrying the Frobenius `InnerProductSpace ℝ` structure,
  for use where a Hilbert-space structure on tensors is needed.

## Main results

* `Lin.dcontr_eq_sum`: `A : B = ∑ᵢ A eᵢ · B eᵢ` in any orthonormal basis.
* `Lin.dcontr_comm`, `Lin.dcontr_self_nonneg`, `Lin.dcontr_self_eq_zero`: `:` is an inner product.
* `Lin.dcontr_sym_skw`: symmetric and skew tensors are orthogonal.
* `Lin.one_dcontr`: `I : A = tr A`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **double contraction** `A : B = tr (Aᵀ B)`, as a bilinear map. [Gurtin1981], §1.2. -/
noncomputable def dcontr : Lin E →ₗ[ℝ] Lin E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B => tr (Aᵀ * B))
    (fun A₁ A₂ B => by rw [transpose_add, add_mul, map_add])
    (fun c A B => by rw [transpose_smul, smul_mul_assoc, map_smul, smul_eq_mul])
    (fun A B₁ B₂ => by rw [mul_add, map_add])
    (fun c A B => by rw [mul_smul_comm, map_smul, smul_eq_mul])

@[inherit_doc] scoped[ContinuumMechanics] infixl:70 " ⊡ " => Lin.dcontr

theorem dcontr_apply (A B : Lin E) : A ⊡ B = tr (Aᵀ * B) := rfl

/-- `A : B = ∑ᵢ A eᵢ · B eᵢ` for any orthonormal basis `(eᵢ)`. -/
theorem dcontr_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A B : Lin E) :
    A ⊡ B = ∑ i, ⟪A (b i), B (b i)⟫_ℝ := by
  rw [dcontr_apply, tr_eq_sum_inner b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Aᵀ * B) (b i) = Aᵀ (B (b i)) from rfl, inner_transpose_right]

/-- Symmetry of the double contraction. -/
theorem dcontr_comm (A B : Lin E) : A ⊡ B = B ⊡ A := by
  let b := stdOrthonormalBasis ℝ E
  rw [dcontr_eq_sum b, dcontr_eq_sum b]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem dcontr_self_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A : Lin E) :
    A ⊡ A = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [dcontr_eq_sum b]
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

theorem dcontr_self_nonneg (A : Lin E) : 0 ≤ A ⊡ A := by
  rw [dcontr_self_eq_sum (stdOrthonormalBasis ℝ E)]
  positivity

@[simp]
theorem dcontr_self_eq_zero {A : Lin E} : A ⊡ A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  let b := stdOrthonormalBasis ℝ E
  rw [dcontr_self_eq_sum b, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => ?_)
  simpa using h i (Finset.mem_univ i)

theorem dcontr_self_pos {A : Lin E} (hA : A ≠ 0) : 0 < A ⊡ A :=
  (dcontr_self_nonneg A).lt_of_ne' (dcontr_self_eq_zero.not.mpr hA)

/-- `I : A = tr A`. [Gurtin1981], §1.2. -/
@[simp]
theorem one_dcontr (A : Lin E) : (1 : Lin E) ⊡ A = tr A := by
  rw [dcontr_apply, transpose_one, one_mul]

@[simp]
theorem dcontr_one (A : Lin E) : A ⊡ (1 : Lin E) = tr A := by
  rw [dcontr_comm, one_dcontr]

/-- `Aᵀ : Bᵀ = A : B`. -/
@[simp]
theorem transpose_dcontr_transpose (A B : Lin E) : Aᵀ ⊡ Bᵀ = A ⊡ B := by
  rw [dcontr_apply, dcontr_apply, transpose_transpose, ← tr_transpose (Aᵀ * B), transpose_mul,
    transpose_transpose, tr_mul_comm]

/-- `(A B) : C = B : (Aᵀ C)`. [Gurtin1981], §1.2. -/
theorem mul_dcontr_left (A B C : Lin E) : (A * B) ⊡ C = B ⊡ (Aᵀ * C) := by
  rw [dcontr_apply, dcontr_apply, transpose_mul, mul_assoc]

/-- `(A B) : C = A : (C Bᵀ)`. [Gurtin1981], §1.2. -/
theorem mul_dcontr_right (A B C : Lin E) : (A * B) ⊡ C = A ⊡ (C * Bᵀ) := by
  rw [dcontr_apply, dcontr_apply, transpose_mul, mul_assoc, tr_mul_comm, mul_assoc]

/-- Symmetric and skew tensors are orthogonal: `S : W = 0`. [Gurtin1981], §1.2. -/
theorem dcontr_sym_skw {S W : Lin E} (hS : S ∈ Sym E) (hW : W ∈ Skw E) : S ⊡ W = 0 := by
  have h : S ⊡ W = -(S ⊡ W) := by
    calc S ⊡ W = Sᵀ ⊡ Wᵀ := (transpose_dcontr_transpose S W).symm
      _ = -(S ⊡ W) := by rw [mem_skw_iff.mp hW, mem_sym_iff.mp hS, map_neg]
  linarith

/-- For symmetric `S`, `S : A = S : sym A`. [Gurtin1981], §1.2. -/
theorem dcontr_sym_of_mem_sym {S : Lin E} (hS : S ∈ Sym E) (A : Lin E) :
    S ⊡ A = S ⊡ sym A := by
  conv_lhs => rw [← sym_add_skw A]
  rw [map_add, dcontr_sym_skw hS (skw_mem A), add_zero]

/-- For skew `W`, `W : A = W : skw A`. -/
theorem dcontr_skw_of_mem_skw {W : Lin E} (hW : W ∈ Skw E) (A : Lin E) :
    W ⊡ A = W ⊡ skw A := by
  conv_lhs => rw [← sym_add_skw A]
  rw [map_add, dcontr_comm W (sym A), dcontr_sym_skw (sym_mem A) hW, zero_add]

/-- `A : (a ⊗ b) = a · A b`. [Gurtin1981], §1.2. -/
theorem dcontr_dyad (A : Lin E) (a b : E) : A ⊡ (a ⊗ b) = ⟪a, A b⟫_ℝ := by
  rw [dcontr_apply, mul_dyad, tr_dyad, inner_transpose_left]

/-- `(a ⊗ b) : (c ⊗ d) = (a · c)(b · d)`. [Gurtin1981], §1.2. -/
theorem dyad_dcontr_dyad (a b c d : E) : (a ⊗ b) ⊡ (c ⊗ d) = ⟪a, c⟫_ℝ * ⟪b, d⟫_ℝ := by
  rw [dcontr_dyad, dyad_apply, inner_smul_right, mul_comm, real_inner_comm a c]

end Lin

/-! ### The Frobenius inner product space -/

/-- `Frob E` is `Lin E` equipped with the **Frobenius inner product** `⟪A, B⟫ = A : B` (and the
induced Frobenius norm) instead of the operator norm. It is a type synonym: use `Frob.ofLin` and
`Frob.toLin` to move between the two. -/
def Frob (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := Lin E

namespace Frob

instance : AddCommGroup (Frob E) := inferInstanceAs (AddCommGroup (Lin E))

instance : Module ℝ (Frob E) := inferInstanceAs (Module ℝ (Lin E))

/-- The identity map `Lin E → Frob E`, as a linear equivalence. -/
def ofLin : Lin E ≃ₗ[ℝ] Frob E := LinearEquiv.refl ℝ (Lin E)

/-- The identity map `Frob E → Lin E`, as a linear equivalence. -/
def toLin : Frob E ≃ₗ[ℝ] Lin E := LinearEquiv.refl ℝ (Lin E)

/-- The Frobenius inner product core: `⟪A, B⟫ = A : B`. -/
noncomputable instance innerProductSpaceCore : InnerProductSpace.Core ℝ (Frob E) where
  inner A B := Lin.dcontr (toLin A) (toLin B)
  conj_inner_symm A B := by simp [Lin.dcontr_comm (toLin A)]
  re_inner_nonneg A := by simpa using Lin.dcontr_self_nonneg (toLin A)
  add_left A B C := by simp
  smul_left A B r := by simp
  definite A h := Lin.dcontr_self_eq_zero.mp h

noncomputable instance : NormedAddCommGroup (Frob E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (Frob E) :=
  InnerProductSpace.ofCore (innerProductSpaceCore (E := E)).toCore

theorem inner_def (A B : Frob E) : ⟪A, B⟫_ℝ = toLin A ⊡ toLin B := rfl

theorem norm_sq_eq (A : Frob E) : ‖A‖ ^ 2 = toLin A ⊡ toLin A := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

end Frob

section Examples

example (A : Lin E) : A ⊡ A = 0 → A = 0 := Lin.dcontr_self_eq_zero.mp

example (S W : Lin E) (hS : S ∈ Sym E) (hW : W ∈ Skw E) : (S + W) ⊡ (S + W) = S ⊡ S + W ⊡ W := by
  simp only [map_add, LinearMap.add_apply, Lin.dcontr_sym_skw hS hW, Lin.dcontr_comm W S]
  ring

end Examples

end ContinuumMechanics
