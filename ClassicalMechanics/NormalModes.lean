import ClassicalMechanics.SmallOscillations

/-!
# Complete sets of normal modes

For `M q̈ + K q = 0` with `M` positive definite and `K` positive semidefinite, there are `n`
normal modes `K φⱼ = ωⱼ² M φⱼ` which are **`M`-orthonormal**, `φᵢ · M φⱼ = δᵢⱼ`
(`SmallOscillations.exists_modes_general`): `M` and `K` are **simultaneously diagonalizable**
([Arnold1989], §23; [Goldstein2002], §6.2).

## Proof

Diagonalize `M`: `M bⱼ = μⱼ bⱼ` with an orthonormal basis `(bⱼ)` and `μⱼ > 0`. The rescaled
vectors `sⱼ = bⱼ / √μⱼ` are `M`-orthonormal (`gram`). In this basis `K` becomes the symmetric
positive semidefinite matrix `Aᵢⱼ = sᵢ · K sⱼ`; its orthonormal eigenvectors `cⱼ`
(`A cⱼ = λⱼ cⱼ`, `λⱼ ≥ 0`) give the modes `φⱼ = Σₖ cⱼₖ sₖ`, with `ωⱼ = √λⱼ`. The mode equation
follows by testing `K φ - λ M φ` against the basis `(sᵢ)` (`eq_zero_of_dot`).

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §23.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §6.2.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

/-- A vector orthogonal to all the eigenvectors of a symmetric matrix vanishes. -/
theorem eq_zero_of_dot_eigenvectors {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {y : Fin n → ℝ} (h : ∀ j, ⇑(hA.eigenvectorBasis j) ⬝ᵥ y = 0) : y = 0 := by
  set U : Matrix (Fin n) (Fin n) ℝ := ↑hA.eigenvectorUnitary
  have h1 : star U *ᵥ y = 0 := by
    ext j
    simpa [U, mulVec, dotProduct, Matrix.star_apply] using h j
  have hU : U * star U = 1 := hA.eigenvectorUnitary.prop.2
  calc y = (U * star U) *ᵥ y := by rw [hU, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h1, mulVec_zero]

/-- The eigenvectors of a symmetric matrix are orthonormal for the dot product. -/
theorem eigenvectors_orthonormal {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i j : Fin n) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = if i = j then 1 else 0 := by
  have h := hA.eigenvectorBasis.inner_eq_ite i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

namespace SmallOscillations

variable (S : SmallOscillations n)

/-- **Simultaneous diagonalization**: for positive semidefinite `K`, there are `n`
`M`-orthonormal normal modes `K φⱼ = ωⱼ² M φⱼ`. -/
theorem exists_modes_general (hK : S.K.PosSemidef) :
    ∃ (φ : Fin n → Fin n → ℝ) (ω : Fin n → ℝ),
      (∀ i j, φ i ⬝ᵥ S.M *ᵥ φ j = if i = j then 1 else 0) ∧ ∀ j, S.IsMode (ω j) (φ j) := by
  have hMh := S.M_posDef.1
  set b := hMh.eigenvectorBasis
  set μ := hMh.eigenvalues
  have hμ : ∀ j, 0 < μ j := S.M_posDef.eigenvalues_pos
  have hsq : ∀ j, √(μ j) ≠ 0 := fun j => (sqrt_pos.mpr (hμ j)).ne'
  -- the `M`-orthonormal basis `sⱼ = bⱼ / √μⱼ`
  set s : Fin n → Fin n → ℝ := fun j => (√(μ j))⁻¹ • ⇑(b j) with hs
  have hMs : ∀ j, S.M *ᵥ s j = √(μ j) • ⇑(b j) := fun j => by
    rw [hs, mulVec_smul, hMh.mulVec_eigenvectorBasis j, smul_smul]
    congr 1
    rw [inv_mul_eq_iff_eq_mul₀ (hsq j)]
    exact (mul_self_sqrt (hμ j).le).symm
  have gram : ∀ i j, s i ⬝ᵥ S.M *ᵥ s j = if i = j then 1 else 0 := fun i j => by
    rw [hMs, hs, smul_dotProduct, dotProduct_smul, eigenvectors_orthonormal]
    split_ifs with h
    · subst h; simp [hsq i]
    · simp
  -- coordinates in the basis `s`
  let Sv : (Fin n → ℝ) → Fin n → ℝ := fun x => ∑ k, x k • s k
  have Sv_dot : ∀ x y, Sv x ⬝ᵥ y = x ⬝ᵥ fun k => s k ⬝ᵥ y := fun x y => by
    simp only [Sv]
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    rfl
  have dot_Sv : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ),
      s i ⬝ᵥ B *ᵥ Sv x = ∑ k, (s i ⬝ᵥ B *ᵥ s k) * x k := fun B i x => by
    simp only [Sv, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- `K` in the basis `s`
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => s i ⬝ᵥ S.K *ᵥ s j with hAdef
  have hA : A.IsHermitian := IsHermitian.ext fun i j => by
    simp [A, dot_mulVec_comm S.K_symm (s j) (s i)]
  have hAv : ∀ x i, (A *ᵥ x) i = s i ⬝ᵥ S.K *ᵥ Sv x := fun x i => by
    rw [dot_Sv]; simp [A, mulVec, dotProduct]
  refine ⟨fun j => Sv ⇑(hA.eigenvectorBasis j), fun j => √(hA.eigenvalues j), fun i j => ?_,
    fun j => ?_⟩
  · -- `M`-orthonormality
    rw [Sv_dot, ← eigenvectors_orthonormal hA i j]
    congr 1
    ext k
    rw [dot_Sv]
    simp only [gram, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · -- the mode equation `K φ = λ M φ`, with `λ ≥ 0`
    have hcj := hA.mulVec_eigenvectorBasis j
    have hmode : S.K *ᵥ Sv ⇑(hA.eigenvectorBasis j) =
        hA.eigenvalues j • S.M *ᵥ Sv ⇑(hA.eigenvectorBasis j) := by
      rw [← sub_eq_zero]
      refine eq_zero_of_dot_eigenvectors hMh fun i => ?_
      have : ⇑(b i) = √(μ i) • s i := by rw [hs, smul_smul, mul_inv_cancel₀ (hsq i), one_smul]
      rw [this, smul_dotProduct, dotProduct_sub, dotProduct_smul, ← hAv, hcj, dot_Sv]
      simp only [gram, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Pi.smul_apply, smul_eq_mul, sub_self, mul_zero]
    have hlam : 0 ≤ hA.eigenvalues j := by
      have h1 : hA.eigenvalues j =
          Sv ⇑(hA.eigenvectorBasis j) ⬝ᵥ S.K *ᵥ Sv ⇑(hA.eigenvectorBasis j) := by
        rw [Sv_dot]
        have : (fun k => s k ⬝ᵥ S.K *ᵥ Sv ⇑(hA.eigenvectorBasis j)) =
            A *ᵥ ⇑(hA.eigenvectorBasis j) := by ext k; rw [hAv]
        rw [this, hcj, dotProduct_smul, eigenvectors_orthonormal hA j j]
        simp only [↓reduceIte, smul_eq_mul, mul_one]
      rw [h1]
      simpa using hK.dotProduct_mulVec_nonneg (Sv ⇑(hA.eigenvectorBasis j))
    change S.K *ᵥ Sv ⇑(hA.eigenvectorBasis j) =
      (√(hA.eigenvalues j)) ^ 2 • S.M *ᵥ Sv ⇑(hA.eigenvectorBasis j)
    rw [sq_sqrt hlam]
    exact hmode

end SmallOscillations

end ClassicalMechanics
