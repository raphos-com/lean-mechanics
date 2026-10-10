import Mathlib.Analysis.SpecialFunctions.Sqrt
import ContinuumMechanics.Tensor.Spectral
import ContinuumMechanics.Tensor.Spherical

/-!
# Stress invariants and yield criteria

For a symmetric (Cauchy) stress `σ`:

* the **principal stresses** are its eigenvalues;
* `J₂ = ½ dev σ : dev σ` is the second invariant of the stress deviator;
* the **von Mises equivalent stress** is `σ_vM = √(3 J₂)`;
* the **Tresca equivalent stress** is `σ_T = σ_max - σ_min` (twice the maximal shear stress).

([Gurtin1981], §§21, 29; standard plasticity texts.) In three dimensions
`J₂ = ⅙ [(σ₁ - σ₂)² + (σ₂ - σ₃)² + (σ₃ - σ₁)²]`, and the two criteria are comparable:
`(√3 / 2) σ_T ≤ σ_vM ≤ σ_T`.

## Main results

* `Lin.J₂_eq`: `J₂ = ½ (σ : σ - (tr σ)² / d)`.
* `Lin.J₂_eq_principal`: the principal-stress formula in dimension three.
* `Lin.vonMises_le_tresca`, `Lin.tresca_mul_le_vonMises`: the comparison.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The second invariant of the stress deviator, `J₂ = ½ dev σ : dev σ`. -/
noncomputable def J₂ (σ : Lin E) : ℝ := 2⁻¹ * (dev σ ⊡ dev σ)

/-- The **von Mises equivalent stress** `σ_vM = √(3 J₂)`. -/
noncomputable def vonMises (σ : Lin E) : ℝ := √(3 * J₂ σ)

theorem J₂_nonneg (σ : Lin E) : 0 ≤ J₂ σ := mul_nonneg (by norm_num) (dcontr_self_nonneg _)

/-- `J₂ = ½ (σ : σ - (tr σ)² / d)`. -/
theorem J₂_eq [Nontrivial E] (σ : Lin E) :
    J₂ σ = 2⁻¹ * (σ ⊡ σ - tr σ ^ 2 / finrank ℝ E) := by
  have hd : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hsph : sph σ ⊡ sph σ = tr σ ^ 2 / finrank ℝ E := by
    rw [sph_apply]
    simp only [map_smul, LinearMap.smul_apply, dcontr_one, tr_one, smul_eq_mul]
    field_simp
  have : σ ⊡ σ = sph σ ⊡ sph σ + dev σ ⊡ dev σ := by
    conv_lhs => rw [← sph_add_dev σ]
    simp only [map_add, LinearMap.add_apply, sph_dcontr_dev, dcontr_comm (dev σ) (sph σ)]
    ring
  rw [J₂, this, hsph]
  ring

section Dim3

variable (hn : finrank ℝ E = 3) {σ : Lin E} (hσ : σ ∈ Sym E)
include hn hσ

/-- The **principal stresses** `σ₁ ≥ σ₂ ≥ σ₃` of a symmetric stress in dimension three. -/
noncomputable def principal : Fin 3 → ℝ := (isSymmetric_of_mem_sym hσ).eigenvalues hn

/-- The corresponding orthonormal principal directions. -/
noncomputable def principalBasis : OrthonormalBasis (Fin 3) ℝ E :=
  (isSymmetric_of_mem_sym hσ).eigenvectorBasis hn

theorem principal_antitone : Antitone (principal hn hσ) :=
  (isSymmetric_of_mem_sym hσ).eigenvalues_antitone hn

theorem apply_principalBasis (i : Fin 3) :
    σ (principalBasis hn hσ i) = principal hn hσ i • principalBasis hn hσ i := by
  have := (isSymmetric_of_mem_sym hσ).apply_eigenvectorBasis hn i
  simp only [RCLike.ofReal_real_eq_id, id] at this
  exact this

theorem tr_eq_principal : tr σ = principal hn hσ 0 + principal hn hσ 1 + principal hn hσ 2 := by
  rw [tr_eq_sum_inner (principalBasis hn hσ), Fin.sum_univ_three]
  simp only [apply_principalBasis, inner_smul_right, real_inner_self_eq_norm_sq,
    (principalBasis hn hσ).orthonormal.1, one_pow, mul_one]

theorem dcontr_self_eq_principal :
    σ ⊡ σ = principal hn hσ 0 ^ 2 + principal hn hσ 1 ^ 2 + principal hn hσ 2 ^ 2 := by
  rw [dcontr_self_eq_sum (principalBasis hn hσ), Fin.sum_univ_three]
  simp only [apply_principalBasis, norm_smul, (principalBasis hn hσ).orthonormal.1, mul_one,
    Real.norm_eq_abs, sq_abs]

/-- `J₂ = ⅙ [(σ₁ - σ₂)² + (σ₂ - σ₃)² + (σ₃ - σ₁)²]`. -/
theorem J₂_eq_principal :
    J₂ σ = ((principal hn hσ 0 - principal hn hσ 1) ^ 2
      + (principal hn hσ 1 - principal hn hσ 2) ^ 2
      + (principal hn hσ 2 - principal hn hσ 0) ^ 2) / 6 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hn
  rw [J₂_eq, dcontr_self_eq_principal hn hσ, tr_eq_principal hn hσ, hn]
  push_cast
  ring

/-- The **Tresca equivalent stress** `σ_T = σ_max - σ_min`. -/
noncomputable def tresca : ℝ := principal hn hσ 0 - principal hn hσ 2

/-- `σ_vM ≤ σ_T`: the von Mises equivalent stress never exceeds the Tresca one. -/
theorem vonMises_le_tresca : vonMises σ ≤ tresca hn hσ := by
  have h01 := principal_antitone hn hσ (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := principal_antitone hn hσ (show (1 : Fin 3) ≤ 2 by decide)
  rw [vonMises, J₂_eq_principal hn hσ, tresca, Real.sqrt_le_left (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h01) (sub_nonneg.mpr h12)]

/-- `(√3 / 2) σ_T ≤ σ_vM`. -/
theorem tresca_mul_le_vonMises : √3 / 2 * tresca hn hσ ≤ vonMises σ := by
  have h01 := principal_antitone hn hσ (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := principal_antitone hn hσ (show (1 : Fin 3) ≤ 2 by decide)
  rw [vonMises, J₂_eq_principal hn hσ, tresca]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [sq_nonneg ((principal hn hσ 0 - principal hn hσ 1) -
    (principal hn hσ 1 - principal hn hσ 2))]

end Dim3

end Lin

end ContinuumMechanics
