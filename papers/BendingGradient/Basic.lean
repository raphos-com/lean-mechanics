import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

/-!
# The Bending-Gradient plate theory: generalized shear force and the Reissner–Mindlin projection

In the Bending-Gradient theory of [LebeeSab2011] the shear force `Q` of Reissner–Mindlin is
replaced by the **generalized shear force** `R = M ⊗ ∇` (`R_αβγ = M_αβ,γ`), a third-order tensor
symmetric in its first two indices, with six independent components. The shear force is recovered
as `Q = i ∴ R` (`Q_α = R_αββ`), where `i` is the identity on symmetric second-order tensors; the
statically compatible fields are `M ⊗ ∇ - R = 0`, `(i ∴ R) · ∇ + p₃ = 0` ((47)). The constitutive
law is `Γ = f ∴ R` with a generalized shear compliance `f` (sixth-order tensor).

Third-order tensors are indexed by `Fin 2 × Fin 2 × Fin 2` with the full inner product
`R ∴ R' = Σ R_αβγ R'_αβγ`. The map `Q ↦ i · Q`, `(i · Q)_αβγ = (δ_αγ Q_β + δ_βγ Q_α)/2`, is the
matrix `embed` (`8 × 2`); its transpose `embedᵀ` is `R ↦ i ∴ R`. We prove:

* `embedᵀ` computes the shear force: `(i ∴ R)_α = Σ_β R_αββ` for `R` symmetric in its first two
  indices (`shear_eq`), so `Q₁ = R₁₁₁ + R₁₂₂`, `Q₂ = R₁₂₁ + R₂₂₂`, and the components `R₁₁₂`,
  `R₂₂₁` are **self-equilibrated** (`shear_selfEquilibrated`);
* `embedᵀ · embed = (3/2) I` (`embed_transpose_mul`), the identity behind the factor `2/3`;
* **homogeneous plate** ((55)–(56)): with `f = (6/5h) i · S · i`, the Bending-Gradient shear
  energy `½ R ∴ f ∴ R` equals the Reissner–Mindlin energy `½ Q · (6/5h) S · Q`, `Q = i ∴ R`
  (`homogeneous_energy`): the two models coincide, with Reissner's shear factor `5/6`;
* **Reissner–Mindlin projection** ((64)–(67)): `f_RM = i · ((2/3) i ∴ f ∴ (2/3) i) · i` is the
  orthogonal projection of `f` onto the compliances of Reissner–Mindlin form `i · g · i`, for the
  inner product `f ::: g = tr(fᵀ g)` (`rmProj_orthogonal`); it leaves Reissner–Mindlin compliances
  unchanged (`rmProj_rm`), in particular the homogeneous one.

## References

* [LebeeSab2011] A. Lebée, K. Sab, *A Bending-Gradient model for thick plates. Part I: Theory*,
  Int. J. Solids Struct. 48(20), 2878–2888 (2011).
-/

open Matrix

noncomputable section

namespace ContinuumMechanics.BendingGradient

/-- Index of third-order 2D tensors. -/
abbrev I3 := Fin 2 × Fin 2 × Fin 2

/-- The matrix of `Q ↦ i · Q`: `(i · Q)_αβγ = (δ_αγ Q_β + δ_βγ Q_α) / 2`. -/
def embed : Matrix I3 (Fin 2) ℝ := fun p δ =>
  ((if p.1 = p.2.2 ∧ p.2.1 = δ then 1 else 0) + (if p.2.1 = p.2.2 ∧ p.1 = δ then 1 else 0)) / 2

/-- Third-order tensors symmetric in their first two indices (the space `R²³`). -/
def IsSym (R : I3 → ℝ) : Prop := ∀ a b c, R (a, b, c) = R (b, a, c)

/-- **Shear force from the generalized shear force**: `(i ∴ R)_α = Σ_β R_αββ`. -/
theorem shear_eq {R : I3 → ℝ} (hR : IsSym R) (α : Fin 2) :
    (embedᵀ *ᵥ R) α = ∑ β, R (α, β, β) := by
  simp only [mulVec, dotProduct, transpose_apply, embed, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases α <;> simp [hR 1 0 0, hR 1 0 1] <;> ring

/-- `Q₁ = R₁₁₁ + R₁₂₂`, `Q₂ = R₁₂₁ + R₂₂₂`. -/
theorem shear_components {R : I3 → ℝ} (hR : IsSym R) :
    (embedᵀ *ᵥ R) 0 = R (0, 0, 0) + R (0, 1, 1) ∧
      (embedᵀ *ᵥ R) 1 = R (0, 1, 0) + R (1, 1, 1) := by
  refine ⟨?_, ?_⟩ <;> rw [shear_eq hR] <;> simp [Fin.sum_univ_two, hR 1 0 0]

/-- The components `R₁₁₂` and `R₂₂₁` (and their symmetric partners) are **self-equilibrated**:
they carry no shear force. -/
theorem shear_selfEquilibrated (x y : ℝ) :
    embedᵀ *ᵥ (fun p : I3 => if p = (0, 0, 1) then x else if p = (1, 1, 0) then y else 0) = 0 := by
  funext α
  simp only [mulVec, dotProduct, transpose_apply, embed, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases α <;> simp

/-- `(i·)ᵀ (i·) = (3/2) I`. -/
theorem embed_transpose_mul : embedᵀ * embed = (3 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  simp only [mul_apply, transpose_apply, embed, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, and_self, ↓reduceIte, add_self_div_two,
      mul_one, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, and_true, and_false,
      add_zero, zero_add, zero_div, mul_zero, zero_mul, one_div, Matrix.smul_apply, one_apply_eq,
      one_apply_ne, ne_eq, not_false_eq_true, smul_eq_mul, Nat.reduceAdd] <;> norm_num

/-! ### Homogeneous plates -/

/-- **Homogeneous plate** ((55)–(56)): with `f = (6/5h) i · S · i`, the Bending-Gradient shear
stress energy is the Reissner–Mindlin one, `½ Q · (6/5h) S · Q`, `Q = i ∴ R`. -/
theorem homogeneous_energy (h : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (R : I3 → ℝ) :
    R ⬝ᵥ (((6 / (5 * h)) • (embed * S * embedᵀ)) *ᵥ R) / 2 =
      (embedᵀ *ᵥ R) ⬝ᵥ (((6 / (5 * h)) • S) *ᵥ (embedᵀ *ᵥ R)) / 2 := by
  congr 1
  rw [smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul, ← mulVec_mulVec,
    ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-! ### Projection on Reissner–Mindlin compliances -/

/-- The inner product `f ::: g = Σ f_ij g_ij = tr(fᵀ g)` ((62)). -/
def inner (f g : Matrix I3 I3 ℝ) : ℝ := (fᵀ * g).trace

/-- The Reissner–Mindlin part `f_RM = (2/3) i ∴ f ∴ (2/3) i` ((66)). -/
def rmPart (f : Matrix I3 I3 ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (4 / 9 : ℝ) • (embedᵀ * f * embed)

/-- The projection `i · f_RM · i` ((67)). -/
def rmProj (f : Matrix I3 I3 ℝ) : Matrix I3 I3 ℝ := embed * rmPart f * embedᵀ

/-- `tr(i · K · i ∴ i · g · i) = tr(K (iᵀi) g (iᵀi))`. -/
theorem trace_sandwich (K g : Matrix (Fin 2) (Fin 2) ℝ) :
    (embed * K * embedᵀ * (embed * g * embedᵀ)).trace =
      (K * (embedᵀ * embed) * g * (embedᵀ * embed)).trace := by
  rw [show embed * K * embedᵀ * (embed * g * embedᵀ) =
      embed * (K * (embedᵀ * embed) * g * embedᵀ) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **`rmProj f` is the orthogonal projection of `f` onto the Reissner–Mindlin compliances**
`i · g · i` ((64)). -/
theorem rmProj_orthogonal (f : Matrix I3 I3 ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    inner (f - rmProj f) (embed * g * embedᵀ) = 0 := by
  have e1 : (fᵀ * (embed * g * embedᵀ)).trace = (embedᵀ * fᵀ * embed * g).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hP : (rmProj f)ᵀ = embed * ((4 / 9 : ℝ) • (embedᵀ * fᵀ * embed)) * embedᵀ := by
    simp only [rmProj, rmPart, transpose_mul, transpose_transpose, transpose_smul,
      Matrix.mul_assoc]
  rw [inner, transpose_sub, Matrix.sub_mul, trace_sub, e1, hP, trace_sandwich,
    embed_transpose_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, smul_smul]
  ring

/-- Reissner–Mindlin compliances are left unchanged by the projection. -/
theorem rmProj_rm (g : Matrix (Fin 2) (Fin 2) ℝ) :
    rmProj (embed * g * embedᵀ) = embed * g * embedᵀ := by
  have : rmPart (embed * g * embedᵀ) = g := by
    rw [rmPart, show embedᵀ * (embed * g * embedᵀ) * embed =
      (embedᵀ * embed) * g * (embedᵀ * embed) by simp only [Matrix.mul_assoc],
      embed_transpose_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    norm_num
  rw [rmProj, this]

/-- In particular the homogeneous compliance `(6/5h) i · S · i` is its own Reissner–Mindlin part. -/
theorem rmProj_homogeneous (h : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) :
    rmProj ((6 / (5 * h)) • (embed * S * embedᵀ)) = (6 / (5 * h)) • (embed * S * embedᵀ) := by
  rw [show (6 / (5 * h)) • (embed * S * embedᵀ) = embed * ((6 / (5 * h)) • S) * embedᵀ by
    simp only [Matrix.mul_smul, Matrix.smul_mul], rmProj_rm]

end ContinuumMechanics.BendingGradient
