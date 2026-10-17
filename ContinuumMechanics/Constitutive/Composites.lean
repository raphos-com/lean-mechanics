import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Micromechanics and classical lamination theory

Elementary stiffness results for fibre-reinforced composites ([Jones1999], [Reddy2004]).

**Micromechanics.** A unidirectional ply consists of fibres (modulus `E_f`, volume fraction
`V_f`) in a matrix (modulus `E_m`). Loaded along the fibres, both phases share the same strain
(Voigt): the average stress is `σ̄ = E₁ ε` with the rule of mixtures
`E₁ = V_f E_f + (1 - V_f) E_m`. Loaded across the fibres, both phases carry the same stress
(Reuss): the average strain is `ε̄ = σ / E₂` with `1/E₂ = V_f/E_f + (1 - V_f)/E_m`. More
generally, for `n` phases with fractions `cᵢ` and moduli `Eᵢ`, the harmonic (Reuss) mean lies below
the arithmetic (Voigt) mean, and both lie between `min Eᵢ` and `max Eᵢ`.

**Ply stiffness.** In plane stress an orthotropic ply has, in Voigt notation `(σ₁, σ₂, τ₁₂)` vs
`(ε₁, ε₂, γ₁₂)`, the reduced stiffness `Q` with `Q₁₁ = E₁/Δ`, `Q₂₂ = E₂/Δ`,
`Q₁₂ = ν₁₂E₂/Δ = ν₂₁E₁/Δ`, `Q₆₆ = G₁₂`, `Δ = 1 - ν₁₂ν₂₁`. Rotated by `θ`, its stiffness is
`Q̄(θ) = T(θ)⁻¹ Q T(θ)⁻ᵀ` with the stress transformation matrix `T(θ)`.

**Lamination theory.** For plies `k = 1..N` with stiffnesses `Q̄_k` between interfaces
`z_{k-1}, z_k`, the extensional, coupling and bending stiffnesses are
`A = Σ Q̄_k (z_k - z_{k-1})`, `B = ½ Σ Q̄_k (z_k² - z_{k-1}²)`,
`D = ⅓ Σ Q̄_k (z_k³ - z_{k-1}³)`. (The ordering `z_{k-1} < z_k` is physically required but is
not needed by the algebraic statements below.)

## Main results

* `Composites.equal_strain_average`, `Composites.equal_stress_average`: the Voigt and Reuss
  moduli as average stress / average strain under the equal-strain resp. equal-stress
  assumptions.
* `Composites.voigt_sub_reuss`, `Composites.reuss_le_voigt`, `Composites.reuss_eq_voigt_iff`:
  `E₁ - E₂ = V_f(1 - V_f)(E_f - E_m)² / (V_f E_m + (1 - V_f) E_f) ≥ 0`, with equality iff
  `E_f = E_m`, `V_f = 0` or `V_f = 1`.
* `Composites.harmonic_le_arith`, `Composites.le_harmonic`, `Composites.arith_le`,
  `Composites.inf'_le_harmonic`, `Composites.arith_le_sup'`: the `n`-phase Voigt–Reuss bounds
  `min Eᵢ ≤ (Σ cᵢ/Eᵢ)⁻¹ ≤ Σ cᵢ Eᵢ ≤ max Eᵢ`.
* `Composites.Ply.qMat_isSymm`, `Composites.Ply.qMat_mul_sMat`: the reduced stiffness is
  symmetric under reciprocity `ν₂₁/E₂ = ν₁₂/E₁`, and inverts the compliance.
* `Composites.tMat_mul_tInv`, `Composites.qBar_isSymm`: `T(θ) T(θ)⁻¹ = 1`; `Q̄` is symmetric.
* `Composites.qBar_00` … `Composites.qBar_12`: the explicit trigonometric formulas for
  `Q̄₁₁, Q̄₂₂, Q̄₁₂, Q̄₆₆, Q̄₁₆, Q̄₂₆`, and `Composites.qBar_invariant`:
  `Q̄₁₁ + Q̄₂₂ + 2Q̄₁₂ = Q₁₁ + Q₂₂ + 2Q₁₂` for every `θ`.
* `Composites.bMat_eq_zero_of_symmetric`: a midplane-symmetric laminate has `B = 0`.
* `Composites.aMat_isSymm`, `Composites.dMat_isSymm`: `A`, `D` are symmetric.
* `Composites.single_layer_aMat`, `Composites.single_layer_bMat`,
  `Composites.single_layer_dMat`: a single layer of thickness `h` has `A = hQ`, `B = 0`,
  `D = h³Q/12`.

## References

* [Jones1999] R. M. Jones, *Mechanics of Composite Materials*, 2nd ed., §§2.6, 3.2, 4.2.
* [Reddy2004] J. N. Reddy, *Mechanics of Laminated Composite Plates and Shells*, §§2.3, 3.3.
* [Hill1952] R. Hill, *The elastic behaviour of a crystalline aggregate*, Proc. Phys. Soc. A 65,
  349–354 (1952).
-/

open Real Matrix Finset

noncomputable section

namespace ContinuumMechanics.Composites

/-! ### Rule of mixtures for a unidirectional ply -/

/-- The Voigt (rule of mixtures, longitudinal) modulus `E₁ = V_f E_f + (1 - V_f) E_m`. -/
def voigt (Vf Ef Em : ℝ) : ℝ := Vf * Ef + (1 - Vf) * Em

/-- The Reuss (inverse rule of mixtures, transverse) modulus
`E₂ = 1 / (V_f/E_f + (1 - V_f)/E_m)`. -/
def reuss (Vf Ef Em : ℝ) : ℝ := 1 / (Vf / Ef + (1 - Vf) / Em)

/-- **Equal strain (Voigt)**: if fibre and matrix both carry the strain `ε`, with stresses
`σ_f = E_f ε`, `σ_m = E_m ε`, the volume-averaged stress is `E₁ ε`. -/
theorem equal_strain_average (Vf Ef Em ε σf σm : ℝ) (hf : σf = Ef * ε) (hm : σm = Em * ε) :
    Vf * σf + (1 - Vf) * σm = voigt Vf Ef Em * ε := by
  subst hf hm
  unfold voigt
  ring

/-- The Reuss modulus in closed form, `E₂ = E_f E_m / (V_f E_m + (1 - V_f) E_f)`. -/
theorem reuss_eq (Vf Ef Em : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em) :
    reuss Vf Ef Em = Ef * Em / (Vf * Em + (1 - Vf) * Ef) := by
  unfold reuss
  rw [div_add_div _ _ hEf.ne' hEm.ne', one_div_div]
  ring

/-- The mixed compliance denominator `V_f E_m + (1 - V_f) E_f` is positive. -/
theorem mix_pos (Vf Ef Em : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em) (h0 : 0 ≤ Vf) (h1 : Vf ≤ 1) :
    0 < Vf * Em + (1 - Vf) * Ef := by
  rcases le_total Ef Em with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h h0]
  · nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.2 h1)]

/-- **Equal stress (Reuss)**: if fibre and matrix both carry the stress `σ`, with strains
`ε_f = σ / E_f`, `ε_m = σ / E_m`, the stress is `E₂` times the volume-averaged strain. -/
theorem equal_stress_average (Vf Ef Em σ εf εm : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em)
    (h0 : 0 ≤ Vf) (h1 : Vf ≤ 1) (hf : εf = σ / Ef) (hm : εm = σ / Em) :
    σ = reuss Vf Ef Em * (Vf * εf + (1 - Vf) * εm) := by
  subst hf hm
  have hpos := mix_pos Vf Ef Em hEf hEm h0 h1
  rw [reuss_eq Vf Ef Em hEf hEm, div_mul_eq_mul_div, eq_div_iff hpos.ne']
  field_simp

/-- The gap between the Voigt and Reuss moduli:
`E₁ - E₂ = V_f(1 - V_f)(E_f - E_m)² / (V_f E_m + (1 - V_f) E_f)`. -/
theorem voigt_sub_reuss (Vf Ef Em : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em) (h0 : 0 ≤ Vf)
    (h1 : Vf ≤ 1) :
    voigt Vf Ef Em - reuss Vf Ef Em =
      Vf * (1 - Vf) * (Ef - Em) ^ 2 / (Vf * Em + (1 - Vf) * Ef) := by
  have hpos := mix_pos Vf Ef Em hEf hEm h0 h1
  rw [reuss_eq Vf Ef Em hEf hEm, voigt, eq_div_iff hpos.ne', sub_mul,
    div_mul_cancel₀ _ hpos.ne']
  ring

/-- **Reuss ≤ Voigt**: the transverse (equal-stress) modulus never exceeds the longitudinal
(equal-strain) one; the weighted harmonic mean is at most the weighted arithmetic mean. -/
theorem reuss_le_voigt (Vf Ef Em : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em) (h0 : 0 ≤ Vf)
    (h1 : Vf ≤ 1) : reuss Vf Ef Em ≤ voigt Vf Ef Em := by
  have hpos := mix_pos Vf Ef Em hEf hEm h0 h1
  have h := voigt_sub_reuss Vf Ef Em hEf hEm h0 h1
  have : 0 ≤ Vf * (1 - Vf) * (Ef - Em) ^ 2 / (Vf * Em + (1 - Vf) * Ef) := by
    apply div_nonneg _ hpos.le
    have : 0 ≤ 1 - Vf := by linarith
    positivity
  linarith

/-- **Equality case**: `E₂ = E₁` iff `E_f = E_m`, `V_f = 0` or `V_f = 1`. -/
theorem reuss_eq_voigt_iff (Vf Ef Em : ℝ) (hEf : 0 < Ef) (hEm : 0 < Em) (h0 : 0 ≤ Vf)
    (h1 : Vf ≤ 1) : reuss Vf Ef Em = voigt Vf Ef Em ↔ Ef = Em ∨ Vf = 0 ∨ Vf = 1 := by
  have hpos := mix_pos Vf Ef Em hEf hEm h0 h1
  have h := voigt_sub_reuss Vf Ef Em hEf hEm h0 h1
  rw [eq_comm, ← sub_eq_zero, h, div_eq_zero_iff, or_iff_left hpos.ne']
  simp only [mul_eq_zero, pow_eq_zero_iff (two_ne_zero), sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h.symm)

/-! ### Voigt–Reuss bounds for `n` phases -/

section Bounds

variable {ι : Type*} (s : Finset ι) (c E : ι → ℝ)

/-- The Voigt (arithmetic) mean `Σ cᵢ Eᵢ` of the phase moduli. -/
def arith : ℝ := ∑ i ∈ s, c i * E i

/-- The Reuss (harmonic) mean `(Σ cᵢ / Eᵢ)⁻¹` of the phase moduli. -/
def harmonic : ℝ := 1 / ∑ i ∈ s, c i / E i

variable {s c E}

/-- Some phase fraction is positive when the fractions sum to `1`. -/
theorem exists_pos_fraction (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1) :
    ∃ i ∈ s, 0 < c i := by
  by_contra h
  push Not at h
  have : ∑ i ∈ s, c i = 0 := Finset.sum_eq_zero fun i hi => le_antisymm (h i hi) (hc i hi)
  linarith

/-- The Voigt mean of positive moduli is positive. -/
theorem arith_pos (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hE : ∀ i ∈ s, 0 < E i) : 0 < arith s c E := by
  obtain ⟨j, hj, hcj⟩ := exists_pos_fraction hc hsum
  exact Finset.sum_pos' (fun i hi => mul_nonneg (hc i hi) (hE i hi).le)
    ⟨j, hj, mul_pos hcj (hE j hj)⟩

/-- The Reuss compliance `Σ cᵢ / Eᵢ` of positive moduli is positive. -/
theorem compliance_pos (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hE : ∀ i ∈ s, 0 < E i) : 0 < ∑ i ∈ s, c i / E i := by
  obtain ⟨j, hj, hcj⟩ := exists_pos_fraction hc hsum
  exact Finset.sum_pos' (fun i hi => div_nonneg (hc i hi) (hE i hi).le)
    ⟨j, hj, div_pos hcj (hE j hj)⟩

/-- **Reuss ≤ Voigt** for `n` phases: `(Σ cᵢ/Eᵢ)⁻¹ ≤ Σ cᵢ Eᵢ`. The proof uses the energy-like
identity `Σ cᵢ (Eᵢ - Ē)² / Eᵢ = Ē² Σ cᵢ/Eᵢ - Ē ≥ 0` with `Ē = Σ cᵢ Eᵢ`. -/
theorem harmonic_le_arith (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hE : ∀ i ∈ s, 0 < E i) : harmonic s c E ≤ arith s c E := by
  set A := arith s c E with hA
  set S := ∑ i ∈ s, c i / E i with hS
  have hApos : 0 < A := arith_pos hc hsum hE
  have hSpos : 0 < S := compliance_pos hc hsum hE
  have key : ∑ i ∈ s, c i * (E i - A) ^ 2 / E i =
      ∑ i ∈ s, (c i * E i - 2 * A * c i + A ^ 2 * (c i / E i)) :=
    Finset.sum_congr rfl fun i hi => by
      have := (hE i hi).ne'
      field_simp
      ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum, ← hS] at key
  have hnn : 0 ≤ ∑ i ∈ s, c i * (E i - A) ^ 2 / E i :=
    Finset.sum_nonneg fun i hi => div_nonneg (mul_nonneg (hc i hi) (sq_nonneg _)) (hE i hi).le
  rw [key] at hnn
  change 0 ≤ A - 2 * A * 1 + A ^ 2 * S at hnn
  have h1 : 1 ≤ A * S := by nlinarith
  unfold harmonic
  rw [← hS, div_le_iff₀ hSpos]
  exact h1

/-- **Upper bound**: if every modulus is at most `M`, so is the Voigt mean. -/
theorem arith_le (M : ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hM : ∀ i ∈ s, E i ≤ M) : arith s c E ≤ M := by
  calc arith s c E ≤ ∑ i ∈ s, c i * M :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM i hi) (hc i hi)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **Lower bound**: if every modulus is at least `m > 0`, so is the Reuss mean. -/
theorem le_harmonic (m : ℝ) (hm : 0 < m) (hc : ∀ i ∈ s, 0 ≤ c i) (hsum : ∑ i ∈ s, c i = 1)
    (hmE : ∀ i ∈ s, m ≤ E i) : m ≤ harmonic s c E := by
  have hE : ∀ i ∈ s, 0 < E i := fun i hi => hm.trans_le (hmE i hi)
  have hSpos := compliance_pos hc hsum hE
  have hle : ∑ i ∈ s, c i / E i ≤ 1 / m :=
    calc ∑ i ∈ s, c i / E i ≤ ∑ i ∈ s, c i / m :=
          Finset.sum_le_sum fun i hi => div_le_div_of_nonneg_left (hc i hi) hm (hmE i hi)
      _ = 1 / m := by rw [← Finset.sum_div, hsum]
  unfold harmonic
  exact (le_one_div hm hSpos).mpr hle

/-- **Voigt–Reuss bounds, lower end**: `min Eᵢ ≤ (Σ cᵢ/Eᵢ)⁻¹`. -/
theorem inf'_le_harmonic (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsum : ∑ i ∈ s, c i = 1) (hE : ∀ i ∈ s, 0 < E i) : s.inf' hs E ≤ harmonic s c E := by
  obtain ⟨j, hj, hjE⟩ := Finset.exists_mem_eq_inf' hs E
  exact le_harmonic _ (hjE ▸ hE j hj) hc hsum fun _ hi => Finset.inf'_le E hi

/-- **Voigt–Reuss bounds, upper end**: `Σ cᵢ Eᵢ ≤ max Eᵢ`. -/
theorem arith_le_sup' (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsum : ∑ i ∈ s, c i = 1) : arith s c E ≤ s.sup' hs E :=
  arith_le _ hc hsum fun _ hi => Finset.le_sup' E hi

/-- **Voigt–Reuss bounds**: `min Eᵢ ≤ (Σ cᵢ/Eᵢ)⁻¹ ≤ Σ cᵢ Eᵢ ≤ max Eᵢ`. -/
theorem voigt_reuss_bounds (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsum : ∑ i ∈ s, c i = 1) (hE : ∀ i ∈ s, 0 < E i) :
    s.inf' hs E ≤ harmonic s c E ∧ harmonic s c E ≤ arith s c E ∧
      arith s c E ≤ s.sup' hs E :=
  ⟨inf'_le_harmonic hs hc hsum hE, harmonic_le_arith hc hsum hE, arith_le_sup' hs hc hsum⟩

end Bounds

/-! ### Orthotropic ply stiffness in plane stress -/

/-- The engineering constants of an orthotropic ply: moduli `E₁, E₂`, Poisson ratios
`ν₁₂, ν₂₁` and in-plane shear modulus `G₁₂`. -/
structure Ply where
  /-- The longitudinal modulus `E₁`. -/
  E₁ : ℝ
  /-- The transverse modulus `E₂`. -/
  E₂ : ℝ
  /-- The major Poisson ratio `ν₁₂`. -/
  ν₁₂ : ℝ
  /-- The minor Poisson ratio `ν₂₁`. -/
  ν₂₁ : ℝ
  /-- The in-plane shear modulus `G₁₂`. -/
  G₁₂ : ℝ

namespace Ply

variable (p : Ply)

/-- The Maxwell–Betti reciprocity relation `ν₂₁ / E₂ = ν₁₂ / E₁`. -/
def Reciprocal : Prop := p.ν₂₁ / p.E₂ = p.ν₁₂ / p.E₁

/-- The determinant factor `Δ = 1 - ν₁₂ ν₂₁`. -/
def Δ : ℝ := 1 - p.ν₁₂ * p.ν₂₁

/-- `Q₁₁ = E₁ / (1 - ν₁₂ν₂₁)`. -/
def Q11 : ℝ := p.E₁ / p.Δ

/-- `Q₂₂ = E₂ / (1 - ν₁₂ν₂₁)`. -/
def Q22 : ℝ := p.E₂ / p.Δ

/-- `Q₁₂ = ν₁₂ E₂ / (1 - ν₁₂ν₂₁)`. -/
def Q12 : ℝ := p.ν₁₂ * p.E₂ / p.Δ

/-- `Q₆₆ = G₁₂`. -/
def Q66 : ℝ := p.G₁₂

/-- The plane-stress compliance in Voigt notation:
`ε₁ = σ₁/E₁ - ν₂₁σ₂/E₂`, `ε₂ = -ν₁₂σ₁/E₁ + σ₂/E₂`, `γ₁₂ = τ₁₂/G₁₂`. -/
def sMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / p.E₁, -p.ν₂₁ / p.E₂, 0; -p.ν₁₂ / p.E₁, 1 / p.E₂, 0; 0, 0, 1 / p.G₁₂]

/-- The reduced stiffness obtained by inverting `sMat`; its `(1,2)` entry is `ν₂₁E₁/Δ` and its
`(2,1)` entry `ν₁₂E₂/Δ = Q₁₂`. -/
def qMat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![p.Q11, p.ν₂₁ * p.E₁ / p.Δ, 0; p.Q12, p.Q22, 0; 0, 0, p.Q66]

/-- Under reciprocity, `ν₂₁ E₁ / Δ = Q₁₂`. -/
theorem Q12_eq_of_reciprocal (h : p.Reciprocal) (h1 : p.E₁ ≠ 0) (h2 : p.E₂ ≠ 0) :
    p.ν₂₁ * p.E₁ / p.Δ = p.Q12 := by
  unfold Reciprocal at h
  unfold Q12
  congr 1
  field_simp at h
  linarith

/-- **Symmetry of the reduced stiffness** under reciprocity. -/
theorem qMat_isSymm (h : p.Reciprocal) (h1 : p.E₁ ≠ 0) (h2 : p.E₂ ≠ 0) : p.qMat.IsSymm := by
  have := p.Q12_eq_of_reciprocal h h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat, this]

/-- Under reciprocity, `Q = !![Q₁₁, Q₁₂, 0; Q₁₂, Q₂₂, 0; 0, 0, Q₆₆]`. -/
theorem qMat_eq (h : p.Reciprocal) (h1 : p.E₁ ≠ 0) (h2 : p.E₂ ≠ 0) :
    p.qMat = !![p.Q11, p.Q12, 0; p.Q12, p.Q22, 0; 0, 0, p.Q66] := by
  rw [qMat, p.Q12_eq_of_reciprocal h h1 h2]

/-- The reduced stiffness inverts the compliance: `Q S = 1`. -/
theorem qMat_mul_sMat (h1 : p.E₁ ≠ 0) (h2 : p.E₂ ≠ 0) (hG : p.G₁₂ ≠ 0) (hΔ : p.Δ ≠ 0) :
    p.qMat * p.sMat = 1 := by
  have hΔ' : 1 - p.ν₁₂ * p.ν₂₁ ≠ 0 := hΔ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMat, sMat, Q11, Q12, Q22, Q66, Δ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

end Ply

/-! ### Transformed stiffness -/

/-- The stress transformation matrix `T(θ)` in Voigt notation `(σ₁, σ₂, τ₁₂)`. -/
def tMat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ ^ 2, sin θ ^ 2, 2 * sin θ * cos θ;
    sin θ ^ 2, cos θ ^ 2, -2 * sin θ * cos θ;
    -(sin θ * cos θ), sin θ * cos θ, cos θ ^ 2 - sin θ ^ 2]

/-- The inverse `T(θ)⁻¹ = T(-θ)` of the stress transformation matrix. -/
def tInv (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ ^ 2, sin θ ^ 2, -(2 * sin θ * cos θ);
    sin θ ^ 2, cos θ ^ 2, 2 * sin θ * cos θ;
    sin θ * cos θ, -(sin θ * cos θ), cos θ ^ 2 - sin θ ^ 2]

/-- `tInv θ` is indeed the inverse of `tMat θ`: `T(θ) T(θ)⁻¹ = 1`. -/
theorem tMat_mul_tInv (θ : ℝ) : tMat θ * tInv θ = 1 := by
  have h := sin_sq_add_cos_sq θ
  simp only [tMat, tInv, Matrix.mul_fin_three, Matrix.one_fin_three,
    EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first
    | ring1
    | linear_combination (sin θ ^ 2 + cos θ ^ 2 + 1) * h

/-- `T(θ)⁻¹ T(θ) = 1`. -/
theorem tInv_mul_tMat (θ : ℝ) : tInv θ * tMat θ = 1 :=
  mul_eq_one_comm.mp (tMat_mul_tInv θ)

/-- The transformed (off-axis) reduced stiffness `Q̄(θ) = T(θ)⁻¹ Q T(θ)⁻ᵀ`. -/
def qBar (Q : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  tInv θ * Q * (tInv θ)ᵀ

/-- `Q̄(θ)` is symmetric whenever `Q` is. -/
theorem qBar_isSymm {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q.IsSymm) (θ : ℝ) :
    (qBar Q θ).IsSymm := by
  unfold qBar Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ.eq,
    Matrix.mul_assoc]

section Orthotropic

variable (Q₁₁ Q₁₂ Q₂₂ Q₆₆ θ : ℝ)

/-- The specially orthotropic reduced stiffness `!![Q₁₁, Q₁₂, 0; Q₁₂, Q₂₂, 0; 0, 0, Q₆₆]`. -/
def orthoQ : Matrix (Fin 3) (Fin 3) ℝ := !![Q₁₁, Q₁₂, 0; Q₁₂, Q₂₂, 0; 0, 0, Q₆₆]

/-- **`Q̄₁₁`** `= Q₁₁c⁴ + 2(Q₁₂ + 2Q₆₆)s²c² + Q₂₂s⁴`, computed from the matrix product. -/
theorem qBar_00 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 0 0 =
    Q₁₁ * cos θ ^ 4 + 2 * (Q₁₂ + 2 * Q₆₆) * sin θ ^ 2 * cos θ ^ 2 + Q₂₂ * sin θ ^ 4 := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **`Q̄₂₂`** `= Q₁₁s⁴ + 2(Q₁₂ + 2Q₆₆)s²c² + Q₂₂c⁴`. -/
theorem qBar_11 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 1 1 =
    Q₁₁ * sin θ ^ 4 + 2 * (Q₁₂ + 2 * Q₆₆) * sin θ ^ 2 * cos θ ^ 2 + Q₂₂ * cos θ ^ 4 := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **`Q̄₁₂`** `= (Q₁₁ + Q₂₂ - 4Q₆₆)s²c² + Q₁₂(s⁴ + c⁴)`. -/
theorem qBar_01 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 0 1 =
    (Q₁₁ + Q₂₂ - 4 * Q₆₆) * sin θ ^ 2 * cos θ ^ 2 + Q₁₂ * (sin θ ^ 4 + cos θ ^ 4) := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **`Q̄₆₆`** `= (Q₁₁ + Q₂₂ - 2Q₁₂ - 2Q₆₆)s²c² + Q₆₆(s⁴ + c⁴)`. -/
theorem qBar_22 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 2 2 =
    (Q₁₁ + Q₂₂ - 2 * Q₁₂ - 2 * Q₆₆) * sin θ ^ 2 * cos θ ^ 2 +
      Q₆₆ * (sin θ ^ 4 + cos θ ^ 4) := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **`Q̄₁₆`** `= (Q₁₁ - Q₁₂ - 2Q₆₆)sc³ + (Q₁₂ - Q₂₂ + 2Q₆₆)s³c`. -/
theorem qBar_02 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 0 2 =
    (Q₁₁ - Q₁₂ - 2 * Q₆₆) * sin θ * cos θ ^ 3 +
      (Q₁₂ - Q₂₂ + 2 * Q₆₆) * sin θ ^ 3 * cos θ := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **`Q̄₂₆`** `= (Q₁₁ - Q₁₂ - 2Q₆₆)s³c + (Q₁₂ - Q₂₂ + 2Q₆₆)sc³`. -/
theorem qBar_12 : qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 1 2 =
    (Q₁₁ - Q₁₂ - 2 * Q₆₆) * sin θ ^ 3 * cos θ +
      (Q₁₂ - Q₂₂ + 2 * Q₆₆) * sin θ * cos θ ^ 3 := by
  simp [qBar, orthoQ, tInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **Rotational invariant**: `Q̄₁₁ + Q̄₂₂ + 2Q̄₁₂ = Q₁₁ + Q₂₂ + 2Q₁₂` for every `θ`. -/
theorem qBar_invariant :
    qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 0 0 + qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 1 1 +
      2 * qBar (orthoQ Q₁₁ Q₁₂ Q₂₂ Q₆₆) θ 0 1 = Q₁₁ + Q₂₂ + 2 * Q₁₂ := by
  rw [qBar_00, qBar_11, qBar_01]
  linear_combination
    (Q₁₁ + Q₂₂ + 2 * Q₁₂) * (sin θ ^ 2 + cos θ ^ 2 + 1) * sin_sq_add_cos_sq θ

/-- At `θ = 0` the transformed stiffness is the on-axis one. -/
theorem qBar_zero (Q : Matrix (Fin 3) (Fin 3) ℝ) : qBar Q 0 = Q := by
  have h : tInv 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tInv]
  simp [qBar, h]

end Orthotropic

/-! ### Classical lamination theory -/

section Lamination

variable {N : ℕ} (Q : Fin N → Matrix (Fin 3) (Fin 3) ℝ) (z : Fin (N + 1) → ℝ)

/-- The extensional stiffness `A = Σₖ Q̄ₖ (zₖ - zₖ₋₁)`; ply `k` lies between the interfaces
`z k.castSucc` and `z k.succ`. -/
def aMat : Matrix (Fin 3) (Fin 3) ℝ := ∑ k, (z k.succ - z k.castSucc) • Q k

/-- The coupling stiffness `B = ½ Σₖ Q̄ₖ (zₖ² - zₖ₋₁²)`. -/
def bMat : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • ∑ k, (z k.succ ^ 2 - z k.castSucc ^ 2) • Q k

/-- The bending stiffness `D = ⅓ Σₖ Q̄ₖ (zₖ³ - zₖ₋₁³)`. -/
def dMat : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 3 : ℝ) • ∑ k, (z k.succ ^ 3 - z k.castSucc ^ 3) • Q k

variable {Q z}

/-- **Midplane-symmetric laminates are uncoupled**: if ply `k` and ply `N + 1 - k` coincide
(`Q (Fin.rev k) = Q k`) and the interfaces are mirrored (`z (Fin.rev j) = -z j`), then `B = 0`. -/
theorem bMat_eq_zero_of_symmetric (hQ : ∀ k, Q k.rev = Q k) (hz : ∀ j, z j.rev = -z j) :
    bMat Q z = 0 := by
  set f : Fin N → Matrix (Fin 3) (Fin 3) ℝ :=
    fun k => (z k.succ ^ 2 - z k.castSucc ^ 2) • Q k with hf
  have hrev : ∀ k, f k.rev = -f k := by
    intro k
    simp only [hf, hQ]
    rw [← Fin.rev_castSucc, ← Fin.rev_succ, hz, hz, ← neg_smul]
    congr 1
    ring
  have hsum : ∑ k, f k = -∑ k, f k := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ k, f k = ∑ k, f (Fin.revPerm k) := (Equiv.sum_comp Fin.revPerm f).symm
      _ = ∑ k, -f k := by simp [hrev]
  have h0 : ∑ k, f k = 0 := by
    have : (2 : ℝ) • ∑ k, f k = 0 := by rw [two_smul]; nth_rw 1 [hsum]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  unfold bMat
  rw [← hf, h0, smul_zero]

/-- **`A` is symmetric** when every ply stiffness is. -/
theorem aMat_isSymm (hQ : ∀ k, (Q k).IsSymm) : (aMat Q z).IsSymm := by
  unfold aMat Matrix.IsSymm
  simp [Matrix.transpose_sum, Matrix.transpose_smul, fun k => (hQ k).eq]

/-- **`B` is symmetric** when every ply stiffness is. -/
theorem bMat_isSymm (hQ : ∀ k, (Q k).IsSymm) : (bMat Q z).IsSymm := by
  unfold bMat Matrix.IsSymm
  simp [Matrix.transpose_sum, Matrix.transpose_smul, fun k => (hQ k).eq]

/-- **`D` is symmetric** when every ply stiffness is. -/
theorem dMat_isSymm (hQ : ∀ k, (Q k).IsSymm) : (dMat Q z).IsSymm := by
  unfold dMat Matrix.IsSymm
  simp [Matrix.transpose_sum, Matrix.transpose_smul, fun k => (hQ k).eq]

/-- The interfaces `-h/2, h/2` of a single layer of thickness `h` centred on the midplane. -/
def singleZ (h : ℝ) : Fin 2 → ℝ := ![-(h / 2), h / 2]

/-- **Single layer, extension**: `A = h Q`. -/
theorem single_layer_aMat (P : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) :
    aMat (fun _ : Fin 1 => P) (singleZ h) = h • P := by
  simp only [aMat, Fin.sum_univ_one, singleZ]
  congr 1
  simp

/-- **Single layer, coupling**: `B = 0`. -/
theorem single_layer_bMat (P : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) :
    bMat (fun _ : Fin 1 => P) (singleZ h) = 0 := by
  simp [bMat, singleZ]

/-- **Single layer, bending**: `D = h³ Q / 12`. -/
theorem single_layer_dMat (P : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) :
    dMat (fun _ : Fin 1 => P) (singleZ h) = (h ^ 3 / 12) • P := by
  simp only [dMat, Fin.sum_univ_one, singleZ, smul_smul]
  congr 1
  simp
  ring

/-- The plane-stress stiffness `E/(1 - ν²) · !![1, ν, 0; ν, 1, 0; 0, 0, (1 - ν)/2]` of an
isotropic layer (`Q₆₆ = G = E/(2(1 + ν))`). -/
def isoQ (E ν : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  orthoQ (E / (1 - ν ^ 2)) (ν * E / (1 - ν ^ 2)) (E / (1 - ν ^ 2)) (E / (2 * (1 + ν)))

/-- The isotropic plane-stress stiffness is symmetric. -/
theorem isoQ_isSymm (E ν : ℝ) : (isoQ E ν).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isoQ, orthoQ]

/-- **Single isotropic layer** of thickness `h`: `A = hQ`, `B = 0`, `D = h³Q/12`. -/
theorem single_isotropic_layer (E ν h : ℝ) :
    aMat (fun _ : Fin 1 => isoQ E ν) (singleZ h) = h • isoQ E ν ∧
      bMat (fun _ : Fin 1 => isoQ E ν) (singleZ h) = 0 ∧
      dMat (fun _ : Fin 1 => isoQ E ν) (singleZ h) = (h ^ 3 / 12) • isoQ E ν :=
  ⟨single_layer_aMat _ h, single_layer_bMat _ h, single_layer_dMat _ h⟩

end Lamination

end ContinuumMechanics.Composites
