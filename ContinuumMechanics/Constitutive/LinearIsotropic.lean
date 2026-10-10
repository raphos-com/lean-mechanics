import ContinuumMechanics.Tensor.Fourth
import ContinuumMechanics.Tensor.Orthogonal

/-!
# Linear isotropic elasticity

The constitutive law of a linear isotropic elastic material is
`σ = ℂ ε = λ (tr ε) I + 2μ ε` with Lamé moduli `λ`, `μ` ([Gurtin1981], §22; [Ciarlet1988], §3.8).
Equivalent parameter sets are Young's modulus and Poisson's ratio `(E, ν)` and bulk and shear
moduli `(K, G)`:

`E = μ (3λ + 2μ) / (λ + μ)`, `ν = λ / (2 (λ + μ))`, `K = λ + 2μ / 3`, `G = μ`,
`λ = E ν / ((1 + ν)(1 - 2ν))`, `μ = E / (2 (1 + ν))`.

## Main results

* `Lin4.isotropic_dcontr_self_eq`: `ℂA : A = (λ + 2μ/d)(tr A)² + 2μ dev A : dev A` on `Sym`.
* `Lin4.isotropic_posDefOnSym_iff`: in dimension `d ≥ 2`,
  `ℂ` is positive definite on symmetric tensors iff `μ > 0 ∧ dλ + 2μ > 0`
  (so `μ > 0 ∧ 3λ + 2μ > 0` in 3D). [Gurtin1981], §22.
* `Lame.posDef_iff_young_poisson`, `Lame.posDef_iff_bulk_shear`: the same condition in the other
  parameter sets: `E > 0 ∧ -1 < ν < ½`, and `K > 0 ∧ G > 0`.
* Round-trip lemmas between the parameter sets.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §22.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §3.8.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin4

open Lin

/-- `A : A = (tr A)² / d + dev A : dev A`. -/
theorem dcontr_self_eq_tr_dev [Nontrivial E] (A : Lin E) :
    A ⊡ A = tr A ^ 2 / finrank ℝ E + dev A ⊡ dev A := by
  have hd : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hsph : sph A ⊡ sph A = tr A ^ 2 / finrank ℝ E := by
    rw [sph_apply]
    simp only [map_smul, LinearMap.smul_apply, dcontr_one, tr_one, smul_eq_mul]
    field_simp
  conv_lhs => rw [← sph_add_dev A]
  simp only [map_add, LinearMap.add_apply, sph_dcontr_dev, dcontr_comm (dev A) (sph A), hsph]
  ring

/-- `ℂA : A = (λ + 2μ/d)(tr A)² + 2μ dev A : dev A` for symmetric `A`. -/
theorem isotropic_dcontr_self_eq [Nontrivial E] (lam mu : ℝ) {A : Lin E} (hA : A ∈ Sym E) :
    isotropic lam mu A ⊡ A =
      (lam + 2 * mu / finrank ℝ E) * tr A ^ 2 + 2 * mu * (dev A ⊡ dev A) := by
  rw [isotropic_dcontr_self lam mu hA, dcontr_self_eq_tr_dev]
  ring

/-- **Positive definiteness of the isotropic elasticity tensor**: in dimension `d ≥ 2`,
`λ I⊗I + 2μ 𝕀ˢʸᵐ` is positive definite on symmetric tensors iff `μ > 0` and `dλ + 2μ > 0`.
[Gurtin1981], §22. -/
theorem isotropic_posDefOnSym_iff (hd : 2 ≤ finrank ℝ E) (lam mu : ℝ) :
    (isotropic lam mu : Lin4 E).PosDefOnSym ↔ 0 < mu ∧ 0 < finrank ℝ E * lam + 2 * mu := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set d : ℝ := (finrank ℝ E : ℝ) with hd_def
  have hdpos : 0 < d := by rw [hd_def]; exact_mod_cast (by omega : 0 < finrank ℝ E)
  constructor
  · intro h
    -- test with `A = I`
    have hI := h 1 (mem_sym_iff.mpr transpose_one) one_ne_zero
    rw [isotropic_dcontr_self lam mu (mem_sym_iff.mpr transpose_one), tr_one, dcontr_one,
      tr_one] at hI
    -- test with a traceless symmetric tensor `e₁ ⊗ e₁ - e₂ ⊗ e₂`
    let b := stdOrthonormalBasis ℝ E
    let e₁ := b ⟨0, by omega⟩
    let e₂ := b ⟨1, by omega⟩
    have h11 : ⟪e₁, e₁⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1, one_pow]
    have h22 : ⟪e₂, e₂⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1, one_pow]
    have h12 : ⟪e₁, e₂⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
    have h21 : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact h12
    set A := e₁ ⊗ e₁ - e₂ ⊗ e₂
    have hAs : A ∈ Sym E := by
      rw [mem_sym_iff, star_sub, dyad_transpose, dyad_transpose]
    have hn1 : ‖e₁‖ = 1 := b.orthonormal.1 _
    have hn2 : ‖e₂‖ = 1 := b.orthonormal.1 _
    have htr : tr A = 0 := by simp [A, hn1, hn2]
    have hAA : A ⊡ A = 2 := by
      simp only [A, map_sub, LinearMap.sub_apply, dyad_dcontr_dyad, h11, h22, h12, h21]
      norm_num
    have hA0 : A ≠ 0 := fun h0 => by simp [h0] at hAA
    have hAp := h A hAs hA0
    rw [isotropic_dcontr_self lam mu hAs, htr, hAA] at hAp
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hmu, hk⟩ A hA hA0
    rw [isotropic_dcontr_self_eq lam mu hA]
    have hk' : 0 < lam + 2 * mu / d := by
      have : lam + 2 * mu / d = (d * lam + 2 * mu) / d := by field_simp
      rw [this]; exact div_pos hk hdpos
    have hdev := dcontr_self_nonneg (dev A)
    have htr := sq_nonneg (tr A)
    by_cases hdz : dev A = 0
    · have htr0 : tr A ≠ 0 := by
        intro h0
        apply hA0
        rw [← sph_add_dev A, hdz, sph_apply, h0]
        simp
      have := dcontr_self_eq_zero.mpr hdz
      rw [this]
      have : 0 < tr A ^ 2 := by positivity
      nlinarith
    · have := dcontr_self_pos hdz
      nlinarith

end Lin4

/-! ### Elastic moduli -/

/-- Lamé moduli `λ`, `μ` of a linear isotropic material. -/
structure Lame where
  /-- First Lamé modulus `λ`. -/
  lam : ℝ
  /-- Shear modulus `μ`. -/
  mu : ℝ

namespace Lame

variable (m : Lame)

/-- Young's modulus `E = μ (3λ + 2μ) / (λ + μ)`. -/
noncomputable def young : ℝ := m.mu * (3 * m.lam + 2 * m.mu) / (m.lam + m.mu)

/-- Poisson's ratio `ν = λ / (2 (λ + μ))`. -/
noncomputable def poisson : ℝ := m.lam / (2 * (m.lam + m.mu))

/-- Bulk modulus `K = λ + 2μ/3`. -/
noncomputable def bulk : ℝ := m.lam + 2 * m.mu / 3

/-- Shear modulus `G = μ`. -/
def shear : ℝ := m.mu

/-- Lamé moduli from Young's modulus and Poisson's ratio:
`λ = E ν / ((1 + ν)(1 - 2ν))`, `μ = E / (2 (1 + ν))`. -/
noncomputable def ofYoungPoisson (Y ν : ℝ) : Lame :=
  ⟨Y * ν / ((1 + ν) * (1 - 2 * ν)), Y / (2 * (1 + ν))⟩

/-- Lamé moduli from bulk and shear moduli: `λ = K - 2G/3`, `μ = G`. -/
noncomputable def ofBulkShear (K G : ℝ) : Lame := ⟨K - 2 * G / 3, G⟩

/-- The positive-definiteness condition in three dimensions. -/
def PosDef : Prop := 0 < m.mu ∧ 0 < 3 * m.lam + 2 * m.mu

theorem sum_ofYoungPoisson {Y ν : ℝ} (h1 : 1 + ν ≠ 0) (h2 : 1 - 2 * ν ≠ 0) :
    (ofYoungPoisson Y ν).lam + (ofYoungPoisson Y ν).mu = Y / (2 * (1 + ν) * (1 - 2 * ν)) := by
  simp only [ofYoungPoisson]
  rw [div_add_div _ _ (mul_ne_zero h1 h2) (mul_ne_zero two_ne_zero h1),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero two_ne_zero h1))
      (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2)]
  ring

theorem young_ofYoungPoisson {Y ν : ℝ} (h1 : 1 + ν ≠ 0) (h2 : 1 - 2 * ν ≠ 0) (hY : Y ≠ 0) :
    (ofYoungPoisson Y ν).young = Y := by
  have hs := sum_ofYoungPoisson (Y := Y) h1 h2
  have hk : 3 * (ofYoungPoisson Y ν).lam + 2 * (ofYoungPoisson Y ν).mu = Y / (1 - 2 * ν) := by
    simp only [ofYoungPoisson]
    rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ (mul_ne_zero h1 h2)
      (mul_ne_zero two_ne_zero h1), div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2)
      (mul_ne_zero two_ne_zero h1)) h2]
    ring
  rw [young, hs, hk]
  simp only [ofYoungPoisson]
  rw [div_mul_div_comm, div_div_div_eq, div_eq_iff (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) hY)]
  ring

theorem poisson_ofYoungPoisson {Y ν : ℝ} (h1 : 1 + ν ≠ 0) (h2 : 1 - 2 * ν ≠ 0) (hY : Y ≠ 0) :
    (ofYoungPoisson Y ν).poisson = ν := by
  rw [poisson, sum_ofYoungPoisson h1 h2]
  simp only [ofYoungPoisson]
  have hD : 2 * (Y / (2 * (1 + ν) * (1 - 2 * ν))) ≠ 0 :=
    mul_ne_zero two_ne_zero (div_ne_zero hY (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2))
  rw [div_eq_iff hD, mul_div_assoc', mul_div_assoc', div_eq_div_iff (mul_ne_zero h1 h2)
    (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2)]
  ring

theorem ofBulkShear_bulk_shear (K G : ℝ) :
    (ofBulkShear K G).bulk = K ∧ (ofBulkShear K G).shear = G := by
  simp only [bulk, shear, ofBulkShear]; exact ⟨by ring, trivial⟩

/-- `μ > 0 ∧ 3λ + 2μ > 0 ⇔ K > 0 ∧ G > 0`. -/
theorem posDef_iff_bulk_shear : m.PosDef ↔ 0 < m.bulk ∧ 0 < m.shear := by
  simp only [PosDef, bulk, shear]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `μ > 0 ∧ 3λ + 2μ > 0 ⇔ E > 0 ∧ -1 < ν < ½`. [Gurtin1981], §22. -/
theorem posDef_iff_young_poisson :
    m.PosDef ↔ 0 < m.young ∧ -1 < m.poisson ∧ m.poisson < 1 / 2 := by
  simp only [PosDef, young, poisson]
  constructor
  · rintro ⟨hmu, hk⟩
    have hs : 0 < m.lam + m.mu := by linarith
    refine ⟨div_pos (mul_pos hmu hk) hs, ?_, ?_⟩
    · rw [lt_div_iff₀ (by positivity)]; linarith
    · rw [div_lt_iff₀ (by positivity)]; linarith
  · rintro ⟨hY, hν1, hν2⟩
    -- the sign of `λ + μ` is forced
    by_cases hs : 0 < m.lam + m.mu
    · rw [lt_div_iff₀ (by positivity)] at hν1
      rw [div_lt_iff₀ (by positivity)] at hν2
      constructor <;> linarith
    · exfalso
      rcases (not_lt.mp hs).lt_or_eq with hs | hs
      · have h2 : 2 * (m.lam + m.mu) < 0 := by linarith
        rw [lt_div_iff_of_neg h2] at hν1
        rw [div_lt_iff_of_neg h2] at hν2
        have hmu : m.mu < 0 := by linarith
        have hk : 3 * m.lam + 2 * m.mu < 0 := by linarith
        have : m.mu * (3 * m.lam + 2 * m.mu) / (m.lam + m.mu) < 0 :=
          div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hmu hk) hs
        linarith
      · rw [hs, div_zero] at hY; exact lt_irrefl 0 hY

end Lame

/-- The positive-definiteness condition, in three dimensions, in terms of Lamé moduli. -/
theorem Lin4.isotropic_posDefOnSym_iff_three (hd : finrank ℝ E = 3) (m : Lame) :
    (Lin4.isotropic m.lam m.mu : Lin4 E).PosDefOnSym ↔ m.PosDef := by
  rw [Lin4.isotropic_posDefOnSym_iff (by omega), hd, Lame.PosDef]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

section Examples

/-- Structural steel: `E = 210 GPa`, `ν = 0.3` gives `μ ≈ 80.8 GPa`, `λ ≈ 121.2 GPa`, and a positive
definite elasticity tensor. -/
example : (Lame.ofYoungPoisson 210 0.3).PosDef := by
  simp only [Lame.PosDef, Lame.ofYoungPoisson]
  norm_num

/-- Rubber-like incompressibility limit: `ν = ½` is excluded from the positive-definite range. -/
example (m : Lame) (h : m.PosDef) : m.poisson < 1 / 2 :=
  ((Lame.posDef_iff_young_poisson m).mp h).2.2

end Examples

end ContinuumMechanics
