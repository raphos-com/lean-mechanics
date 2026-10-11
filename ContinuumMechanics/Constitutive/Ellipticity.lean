import ContinuumMechanics.Tensor.Second

/-!
# Strong ellipticity and elastic waves in isotropic materials

For an isotropic linear elastic material with Lamé moduli `λ`, `μ`, the **acoustic tensor** in
the direction `n` is

`A(n) = μ |n|² I + (λ + μ) n ⊗ n`,

i.e. `A(n) m = ℂ(m ⊗ n) n`, with `(m ⊗ n) : ℂ (m ⊗ n) = A(n) m · m = μ |m|²|n|² + (λ + μ)(m · n)²`
(`inner_acoustic`) ([Gurtin1981], §§22, 31; [Achenbach1973], §4.2).

* **Strong ellipticity** (`stronglyElliptic_iff`): in dimension `≥ 2`,
  `A(n) m · m > 0` for all `m, n ≠ 0` iff `μ > 0` and `λ + 2μ > 0`. This is weaker than positive
  definiteness of `ℂ` (`μ > 0`, `dλ + 2μ > 0`, `Constitutive/LinearIsotropic`).
* **Plane waves** (`acoustic_eigen_iff`): a plane wave `u = a f(n · x - c t)` with unit `n`
  solves `div ℂ∇u = ρ ü` iff `ρc² a = A(n) a`. For `λ + μ ≠ 0` this holds iff either
  `a ∥ n` and `ρc² = λ + 2μ` (**longitudinal / P waves**), or `a ⊥ n` and `ρc² = μ`
  (**transverse / S waves**).

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§22, 31.
* [Achenbach1973] J. D. Achenbach, *Wave Propagation in Elastic Solids*, §4.2.
-/

open scoped InnerProductSpace ContinuumMechanics
open Module

noncomputable section

namespace ContinuumMechanics.Ellipticity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **acoustic tensor** `A(n) = μ |n|² I + (λ + μ) n ⊗ n` of an isotropic material. -/
def acoustic (lam μ : ℝ) (n : E) : Lin E := (μ * ‖n‖ ^ 2) • (1 : Lin E) + (lam + μ) • (n ⊗ n)

variable {lam μ : ℝ}

theorem acoustic_apply (n m : E) :
    acoustic lam μ n m = (μ * ‖n‖ ^ 2) • m + ((lam + μ) * ⟪n, m⟫_ℝ) • n := by
  simp [acoustic, dyad_apply, smul_smul]

/-- `A(n) m · m = μ |n|²|m|² + (λ + μ)(n · m)²`. -/
theorem inner_acoustic (n m : E) :
    ⟪acoustic lam μ n m, m⟫_ℝ = μ * ‖n‖ ^ 2 * ‖m‖ ^ 2 + (lam + μ) * ⟪n, m⟫_ℝ ^ 2 := by
  rw [acoustic_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

/-- `A(n) n = (λ + 2μ) n` for a unit vector `n`. -/
theorem acoustic_apply_self {n : E} (hn : ‖n‖ = 1) : acoustic lam μ n n = (lam + 2 * μ) • n := by
  rw [acoustic_apply, real_inner_self_eq_norm_sq, hn, ← add_smul]
  ring_nf

/-- `A(n) m = μ m` for a unit vector `n` and `m ⊥ n`. -/
theorem acoustic_apply_of_inner_eq_zero {n m : E} (hn : ‖n‖ = 1) (h : ⟪n, m⟫_ℝ = 0) :
    acoustic lam μ n m = μ • m := by
  rw [acoustic_apply, h, hn]
  simp

/-- **Strong ellipticity**: `A(n) m · m > 0` for all nonzero `m, n`. -/
def StronglyElliptic (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam μ : ℝ) : Prop :=
  ∀ n m : E, n ≠ 0 → m ≠ 0 → 0 < ⟪acoustic lam μ n m, m⟫_ℝ

/-- In dimension `≥ 2` there are nonzero orthogonal vectors. -/
theorem exists_orthogonal [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E) :
    ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ ⟪a, b⟫_ℝ = 0 := by
  have : Nontrivial E := Module.finrank_pos_iff (R := ℝ).mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : E)
  have hK : finrank ℝ (ℝ ∙ a)ᗮ = finrank ℝ E - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ a)
    rw [finrank_span_singleton ha] at h
    omega
  have hne : (ℝ ∙ a)ᗮ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hK
    omega
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨a, b, ha, hb0, Submodule.mem_orthogonal_singleton_iff_inner_right.mp hb⟩

/-- **Strong ellipticity of isotropic elasticity**: in dimension `≥ 2`, `ℂ` is strongly elliptic
iff `μ > 0` and `λ + 2μ > 0`. [Gurtin1981], §31. -/
theorem stronglyElliptic_iff [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E) :
    StronglyElliptic E lam μ ↔ 0 < μ ∧ 0 < lam + 2 * μ := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hab⟩ := exists_orthogonal (E := E) hE
    have h1 := h a b ha hb
    rw [inner_acoustic, hab] at h1
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hμ : 0 < μ := by
      by_contra hμ
      have : μ * ‖a‖ ^ 2 * ‖b‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hμ)
          (by positivity)) (by positivity)
      nlinarith
    refine ⟨hμ, ?_⟩
    have h2 := h a a ha ha
    rw [inner_acoustic, real_inner_self_eq_norm_sq] at h2
    have : 0 < ‖a‖ ^ 4 := by positivity
    nlinarith
  · rintro ⟨hμ, hl⟩ n m hn hm
    rw [inner_acoustic]
    have hn' : 0 < ‖n‖ := norm_pos_iff.mpr hn
    have hm' : 0 < ‖m‖ := norm_pos_iff.mpr hm
    have hcs : ⟪n, m⟫_ℝ ^ 2 ≤ ‖n‖ ^ 2 * ‖m‖ ^ 2 := by
      have := abs_real_inner_le_norm n m
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hp : 0 < ‖n‖ ^ 2 * ‖m‖ ^ 2 := by positivity
    by_cases hlm : 0 ≤ lam + μ
    · nlinarith [sq_nonneg ⟪n, m⟫_ℝ]
    · nlinarith

/-- **Plane waves in isotropic media**: for a unit direction `n`, an amplitude `a ≠ 0` and
`λ + μ ≠ 0`, the propagation condition `A(n) a = s a` (`s = ρc²`) holds iff the wave is
longitudinal (`a ∥ n`, `s = λ + 2μ`) or transverse (`a ⊥ n`, `s = μ`). -/
theorem acoustic_eigen_iff {n a : E} (hn : ‖n‖ = 1) (ha : a ≠ 0) (hlm : lam + μ ≠ 0) (s : ℝ) :
    acoustic lam μ n a = s • a ↔
      ((∃ t : ℝ, a = t • n) ∧ s = lam + 2 * μ) ∨ (⟪n, a⟫_ℝ = 0 ∧ s = μ) := by
  constructor
  · intro h
    rw [acoustic_apply, hn, one_pow, mul_one] at h
    -- `(s - μ) a = (λ + μ)(n · a) n`
    have key : (s - μ) • a = ((lam + μ) * ⟪n, a⟫_ℝ) • n := by
      rw [sub_smul, ← h]
      abel
    by_cases hna : ⟪n, a⟫_ℝ = 0
    · right
      refine ⟨hna, ?_⟩
      rw [hna, mul_zero, zero_smul, smul_eq_zero] at key
      exact sub_eq_zero.mp (key.resolve_right ha)
    · left
      have hs : s = lam + 2 * μ := by
        have := congrArg (fun v => ⟪n, v⟫_ℝ) key
        simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hn] at this
        have := mul_right_cancel₀ hna (by linarith : (s - μ) * ⟪n, a⟫_ℝ = (lam + μ) * ⟪n, a⟫_ℝ)
        linarith
      refine ⟨⟨⟪n, a⟫_ℝ, ?_⟩, hs⟩
      rw [hs, show lam + 2 * μ - μ = lam + μ by ring, mul_smul] at key
      exact smul_right_injective E hlm key
  · rintro (⟨⟨t, rfl⟩, rfl⟩ | ⟨hna, rfl⟩)
    · rw [map_smul, acoustic_apply_self hn, smul_comm]
    · exact acoustic_apply_of_inner_eq_zero hn hna

end ContinuumMechanics.Ellipticity
