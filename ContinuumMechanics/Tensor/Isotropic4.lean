import ContinuumMechanics.Tensor.Fourth
import ContinuumMechanics.Tensor.Orthogonal
import ContinuumMechanics.Tensor.Spectral

/-!
# Isotropic fourth-order tensors

A fourth-order tensor `ℂ` is **isotropic** if `ℂ(Q A Qᵀ) = Q ℂ(A) Qᵀ` for every orthogonal `Q`.
The **representation theorem** ([Gurtin1981], §22, Thm. 1; [Ciarlet1988], Thm. 3.6-2) states that
on symmetric tensors every isotropic `ℂ` has the form `ℂ = λ I ⊗ I + 2μ 𝕀ˢʸᵐ`.

The proof here uses only reflections `R_h = I - 2 h ⊗ h` and works in any dimension `≥ 2`:

1. A reflection fixing `e ⊗ e` commutes with `B = ℂ(e ⊗ e)`; hence `e` and every unit vector
   `f ⊥ e` are eigenvectors of `B`, and reflections swapping two such `f` show the eigenvalue on
   `e^⊥` is a single number. So `ℂ(e ⊗ e) = α I + β e ⊗ e`.
2. Reflections act transitively on unit vectors, so `α`, `β` do not depend on `e`.
3. By the spectral theorem every symmetric `A = ∑ λᵢ eᵢ ⊗ eᵢ`, hence
   `ℂ A = α (tr A) I + β A`.

## Main results

* `Lin4.IsIsotropic`, `Lin4.isotropic_isIsotropic` (the converse direction).
* `Lin4.IsIsotropic.exists_lame`: the representation theorem.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §22.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §3.6.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- The **reflection** `R_h = I - 2 h ⊗ h` across the hyperplane orthogonal to `h`. -/
noncomputable def reflection (h : E) : Lin E := 1 - (2 : ℝ) • (h ⊗ h)

omit [FiniteDimensional ℝ E] in
theorem reflection_apply (h v : E) : reflection h v = v - (2 * ⟪h, v⟫_ℝ) • h := by
  simp [reflection, smul_smul]

theorem transpose_reflection (h : E) : (reflection h)ᵀ = reflection h := by
  rw [reflection, star_sub, star_one, transpose_smul, dyad_transpose]

omit [FiniteDimensional ℝ E] in
theorem reflection_mul_self {h : E} (hh : ‖h‖ = 1) : reflection h * reflection h = 1 := by
  ext v
  have h1 : ⟪h, h⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hh, one_pow]
  simp only [Lin.mul_apply, reflection_apply, inner_sub_right, inner_smul_right,
    h1, one_apply_eq_self]
  module

theorem reflection_mem_orth {h : E} (hh : ‖h‖ = 1) : reflection h ∈ Orth E := by
  rw [mem_orth_iff, transpose_reflection, reflection_mul_self hh]

/-- Conjugating a dyad: `Q (a ⊗ b) Qᵀ = (Q a) ⊗ (Q b)`. -/
theorem conj_dyad (Q : Lin E) (a b : E) : Q * (a ⊗ b) * Qᵀ = (Q a) ⊗ (Q b) := by
  rw [mul_dyad, dyad_mul, transpose_transpose]

omit [FiniteDimensional ℝ E] in
/-- A reflection swapping two distinct unit vectors `a`, `b`: `R_h a = b` for
`h = (a - b) / ‖a - b‖`. -/
theorem reflection_swap {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    let h := ‖a - b‖⁻¹ • (a - b)
    ‖h‖ = 1 ∧ reflection h a = b := by
  intro h
  have hne : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
  refine ⟨by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne], ?_⟩
  have hsq : ‖a - b‖ ^ 2 = 2 * (1 - ⟪b, a⟫_ℝ) := by
    rw [norm_sub_sq_real, ha, hb, real_inner_comm a b]; ring
  have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
  rw [reflection_apply]
  simp only [h, inner_smul_left, inner_sub_left, haa, RCLike.conj_to_real, smul_smul]
  have hcoef : 2 * (‖a - b‖⁻¹ * (1 - ⟪b, a⟫_ℝ)) * ‖a - b‖⁻¹ = 1 := by
    have hinv : ‖a - b‖⁻¹ * ‖a - b‖⁻¹ = (‖a - b‖ ^ 2)⁻¹ := by rw [sq, mul_inv]
    have hpos : 2 * (1 - ⟪b, a⟫_ℝ) ≠ 0 := by rw [← hsq]; exact pow_ne_zero 2 hne
    calc 2 * (‖a - b‖⁻¹ * (1 - ⟪b, a⟫_ℝ)) * ‖a - b‖⁻¹
        = 2 * (1 - ⟪b, a⟫_ℝ) * (‖a - b‖⁻¹ * ‖a - b‖⁻¹) := by ring
      _ = 1 := by rw [hinv, hsq, mul_inv_cancel₀ hpos]
  rw [hcoef, one_smul, sub_sub_cancel]

omit [FiniteDimensional ℝ E] in
theorem inner_reflection_of_orth {h e : E} (he : ⟪h, e⟫_ℝ = 0) : reflection h e = e := by
  rw [reflection_apply, he, mul_zero, zero_smul, sub_zero]

end Lin

namespace Lin4

open Lin

/-- A fourth-order tensor is **isotropic** if `ℂ(Q A Qᵀ) = Q ℂ(A) Qᵀ` for all orthogonal `Q`.
[Gurtin1981], §22. -/
def IsIsotropic (C : Lin4 E) : Prop :=
  ∀ Q ∈ Orth E, ∀ A, C (Q * A * Qᵀ) = Q * C A * Qᵀ

/-- `λ I ⊗ I + 2μ 𝕀ˢʸᵐ` is isotropic. -/
theorem isotropic_isIsotropic (lam mu : ℝ) : (isotropic lam mu : Lin4 E).IsIsotropic := by
  intro Q hQ A
  have hQQ := transpose_mul_self_of_mem_orth hQ
  have htr : tr (Q * A * Qᵀ) = tr A := by rw [tr_mul_comm, ← mul_assoc, hQQ, one_mul]
  have hsym : sym (Q * A * Qᵀ) = Q * sym A * Qᵀ := by
    rw [sym_apply, sym_apply, transpose_mul, transpose_mul, transpose_transpose, mul_smul_comm,
      smul_mul_assoc, mul_add, add_mul, mul_assoc Q Aᵀ]
  rw [isotropic_apply, isotropic_apply, htr, hsym, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, mul_transpose_self_of_mem_orth hQ, mul_smul_comm, smul_mul_assoc]

section Representation

variable {C : Lin4 E} (hC : C.IsIsotropic)
include hC

/-- If an orthogonal, symmetric `Q` fixes `A` under conjugation, it commutes with `ℂ(A)`. -/
theorem commute_of_fix {Q A : Lin E} (hQ : Q ∈ Orth E) (hQs : Qᵀ = Q) (hfix : Q * A * Qᵀ = A) :
    Q * C A = C A * Q := by
  have h := hC Q hQ A
  rw [hfix, hQs] at h
  have hQQ : Q * Q = 1 := by rw [← hQs]; nth_rw 2 [← hQs]; rw [transpose_transpose];
                               exact (transpose_mul_self_of_mem_orth hQ)
  calc Q * C A = Q * (Q * C A * Q) := by rw [← h]
    _ = (Q * Q) * C A * Q := by simp only [mul_assoc]
    _ = C A * Q := by rw [hQQ, one_mul]

/-- If a reflection `R_h` (`‖h‖ = 1`) fixes `A`, then `h` is an eigenvector of `ℂ(A)`. -/
theorem eigen_of_reflection_fix {h : E} {A : Lin E} (hh : ‖h‖ = 1)
    (hfix : reflection h * A * (reflection h)ᵀ = A) :
    C A h = ⟪h, C A h⟫_ℝ • h := by
  have hc := commute_of_fix hC (reflection_mem_orth hh) (transpose_reflection h) hfix
  have h1 : ⟪h, h⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hh, one_pow]
  have key := congrArg (fun T : Lin E => T h) hc
  simp only [Lin.mul_apply, reflection_apply, h1] at key
  rw [show h - (2 * 1 : ℝ) • h = -h by module, map_neg] at key
  linear_combination (norm := module) (1 / 2 : ℝ) • key

variable {e : E} (he : ‖e‖ = 1)
include he

omit hC in
/-- Reflections in hyperplanes containing `e`, and in `e^⊥`, fix `e ⊗ e`. -/
theorem reflection_fix_dyad {h : E} (hh : ⟪h, e⟫_ℝ = 0 ∨ h = e) (hu : ‖h‖ = 1) :
    reflection h * (e ⊗ e) * (reflection h)ᵀ = e ⊗ e := by
  rw [conj_dyad]
  rcases hh with hh | rfl
  · rw [inner_reflection_of_orth hh]
  · have h1 : ⟪h, h⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hm : reflection h h = -h := by rw [reflection_apply, h1]; module
    rw [hm]
    ext v
    simp

/-- **Step 1** (`ℂ(e ⊗ e) = α I + β e ⊗ e` on `e^⊥`): for unit `f, g ⊥ e`,
`f · ℂ(e⊗e) f = g · ℂ(e⊗e) g`. -/
theorem inner_apply_eq_of_orth {f g : E} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (hfe : ⟪f, e⟫_ℝ = 0) (hge : ⟪g, e⟫_ℝ = 0) :
    ⟪f, C (e ⊗ e) f⟫_ℝ = ⟪g, C (e ⊗ e) g⟫_ℝ := by
  by_cases hfg : f = g
  · rw [hfg]
  obtain ⟨hh, hswap⟩ := reflection_swap hf hg hfg
  set h := ‖f - g‖⁻¹ • (f - g)
  have hhe : ⟪h, e⟫_ℝ = 0 := by
    simp only [h, inner_smul_left, inner_sub_left, hfe, hge, sub_self, mul_zero]
  have hc := commute_of_fix hC (reflection_mem_orth hh) (transpose_reflection h)
    (reflection_fix_dyad he (Or.inl hhe) hh)
  have hQ := mem_orth_iff_inner.mp (reflection_mem_orth hh)
  rw [← hswap, ← Lin.mul_apply, ← hc, Lin.mul_apply, hQ]

/-- **Step 1**: given a unit `f₀ ⊥ e`, `ℂ(e ⊗ e) = α I + (γ - α) e ⊗ e` with
`α = f₀ · ℂ(e⊗e) f₀` and `γ = e · ℂ(e⊗e) e`. -/
theorem apply_dyad_self_eq {f₀ : E} (hf₀ : ‖f₀‖ = 1) (hf₀e : ⟪f₀, e⟫_ℝ = 0) :
    C (e ⊗ e) = ⟪f₀, C (e ⊗ e) f₀⟫_ℝ • (1 : Lin E)
      + (⟪e, C (e ⊗ e) e⟫_ℝ - ⟪f₀, C (e ⊗ e) f₀⟫_ℝ) • (e ⊗ e) := by
  set B := C (e ⊗ e)
  set α := ⟪f₀, B f₀⟫_ℝ
  have he1 : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hBe : B e = ⟪e, B e⟫_ℝ • e :=
    eigen_of_reflection_fix hC he (reflection_fix_dyad he (Or.inr rfl) he)
  have hBf : ∀ f : E, ‖f‖ = 1 → ⟪f, e⟫_ℝ = 0 → B f = α • f := fun f hf hfe => by
    rw [eigen_of_reflection_fix hC hf (reflection_fix_dyad he (Or.inl hfe) hf),
      inner_apply_eq_of_orth hC he hf hf₀ hfe hf₀e]
  ext v
  set u := v - ⟪e, v⟫_ℝ • e with hu_def
  have hue : ⟪u, e⟫_ℝ = 0 := by
    simp only [u, inner_sub_left, inner_smul_left, he1, RCLike.conj_to_real, mul_one,
      real_inner_comm e v, sub_self]
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
  have hBu : B u = α • u := by
    by_cases hu : u = 0
    · rw [hu, map_zero, smul_zero]
    · have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      have h1 := hBf (‖u‖⁻¹ • u) (norm_smul_inv_norm hu)
        (by rw [inner_smul_left, hue, mul_zero])
      rw [map_smul, smul_comm] at h1
      exact smul_right_injective E (inv_ne_zero hn) h1
  have hv : v = u + ⟪e, v⟫_ℝ • e := by rw [hu_def, sub_add_cancel]
  rw [hv, map_add, map_smul, hBu, hBe]
  simp only [add_apply, smul_apply, one_apply_eq_self,
    dyad_apply, inner_add_right, inner_smul_right, heu, he1]
  module

end Representation

/-- **Step 2** (transport): if `ℂ(e₀ ⊗ e₀) = α I + β e₀ ⊗ e₀` for one unit `e₀`, the same holds
for every unit `e`. -/
theorem IsIsotropic.apply_dyad_self_of {C : Lin4 E} (hC : C.IsIsotropic) {e₀ : E}
    (he₀ : ‖e₀‖ = 1) {α β : ℝ} (h0 : C (e₀ ⊗ e₀) = α • (1 : Lin E) + β • (e₀ ⊗ e₀)) {e : E}
    (he : ‖e‖ = 1) : C (e ⊗ e) = α • (1 : Lin E) + β • (e ⊗ e) := by
  by_cases h : e₀ = e
  · rw [← h, h0]
  obtain ⟨hh, hswap⟩ := reflection_swap he₀ he h
  set Q := reflection (‖e₀ - e‖⁻¹ • (e₀ - e))
  have hQ := reflection_mem_orth hh
  have hconj : e ⊗ e = Q * (e₀ ⊗ e₀) * Qᵀ := by rw [conj_dyad, hswap]
  rw [hconj, hC Q hQ, h0, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    mul_transpose_self_of_mem_orth hQ, mul_smul_comm, smul_mul_assoc]

/-- **Representation theorem for isotropic fourth-order tensors**: in dimension `≥ 2`, an
isotropic `ℂ` acts on symmetric tensors as `ℂ A = λ (tr A) I + 2μ A` for some `λ`, `μ`.
[Gurtin1981], §22, Thm. 1; [Ciarlet1988], Thm. 3.6-2. -/
theorem IsIsotropic.exists_lame {C : Lin4 E} (hC : C.IsIsotropic) (hd : 2 ≤ finrank ℝ E) :
    ∃ lam mu : ℝ, ∀ A ∈ Sym E, C A = isotropic lam mu A := by
  let b := stdOrthonormalBasis ℝ E
  let e₀ := b ⟨0, by omega⟩
  let f₀ := b ⟨1, by omega⟩
  have he₀ : ‖e₀‖ = 1 := b.orthonormal.1 _
  have hf₀ : ‖f₀‖ = 1 := b.orthonormal.1 _
  have hf₀e : ⟪f₀, e₀⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
  set α := ⟪f₀, C (e₀ ⊗ e₀) f₀⟫_ℝ
  set β := ⟪e₀, C (e₀ ⊗ e₀) e₀⟫_ℝ - α
  have h0 : C (e₀ ⊗ e₀) = α • (1 : Lin E) + β • (e₀ ⊗ e₀) := apply_dyad_self_eq hC he₀ hf₀ hf₀e
  refine ⟨α, β / 2, fun A hA => ?_⟩
  have hdyad : ∀ i, C (eigenbasis hA i ⊗ eigenbasis hA i) =
      α • (1 : Lin E) + β • (eigenbasis hA i ⊗ eigenbasis hA i) := fun i =>
    hC.apply_dyad_self_of he₀ h0 ((eigenbasis hA).orthonormal.1 i)
  rw [isotropic_apply, sym_eq_self_of_mem hA, tr_eq_sum_eigenvalues hA]
  set lam := eigenvalues hA
  set eb := eigenbasis hA
  have hspec : A = ∑ i, lam i • (eb i ⊗ eb i) := spectral_decomposition hA
  calc C A = ∑ i, lam i • C (eb i ⊗ eb i) := by
        conv_lhs => rw [hspec]
        simp only [map_sum, map_smul]
    _ = ∑ i, lam i • (α • (1 : Lin E) + β • (eb i ⊗ eb i)) := by simp only [hdyad, eb]
    _ = (α * ∑ i, lam i) • (1 : Lin E) + β • ∑ i, lam i • (eb i ⊗ eb i) := by
        simp only [smul_add, Finset.sum_add_distrib, smul_smul, Finset.mul_sum, Finset.sum_smul,
          Finset.smul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring_nf
    _ = (α * ∑ i, lam i) • (1 : Lin E) + (2 * (β / 2)) • A := by
        rw [← hspec]; ring_nf

end Lin4

section Examples

open Lin4

/-- In `ℝ³`, isotropic fourth-order tensors are exactly the Lamé tensors on symmetric
arguments. -/
example (C : Lin4 (EuclideanSpace ℝ (Fin 3))) (hC : C.IsIsotropic) :
    ∃ lam mu : ℝ, ∀ A ∈ Sym (EuclideanSpace ℝ (Fin 3)), C A = isotropic lam mu A :=
  hC.exists_lame (by simp)

end Examples

end ContinuumMechanics
