import Mathlib.LinearAlgebra.Lagrange
import ContinuumMechanics.Tensor.Isotropic4
import ContinuumMechanics.Tensor.Invariants

/-!
# The Rivlin–Ericksen representation theorem

A tensor function `G : Sym → Sym` is **isotropic** if `G(Q A Qᵀ) = Q G(A) Qᵀ` for every orthogonal
`Q`. The **Rivlin–Ericksen theorem** states that then, in three dimensions,

`G(A) = φ₀ I + φ₁ A + φ₂ A²`

for scalars `φₖ` depending on `A` ([Gurtin1981], §37; [TruesdellNoll1965], §12).

The proof works in any dimension and needs only reflections `R_e = I - 2 e ⊗ e`:

1. If `e` is a unit eigenvector of `A`, then `R_e` commutes with `A`, so isotropy gives
   `R_e G(A) = G(A) R_e`, which forces `G(A) e ∥ e`: **eigenvectors of `A` are eigenvectors of
   `G(A)`**.
2. If `e ⊥ f` are eigenvectors of `A` for the same eigenvalue, so is `e + f`; hence `G(A)` has the
   same eigenvalue on `e` and `f`.
3. Lagrange interpolation over the eigenvalues of `A` then gives a polynomial `p` with
   `G(A) = p(A)`.
4. In 3D, Cayley–Hamilton reduces `p(A)` to `φ₀ I + φ₁ A + φ₂ A²`.

## Main results

* `Lin.IsIsotropicFun`: isotropy of a tensor function.
* `Lin.IsIsotropicFun.exists_polynomial`: `G(A) = p(A)` (any dimension).
* `Lin.IsIsotropicFun.rivlinEricksen`: `G(A) = φ₀ I + φ₁ A + φ₂ A²` (`d = 3`).

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §37.
* [TruesdellNoll1965] C. Truesdell, W. Noll, *The Non-Linear Field Theories of Mechanics*, §12.
-/

open Module Polynomial
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- An **isotropic tensor function**: `G(Q A Qᵀ) = Q G(A) Qᵀ` for all orthogonal `Q` and symmetric
`A`. [Gurtin1981], §37. -/
def IsIsotropicFun (G : Lin E → Lin E) : Prop :=
  ∀ Q ∈ Orth E, ∀ A ∈ Sym E, G (Q * A * Qᵀ) = Q * G A * Qᵀ

omit [FiniteDimensional ℝ E] in
/-- `p(A) v = p(λ) v` for an eigenvector `v` of `A`. -/
theorem aeval_apply_of_eigen {A : Lin E} {v : E} {lam : ℝ} (hv : A v = lam • v) (p : ℝ[X]) :
    aeval A p v = p.eval lam • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a =>
    have hpow : ∀ k : ℕ, (A ^ k) v = lam ^ k • v := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_apply, ih, map_smul, hv, smul_smul, pow_succ']
        congr 1; ring
    simp [hpow, smul_smul, mul_comm]

/-- A reflection through an eigenvector of a symmetric tensor commutes with it. -/
theorem reflection_commute {A : Lin E} (hA : A ∈ Sym E) {e : E} {lam : ℝ} (he : A e = lam • e) :
    reflection e * A = A * reflection e := by
  have hAt : Aᵀ = A := mem_sym_iff.mp hA
  ext v
  have h : ⟪e, A v⟫_ℝ = lam * ⟪e, v⟫_ℝ := by
    rw [← inner_transpose_left, hAt, he, real_inner_smul_left]
  simp only [mul_apply, reflection_apply, map_sub, map_smul, he, h, smul_smul]
  ring_nf

omit [FiniteDimensional ℝ E] in
/-- If `B` commutes with `R_e` (`e` a unit vector), then `e` is an eigenvector of `B`. -/
theorem apply_eq_of_commute_reflection {B : Lin E} {e : E} (he : ‖e‖ = 1)
    (h : reflection e * B = B * reflection e) : B e = ⟪e, B e⟫_ℝ • e := by
  have h1 : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have := congrArg (fun T : Lin E => T e) h
  simp only [mul_apply, reflection_apply, h1, map_sub, map_smul] at this
  have h2 : B e - (2 * ⟪e, B e⟫_ℝ) • e = -(B e) := by rw [this]; module
  have h3 : (2 : ℝ) • B e = (2 * ⟪e, B e⟫_ℝ) • e := by
    rw [two_smul]; linear_combination (norm := module) h2
  calc B e = (2⁻¹ : ℝ) • ((2 : ℝ) • B e) := by rw [smul_smul]; norm_num
    _ = ⟪e, B e⟫_ℝ • e := by rw [h3, smul_smul]; congr 1; ring

namespace IsIsotropicFun

variable {G : Lin E → Lin E} (hG : IsIsotropicFun G) {A : Lin E} (hA : A ∈ Sym E)
include hG hA

/-- `G(A)` commutes with reflections through eigenvectors of `A`. -/
theorem commute_reflection {e : E} (he : ‖e‖ = 1) {lam : ℝ} (hev : A e = lam • e) :
    reflection e * G A = G A * reflection e := by
  have hR := reflection_mem_orth he
  have hc := reflection_commute hA hev
  have hRR := reflection_mul_self he
  have hconj : reflection e * A * (reflection e)ᵀ = A := by
    rw [transpose_reflection, hc, mul_assoc, hRR, mul_one]
  have := hG _ hR A hA
  rw [hconj, transpose_reflection] at this
  calc reflection e * G A = reflection e * (reflection e * G A * reflection e) := by
        rw [← this]
    _ = G A * reflection e := by
        rw [← mul_assoc, ← mul_assoc, hRR, one_mul]

/-- **Eigenvectors of `A` are eigenvectors of `G(A)`.** -/
theorem apply_eigen {e : E} (he : ‖e‖ = 1) {lam : ℝ} (hev : A e = lam • e) :
    G A e = ⟪e, G A e⟫_ℝ • e :=
  apply_eq_of_commute_reflection he (hG.commute_reflection hA he hev)

/-- `G(A)` has a single eigenvalue on each eigenspace of `A`. -/
theorem inner_eigen_eq {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) {lam : ℝ}
    (hev : A e = lam • e) (hfv : A f = lam • f) : ⟪e, G A e⟫_ℝ = ⟪f, G A f⟫_ℝ := by
  set g := ‖e + f‖⁻¹ • (e + f)
  have hne : e + f ≠ 0 := fun h => by
    have : ⟪e, e + f⟫_ℝ = 1 := by
      rw [inner_add_right, hef, add_zero, real_inner_self_eq_norm_sq, he, one_pow]
    rw [h, inner_zero_right] at this
    exact zero_ne_one this
  have hg : ‖g‖ = 1 := norm_smul_inv_norm hne
  have hgv : A g = lam • g := by
    simp only [g, map_smul, map_add, hev, hfv, smul_add, smul_comm lam]
  have key := hG.apply_eigen hA hg hgv
  set μ := ⟪g, G A g⟫_ℝ
  have hk : ‖e + f‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 hne)
  -- `G(A)(e + f) = μ (e + f)`
  have hsum : G A e + G A f = μ • (e + f) := by
    have h := key
    simp only [g, map_smul] at h
    rw [smul_comm μ] at h
    rw [← map_add]
    exact smul_right_injective E hk h
  have h1 : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have h2 : ⟪f, f⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hf, one_pow]
  have hfe : ⟪f, e⟫_ℝ = 0 := by rw [real_inner_comm, hef]
  have ee := hG.apply_eigen hA he hev
  have ff := hG.apply_eigen hA hf hfv
  set a := ⟪e, G A e⟫_ℝ
  set c := ⟪f, G A f⟫_ℝ
  rw [ee, ff] at hsum
  have i1 := congrArg (fun v => ⟪e, v⟫_ℝ) hsum
  have i2 := congrArg (fun v => ⟪f, v⟫_ℝ) hsum
  simp only [inner_add_right, inner_smul_right, h1, h2, hef, hfe, mul_one, mul_zero, add_zero,
    zero_add] at i1 i2
  linarith

/-- **`G(A)` is a polynomial in `A`** (any dimension). -/
theorem exists_polynomial : ∃ p : ℝ[X], G A = aeval A p := by
  set b := eigenbasis hA
  set lam := eigenvalues hA
  set μ : Fin (finrank ℝ E) → ℝ := fun i => ⟪b i, G A (b i)⟫_ℝ
  have hμ : ∀ i j, lam i = lam j → μ i = μ j := fun i j hij => by
    rcases eq_or_ne i j with rfl | hne
    · rfl
    · refine hG.inner_eigen_eq hA (b.orthonormal.1 i) (b.orthonormal.1 j)
        (b.orthonormal.2 hne) (apply_eigenbasis hA i) ?_
      rw [apply_eigenbasis hA j, show eigenvalues hA i = eigenvalues hA j from hij]
  classical
  set T := Finset.image lam Finset.univ
  let r : ℝ → ℝ := fun t => if h : ∃ i, lam i = t then μ h.choose else 0
  refine ⟨Lagrange.interpolate T id r, ?_⟩
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [aeval_apply_of_eigen (apply_eigenbasis hA j)]
  have hT : lam j ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have := Lagrange.eval_interpolate_at_node (s := T) (v := id) r (Set.injOn_id _) hT
  simp only [id] at this
  rw [this, hG.apply_eigen hA (b.orthonormal.1 j) (apply_eigenbasis hA j)]
  have hex : ∃ i, lam i = lam j := ⟨j, rfl⟩
  simp only [r, hex, dite_true]
  have key : ∀ h : ∃ i, lam i = lam j, μ h.choose = μ j := fun h => hμ _ _ h.choose_spec
  rw [key]

/-- **Rivlin–Ericksen representation theorem** (3D): `G(A) = φ₀ I + φ₁ A + φ₂ A²`.
[Gurtin1981], §37. -/
theorem rivlinEricksen [Fact (finrank ℝ E = 3)] :
    ∃ φ₀ φ₁ φ₂ : ℝ, G A = φ₀ • (1 : Lin E) + φ₁ • A + φ₂ • (A * A) := by
  obtain ⟨p₀, hp₀⟩ := hG.exists_polynomial hA
  rw [hp₀]
  -- `span {I, A, A²}` contains all powers of `A` (Cayley–Hamilton) and is a subspace
  let P : Lin E → Prop := fun X => ∃ a b c : ℝ, X = a • (1 : Lin E) + b • A + c • (A * A)
  have hadd : ∀ X Y, P X → P Y → P (X + Y) := by
    rintro X Y ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', by module⟩
  have hsmul : ∀ (r : ℝ) X, P X → P (r • X) := by
    rintro r X ⟨a, b, c, rfl⟩
    exact ⟨r * a, r * b, r * c, by module⟩
  have hch := cayley_hamilton A
  have hpow : ∀ n : ℕ, P (A ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, 0, by simp⟩
    | succ n ih =>
      obtain ⟨a, b, c, h⟩ := ih
      refine ⟨c * I₃ A, a - c * I₂ A, b + c * I₁ A, ?_⟩
      have h3 : A * A * A = I₁ A • (A * A) - I₂ A • A + I₃ A • (1 : Lin E) := by
        rw [← sub_eq_zero, ← hch]; abel
      rw [pow_succ, h, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul,
        h3]
      module
  have : ∀ p : ℝ[X], P (aeval A p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
    | monomial n a =>
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact hsmul a _ (hpow n)
  exact this p₀

end IsIsotropicFun

/-- Example: `A ↦ A²` is an isotropic tensor function. -/
example : IsIsotropicFun (fun A : Lin E => A * A) := fun Q hQ A _ => by
  have h := transpose_mul_self_of_mem_orth hQ
  calc Q * A * Qᵀ * (Q * A * Qᵀ) = Q * A * (Qᵀ * Q) * A * Qᵀ := by simp only [mul_assoc]
    _ = Q * (A * A) * Qᵀ := by rw [h, mul_one, mul_assoc Q A A]

end Lin

end ContinuumMechanics
