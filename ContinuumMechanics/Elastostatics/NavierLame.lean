import ContinuumMechanics.Elastostatics.Variational

/-!
# Isotropic linear elastostatics: Navier–Lamé equations ⇔ stationary energy

For a displacement `u : ℝⁿ → ℝⁿ` (components `uᵢ`) of an isotropic linear elastic body with Lamé
moduli `λ`, `μ`, the stress is `σ = λ (div u) I + 2μ ε(u)` and the strain energy bilinear form is

`a(u, v) = ∫ λ div u div v + 2μ ε(u) : ε(v)`.

* **Integration by parts** (`form_eq`): for compactly supported `v`,
  `a(u, v) = Σᵢ ∫ Rᵢ vᵢ` with `Rᵢ = -(div σ)ᵢ = -(λ ∂ᵢ div u + 2μ Σⱼ ∂ⱼεᵢⱼ(u))`.
* `res_eq`: `Rᵢ = -(μ Δuᵢ + (λ + μ) ∂ᵢ div u)`, using `2 Σⱼ ∂ⱼεᵢⱼ = Δuᵢ + ∂ᵢ div u`.
* **Strong ⇔ stationary** (`isStationary_iff`): `a(u, v) = ∫ b · v` for every smooth test field
  compactly supported in an open set `U` iff the **Navier–Lamé equations**
  `μ Δu + (λ + μ) ∇ div u + b = 0` hold in `U`.
* `form_self_nonneg`: `a(u, u) ≥ 0` for `μ ≥ 0`, `λ ≥ 0`.

This is the classical (smooth) counterpart of the weak formulation of `Elastostatics/Weak`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§23–25.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §§6.1–6.3.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.NavierLame

open Korn

variable {n : ℕ}

variable (lam μ : ℝ) (u v : Fin n → (Fin n → ℝ) → ℝ)

/-- The **strain energy bilinear form** `a(u, v) = ∫ λ div u div v + 2μ ε(u) : ε(v)`. -/
def form : ℝ :=
  ∫ x, lam * (div u x * div v x) + 2 * μ * ∑ i, ∑ j, strain u i j x * strain v i j x

/-- The residual `Rᵢ = -(λ ∂ᵢ div u + 2μ Σⱼ ∂ⱼεᵢⱼ(u)) = -(div σ)ᵢ`. -/
def res (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  -(lam * pd (div u) i x + 2 * μ * ∑ j, pd (strain u i j) j x)

/-- `u` is **stationary** with body force `b` in `U`: `a(u, v) = ∫ b · v` for all smooth test
fields `v` compactly supported in `U`. -/
def IsStationary (b : Fin n → (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) : Prop :=
  ∀ v : Fin n → (Fin n → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (v i)) → (∀ i, HasCompactSupport (v i)) →
    (∀ i, tsupport (v i) ⊆ U) → form lam μ u v = ∑ i, ∫ x, b i x * v i x

variable {lam μ u v}

/-- The strain energy is nonnegative for `λ, μ ≥ 0`. -/
theorem form_self_nonneg (hl : 0 ≤ lam) (hm : 0 ≤ μ) : 0 ≤ form lam μ u u :=
  integral_nonneg fun x => add_nonneg (mul_nonneg hl (mul_self_nonneg _))
    (mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_self_nonneg _))

theorem continuous_res (hu : ∀ i, ContDiff ℝ 2 (u i)) (i : Fin n) : Continuous (res lam μ u i) :=
  ((continuous_const.mul (continuous_pd (contDiff_div hu) i)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_pd (contDiff_strain hu i j) j))).neg

/-- `Rᵢ = -(μ Δuᵢ + (λ + μ) ∂ᵢ div u)`. -/
theorem res_eq (hu : ∀ i, ContDiff ℝ 3 (u i)) (i : Fin n) :
    res lam μ u i = fun x => -(μ * lap (u i) x + (lam + μ) * pd (div u) i x) := by
  have h2 : ∀ k, ContDiff ℝ 2 (u k) := fun k => (hu k).of_le (by norm_num)
  have d1 : ∀ k l, Differentiable ℝ (pd (u k) l) := fun k l =>
    (contDiff_pd (h2 k) l).differentiable one_ne_zero
  -- `∂ⱼεᵢⱼ = (∂ⱼ∂ⱼuᵢ + ∂ᵢ∂ⱼuⱼ)/2`
  have hs : ∀ j, pd (strain u i j) j =
      fun x => (pd (pd (u i) j) j x + pd (pd (u j) j) i x) / 2 := fun j => by
    have e : strain u i j = (2 : ℝ)⁻¹ • (pd (u i) j + pd (u j) i) := by
      funext x; simp only [strain, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    funext x
    rw [e]
    have hd : DifferentiableAt ℝ (pd (u i) j + pd (u j) i) x := ((d1 i j).add (d1 j i)) x
    have hsm : pd ((2 : ℝ)⁻¹ • (pd (u i) j + pd (u j) i)) j x =
        (2 : ℝ)⁻¹ * pd (pd (u i) j + pd (u j) i) j x := by
      simp only [pd]
      rw [fderiv_const_smul hd]
      rfl
    rw [hsm, pd_add (d1 i j) (d1 j i), Pi.add_apply, pd_pd_comm (h2 j) i j]
    ring
  have hdiv : pd (div u) i = fun x => ∑ j, pd (pd (u j) j) i x :=
    pd_sum _ (fun j => d1 j j) i
  funext x
  simp only [res, hs, hdiv, lap, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- **Integration by parts**: `a(u, v) = Σᵢ ∫ Rᵢ vᵢ` for compactly supported `v`. -/
theorem form_eq (hu : ∀ i, ContDiff ℝ 2 (u i)) (hv : ∀ i, ContDiff ℝ 1 (v i))
    (hvc : ∀ i, HasCompactSupport (v i)) :
    form lam μ u v = ∑ i, ∫ x, res lam μ u i x * v i x := by
  have iA := integrable_div_mul_div hu hv hvc
  have iB := integrable_strain_mul_strain hu hv hvc
  have hR : ∀ i, ∫ x, res lam μ u i x * v i x =
      -lam * (∫ x, pd (div u) i x * v i x) +
        -(2 * μ) * ∫ x, (∑ j, pd (strain u i j) j x) * v i x := fun i => by
    have iP : Integrable fun x => pd (div u) i x * v i x :=
      integrable_mul_cs (continuous_pd (contDiff_div hu) i) (hv i).continuous (hvc i)
    have iQ : Integrable fun x => (∑ j, pd (strain u i j) j x) * v i x :=
      integrable_mul_cs (continuous_finsetSum _ fun j _ => continuous_pd (contDiff_strain hu i j) j)
        (hv i).continuous (hvc i)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iP.const_mul _)
      (iQ.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [res]; ring)
  rw [form, integral_add (iA.const_mul lam) (iB.const_mul (2 * μ)), integral_const_mul,
    integral_const_mul, integral_div_mul_div hu hv hvc, integral_strain_mul_strain hu hv hvc,
    Finset.sum_congr rfl fun i _ => hR i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Strong ⇔ stationary**: `u` is stationary with body force `b` in the open set `U` iff it
satisfies `-(div σ) = b` there, i.e. (`res_eq`) the Navier–Lamé equations
`μ Δu + (λ + μ) ∇ div u + b = 0`. -/
theorem isStationary_iff {b : Fin n → (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (hb : ∀ i, Continuous (b i)) (hU : IsOpen U) :
    IsStationary lam μ u b U ↔ ∀ i, ∀ x ∈ U, res lam μ u i x = b i x := by
  have h1 : ∀ {g : (Fin n → ℝ) → ℝ}, ContDiff ℝ ∞ g → ContDiff ℝ 1 g := fun hg => hg.of_le (by simp)
  constructor
  · intro h i x hx
    refine sub_eq_zero.mp (eq_zero_on_of_integral ((continuous_res hu i).sub (hb i)) hU
      (fun g hg hgc hgU => ?_) x hx)
    -- test with `v = g eᵢ`
    set v : Fin n → (Fin n → ℝ) → ℝ := fun k => if k = i then g else 0 with hv
    have cv : ∀ k, ContDiff ℝ ∞ (v k) := fun k => by
      by_cases hk : k = i
      · simp [v, hk, hg]
      · simp only [v, hk, ite_false]
        exact contDiff_zero_fun
    have sv : ∀ k, HasCompactSupport (v k) := fun k => by
      by_cases hk : k = i <;> simp [v, hk, hgc, HasCompactSupport.zero]
    have tv : ∀ k, tsupport (v k) ⊆ U := fun k => by
      by_cases hk : k = i <;> simp [v, hk, hgU]
    have e := h v cv sv tv
    rw [form_eq hu (fun k => h1 (cv k)) sv, Finset.sum_eq_single i (fun k _ hk => by simp [v, hk])
      (by simp), Finset.sum_eq_single i (fun k _ hk => by simp [v, hk]) (by simp)] at e
    simp only [v, ite_true] at e
    have i1 := integrable_mul_cs (continuous_res (lam := lam) (μ := μ) hu i) (h1 hg).continuous hgc
    have i2 := integrable_mul_cs (hb i) (h1 hg).continuous hgc
    calc ∫ x, g x * (res lam μ u i - b i) x = ∫ x, (res lam μ u i x * g x - b i x * g x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [Pi.sub_apply]; ring)
      _ = 0 := by rw [integral_sub i1 i2, e, sub_self]
  · intro h v hv hvc hvU
    rw [form_eq hu (fun k => h1 (hv k)) hvc]
    exact Finset.sum_congr rfl fun i _ => integral_mul_congr_on (hvU i) (h i)

end ContinuumMechanics.NavierLame
