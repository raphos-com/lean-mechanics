import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Korn's first inequality for compactly supported fields

For a displacement field `u : ℝⁿ → ℝⁿ` of class `C²` with compact support, with
`∂ⱼuᵢ` its partial derivatives and `εᵢⱼ = (∂ⱼuᵢ + ∂ᵢuⱼ)/2` its strain,

`∫ |∇u|² + ∫ (div u)² = 2 ∫ |ε(u)|²`   (`korn_identity`),

hence **Korn's first inequality** `∫ |∇u|² ≤ 2 ∫ |ε(u)|²` (`korn_first`).

The proof integrates by parts twice (Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) and uses the symmetry of second derivatives:
`∫ ∂ⱼuᵢ ∂ᵢuⱼ = -∫ uᵢ ∂ⱼ∂ᵢuⱼ = -∫ uᵢ ∂ᵢ∂ⱼuⱼ = ∫ ∂ᵢuᵢ ∂ⱼuⱼ` (`integral_cross`).

This is the inequality behind the `KornSetting` hypothesis of `Elastostatics.Weak` for fields
vanishing on the whole boundary (`H¹₀`), obtained there by density; the density argument and the
Sobolev space `H¹₀(Ω; ℝⁿ)` are not available in Mathlib yet (see `GAPS.md`).

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.3.
* [Korn1909] A. Korn, *Über einige Ungleichungen, welche in der Theorie der elastischen und
  elektrischen Schwingungen eine Rolle spielen*, Bull. Int. Cracovie Akad. Umiejet (1909).
-/

open MeasureTheory

noncomputable section

namespace ContinuumMechanics.Korn

variable {n : ℕ}

/-- The partial derivative `∂ⱼ f`. -/
def pd (f : (Fin n → ℝ) → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ := fderiv ℝ f x (Pi.single j 1)

variable {f g : (Fin n → ℝ) → ℝ}

theorem continuous_pd (hf : ContDiff ℝ 1 f) (j : Fin n) : Continuous (pd f j) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasCompactSupport_pd (hf : HasCompactSupport f) (j : Fin n) :
    HasCompactSupport (pd f j) := by
  refine (hf.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  exact fun h => hx (by simp [pd, h])

theorem contDiff_pd (hf : ContDiff ℝ 2 f) (j : Fin n) : ContDiff ℝ 1 (pd f j) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- **Integration by parts**: `∫ f ∂ⱼg = -∫ ∂ⱼf g` for `C¹` functions with compact support. -/
theorem integral_mul_pd (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f)
    (j : Fin n) : ∫ x, f x * pd g j x = -∫ x, pd f j x * g x := by
  have cf := hf.continuous; have cg := hg.continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_pd hf j).mul cg).integrable_of_hasCompactSupport
      ((hasCompactSupport_pd hfc j).mul_right))
    ((cf.mul (continuous_pd hg j)).integrable_of_hasCompactSupport hfc.mul_right)
    ((cf.mul cg).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

/-- **Symmetry of second derivatives**: `∂ⱼ∂ᵢ f = ∂ᵢ∂ⱼ f` for `f` of class `C²`. -/
theorem pd_pd_comm (hf : ContDiff ℝ 2 f) (i j : Fin n) :
    pd (pd f i) j = pd (pd f j) i := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hs _ _

/-- `∫ ∂ⱼuᵢ ∂ᵢuⱼ = ∫ ∂ᵢuᵢ ∂ⱼuⱼ` for `C²` fields with compact support. -/
theorem integral_cross {ui uj : (Fin n → ℝ) → ℝ} (hi : ContDiff ℝ 2 ui) (hj : ContDiff ℝ 2 uj)
    (hic : HasCompactSupport ui) (i j : Fin n) :
    ∫ x, pd ui j x * pd uj i x = ∫ x, pd ui i x * pd uj j x := by
  have h1 := hi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  -- `∫ ∂ⱼuᵢ ∂ᵢuⱼ = -∫ uᵢ ∂ⱼ∂ᵢuⱼ`
  have e1 : ∫ x, pd ui j x * pd uj i x = -∫ x, ui x * pd (pd uj i) j x := by
    rw [integral_mul_pd h1 (contDiff_pd hj i) hic j, neg_neg]
  -- `∫ uᵢ ∂ᵢ∂ⱼuⱼ = -∫ ∂ᵢuᵢ ∂ⱼuⱼ`
  have e2 : ∫ x, ui x * pd (pd uj j) i x = -∫ x, pd ui i x * pd uj j x :=
    integral_mul_pd h1 (contDiff_pd hj j) hic i
  rw [e1, pd_pd_comm hj, e2, neg_neg]

/-- The squared norm of the gradient, `|∇u|² = Σᵢⱼ (∂ⱼuᵢ)²`. -/
def gradSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, pd (u i) j x ^ 2

/-- The squared norm of the strain, `|ε|² = Σᵢⱼ ((∂ⱼuᵢ + ∂ᵢuⱼ)/2)²`. -/
def strainSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ((pd (u i) j x + pd (u j) i x) / 2) ^ 2

/-- The divergence `div u = Σᵢ ∂ᵢuᵢ`. -/
def div (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, pd (u i) i x

variable {u : Fin n → (Fin n → ℝ) → ℝ}

/-- Pointwise: `2|ε|² = |∇u|² + ∇u : ∇uᵀ`. -/
theorem two_strainSq (x : Fin n → ℝ) :
    2 * strainSq u x = gradSq u x + ∑ i, ∑ j, pd (u i) j x * pd (u j) i x := by
  have h1 : 2 * strainSq u x = ∑ i, ∑ j, (pd (u i) j x ^ 2 / 2 + pd (u j) i x ^ 2 / 2 +
      pd (u i) j x * pd (u j) i x) := by
    rw [strainSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ i, ∑ j, pd (u i) j x ^ 2 / 2 = gradSq u x / 2 := by
    simp only [gradSq, Finset.sum_div]
  have h3 : ∑ i, ∑ j, pd (u j) i x ^ 2 / 2 = gradSq u x / 2 := by
    rw [Finset.sum_comm, h2]
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3]
  ring

/-- **Korn's identity** for compactly supported `C²` fields:
`∫ |∇u|² + ∫ (div u)² = 2 ∫ |ε(u)|²`. -/
theorem korn_identity (hu : ∀ i, ContDiff ℝ 2 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    (∫ x, gradSq u x) + ∫ x, div u x ^ 2 = 2 * ∫ x, strainSq u x := by
  have h1 : ∀ i, ContDiff ℝ 1 (u i) := fun i => (hu i).of_le (by norm_num)
  have cpd : ∀ i j, Continuous (pd (u i) j) := fun i j => continuous_pd (h1 i) j
  have spd : ∀ i j, HasCompactSupport (pd (u i) j) := fun i j => hasCompactSupport_pd (hc i) j
  have ipp : ∀ i j k l, Integrable (fun x => pd (u i) j x * pd (u k) l x) :=
    fun i j k l => ((cpd i j).mul (cpd k l)).integrable_of_hasCompactSupport
      (spd i j).mul_right
  have isq : ∀ i j, Integrable (fun x => pd (u i) j x ^ 2) := fun i j => by
    simpa [sq] using ipp i j i j
  -- `(div u)² = Σᵢⱼ ∂ᵢuᵢ ∂ⱼuⱼ`
  have hdiv : ∀ x, div u x ^ 2 = ∑ i, ∑ j, pd (u i) i x * pd (u j) j x := fun x => by
    rw [div, sq, Finset.sum_mul_sum]
  have e2 : ∫ x, strainSq u x = (∫ x, gradSq u x + ∑ i, ∑ j, pd (u i) j x * pd (u j) i x) / 2 := by
    rw [eq_div_iff (two_ne_zero), mul_comm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => two_strainSq x)
  have igrad : Integrable (gradSq u) := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => isq i j
  have icross : Integrable (fun x => ∑ i, ∑ j, pd (u i) j x * pd (u j) i x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i j j i
  rw [e2, integral_add igrad icross, mul_div_cancel₀ _ two_ne_zero]
  congr 1
  simp_rw [hdiv]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i i j j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i j j i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ipp i i j j,
    integral_finsetSum _ fun j _ => ipp i j j i]
  exact Finset.sum_congr rfl fun j _ => (integral_cross (hu i) (hu j) (hc i) i j).symm

/-- **Korn's first inequality** for compactly supported `C²` fields:
`∫ |∇u|² ≤ 2 ∫ |ε(u)|²`. -/
theorem korn_first (hu : ∀ i, ContDiff ℝ 2 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    ∫ x, gradSq u x ≤ 2 * ∫ x, strainSq u x := by
  rw [← korn_identity hu hc]
  have : 0 ≤ ∫ x, div u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  linarith

end ContinuumMechanics.Korn
