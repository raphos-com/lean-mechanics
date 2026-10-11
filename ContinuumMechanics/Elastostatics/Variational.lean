import ContinuumMechanics.Elastostatics.Korn
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Variational calculus for compactly supported fields

Tools shared by the variational formulations of linear elasticity and plate theories, for fields
on `ℝⁿ` and the partial derivatives `Korn.pd`:

* integration by parts against a compactly supported factor (`integral_mul_pd'`), linearity of
  `pd`, compact supports and integrability of products;
* the Laplacian `lap`, the strain `strain φ i j = (∂ⱼφᵢ + ∂ᵢφⱼ)/2` of a vector field and the
  identities `∫ div φ div ψ = -Σᵢ ∫ ∂ᵢ(div φ) ψᵢ` (`integral_div_mul_div`) and
  `∫ ε(φ) : ε(ψ) = -Σᵢ ∫ (Σⱼ ∂ⱼεᵢⱼ(φ)) ψᵢ` (`integral_strain_mul_strain`);
* the **fundamental lemma of the calculus of variations** on open sets
  (`eq_zero_on_of_integral`), from Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Korn

variable {n : ℕ} {f g w v : (Fin n → ℝ) → ℝ}

theorem pd_add (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    pd (f + g) j = pd f j + pd g j := by
  funext x
  simp [pd, fderiv_add (hf x) (hg x)]

theorem contDiff_pd_of_le {k m : WithTop ℕ∞} (hf : ContDiff ℝ m f) (hk : k + 1 ≤ m) (j : Fin n) :
    ContDiff ℝ k (pd f j) :=
  (hf.fderiv_right hk).clm_apply contDiff_const

/-- The Laplacian `Δf = Σᵢ ∂ᵢ∂ᵢf`. -/
def lap (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, pd (pd f i) i x

theorem continuous_pd_pd (hf : ContDiff ℝ 2 f) (i j : Fin n) : Continuous (pd (pd f i) j) :=
  continuous_pd (contDiff_pd hf i) j

theorem continuous_lap (hf : ContDiff ℝ 2 f) : Continuous (lap f) :=
  continuous_finsetSum _ fun i _ => continuous_pd_pd hf i i

theorem hasCompactSupport_pd_pd (hf : HasCompactSupport f) (i j : Fin n) :
    HasCompactSupport (pd (pd f i) j) :=
  hasCompactSupport_pd (hasCompactSupport_pd hf i) j

theorem hasCompactSupport_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℝ) → ℝ)
    (h : ∀ i ∈ s, HasCompactSupport (F i)) : HasCompactSupport (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasCompactSupport_lap (hf : HasCompactSupport f) : HasCompactSupport (lap f) :=
  hasCompactSupport_sum _ _ fun i _ => hasCompactSupport_pd_pd hf i i

/-- **Fundamental lemma of the calculus of variations**: a continuous `F` with `∫ g F = 0` for
every smooth `g` compactly supported in the open set `U` vanishes on `U`. -/
theorem eq_zero_on_of_integral {U : Set (Fin n → ℝ)} {F : (Fin n → ℝ) → ℝ} (hF : Continuous F)
    (hU : IsOpen U)
    (h : ∀ g : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x * F x = 0) :
    ∀ x ∈ U, F x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := F) (μ := volume)
    (hF.locallyIntegrable.locallyIntegrableOn U) fun g hg hgc hgU => by
      simpa only [smul_eq_mul] using h g hg hgc hgU
  have hS : IsOpen (U ∩ {x | F x ≠ 0}) := hU.inter (isOpen_ne_fun hF continuous_const)
  have h0 : volume (U ∩ {x | F x ≠ 0}) = 0 := by
    rw [ae_iff] at hae
    convert hae using 2
    ext x
    simp
  have he := (hS.measure_eq_zero_iff volume).mp h0
  intro x hx
  by_contra hne
  have : x ∈ U ∩ {x | F x ≠ 0} := ⟨hx, hne⟩
  rw [he] at this
  exact this

/-- `∫ F g = ∫ G g` when `F = G` on `U ⊇ tsupport g`. -/
theorem integral_mul_congr_on {U : Set (Fin n → ℝ)} {F G g : (Fin n → ℝ) → ℝ}
    (hg : tsupport g ⊆ U)
    (h : ∀ x ∈ U, F x = G x) : ∫ x, F x * g x = ∫ x, G x * g x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ U
  · simp only [h x hx]
  · have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hg h')
    simp [this]

/-- **Integration by parts** with the compact support on the differentiated factor:
`∫ f ∂ⱼg = -∫ ∂ⱼf g`. -/
theorem integral_mul_pd' (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (j : Fin n) : ∫ x, f x * pd g j x = -∫ x, pd f j x * g x := by
  have cf := hf.continuous; have cg := hg.continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_pd hf j).mul cg).integrable_of_hasCompactSupport hgc.mul_left)
    ((cf.mul (continuous_pd hg j)).integrable_of_hasCompactSupport
      (hasCompactSupport_pd hgc j).mul_left)
    ((cf.mul cg).integrable_of_hasCompactSupport hgc.mul_left)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin n) :
    pd (fun x => ∑ i ∈ s, f i x) j = fun x => ∑ i ∈ s, pd (f i) j x := by
  funext x
  simp only [pd]
  rw [fderiv_fun_sum fun i _ => (hf i).differentiableAt, sum_apply]

theorem integrable_mul_cs {F G : (Fin n → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hGc : HasCompactSupport G) : Integrable fun x => F x * G x :=
  (hF.mul hG).integrable_of_hasCompactSupport hGc.mul_left

/-- `εᵢⱼ(φ) = (∂ⱼφᵢ + ∂ᵢφⱼ)/2`. -/
def strain (φ : Fin n → (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) : ℝ :=
  (pd (φ i) j x + pd (φ j) i x) / 2

/-- `Σᵢⱼ εᵢⱼ(φ) εᵢⱼ(ψ) = Σᵢⱼ εᵢⱼ(φ) ∂ⱼψᵢ`, by symmetry of `ε(φ)`. -/
theorem strain_contract (φ ψ : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, strain φ i j x * strain ψ i j x = ∑ i, ∑ j, strain φ i j x * pd (ψ i) j x := by
  have hs : ∀ i j, strain φ i j x = strain φ j i x := fun i j => by
    simp only [strain]; ring
  have h2 : ∑ i, ∑ j, strain φ i j x * pd (ψ j) i x = ∑ i, ∑ j, strain φ i j x * pd (ψ i) j x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs]
  have h : ∀ i j, strain φ i j x * strain ψ i j x =
      (strain φ i j x * pd (ψ i) j x + strain φ i j x * pd (ψ j) i x) / 2 := fun i j => by
    simp only [strain]; ring
  simp only [h, ← Finset.sum_div, Finset.sum_add_distrib, h2]
  ring

section Strain

variable {φ ψ : Fin n → (Fin n → ℝ) → ℝ}

theorem contDiff_div (hφ : ∀ i, ContDiff ℝ 2 (φ i)) : ContDiff ℝ 1 (div φ) :=
  ContDiff.sum fun i _ => contDiff_pd (hφ i) i

theorem contDiff_strain (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (i j : Fin n) :
    ContDiff ℝ 1 (strain φ i j) :=
  ((contDiff_pd (hφ i) j).add (contDiff_pd (hφ j) i)).div_const 2

variable (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
  (hψc : ∀ i, HasCompactSupport (ψ i))
include hφ hψ hψc

/-- `∫ div φ div ψ = -Σᵢ ∫ ∂ᵢ(div φ) ψᵢ` for compactly supported `ψ`. -/
theorem integral_div_mul_div :
    ∫ x, div φ x * div ψ x = -∑ i, ∫ x, pd (div φ) i x * ψ i x := by
  have cd := (contDiff_div hφ).continuous
  have e : ∀ x, div φ x * div ψ x = ∑ i, div φ x * pd (ψ i) i x := fun x => by
    change div φ x * ∑ i, pd (ψ i) i x = _
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_mul_cs cd (continuous_pd (hψ i) i)
    (hasCompactSupport_pd (hψc i) i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => integral_mul_pd' (contDiff_div hφ) (hψ i) (hψc i) i

/-- `∫ ε(φ) : ε(ψ) = -Σᵢ ∫ (Σⱼ ∂ⱼεᵢⱼ(φ)) ψᵢ` for compactly supported `ψ`. -/
theorem integral_strain_mul_strain :
    ∫ x, ∑ i, ∑ j, strain φ i j x * strain ψ i j x =
      -∑ i, ∫ x, (∑ j, pd (strain φ i j) j x) * ψ i x := by
  have cs := fun i j => (contDiff_strain hφ i j).continuous
  simp_rw [strain_contract]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_mul_cs (cs i j) (continuous_pd (hψ i) j) (hasCompactSupport_pd (hψc i) j),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    integrable_mul_cs (cs i j) (continuous_pd (hψ i) j) (hasCompactSupport_pd (hψc i) j)]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => integrable_mul_cs
    (continuous_pd (contDiff_strain hφ i j) j) (hψ i).continuous (hψc i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => integral_mul_pd' (contDiff_strain hφ i j) (hψ i) (hψc i) j

theorem integrable_strain_mul_strain :
    Integrable fun x => ∑ i, ∑ j, strain φ i j x * strain ψ i j x := by
  simp_rw [strain_contract]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_mul_cs (contDiff_strain hφ i j).continuous (continuous_pd (hψ i) j)
      (hasCompactSupport_pd (hψc i) j)

theorem integrable_div_mul_div : Integrable fun x => div φ x * div ψ x :=
  integrable_mul_cs (contDiff_div hφ).continuous
    (continuous_finsetSum _ fun i _ => continuous_pd (hψ i) i)
    (hasCompactSupport_sum _ _ fun i _ => hasCompactSupport_pd (hψc i) i)

end Strain

end ContinuumMechanics.Korn
