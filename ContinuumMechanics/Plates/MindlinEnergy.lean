import ContinuumMechanics.Plates.Energy

/-!
# Mindlin–Reissner plate energy: strong ⇔ stationary

A **Mindlin–Reissner** plate has a deflection `w` and rotations `φ = (φᵢ)`, with bending rigidity
`D`, Poisson ratio `ν` and shear stiffness `S`. Writing `div φ = Σ ∂ᵢφᵢ`,
`εᵢⱼ(φ) = (∂ⱼφᵢ + ∂ᵢφⱼ)/2` and `γᵢ = ∂ᵢw + φᵢ` (transverse shear strains), its energy bilinear
form is ([Reddy2007], §10.2)

`a((w, φ), (v, ψ)) = D ∫ ν div φ div ψ + (1 - ν) ε(φ) : ε(ψ) + S ∫ γ(w, φ) · γ(v, ψ)`,

which for `n = 2` is the classical density
`D/2 ((φ₁,₁)² + (φ₂,₂)² + 2ν φ₁,₁ φ₂,₂ + (1 - ν)/2 (φ₁,₂ + φ₂,₁)²) + S/2 |∇w + φ|²`.

* **Integration by parts** (`form_eq`): for compactly supported test fields,
  `a((w, φ), (v, ψ)) = ∫ R_w v + Σᵢ ∫ Rᵢ ψᵢ` with the residuals
  `R_w = -S div γ = -S (Δw + div φ)` (`resW_eq`) and
  `Rᵢ = -D (ν ∂ᵢ div φ + (1 - ν) Σⱼ ∂ⱼ εᵢⱼ(φ)) + S γᵢ`.
* **Strong ⇔ stationary** (`isStationary_iff`): `a((w, φ), (v, ψ)) = ∫ q v` for all test fields
  supported in an open set `U` iff `R_w = q` and `Rᵢ = 0` in `U`: the Mindlin–Reissner
  equilibrium equations of `Plates/MindlinReissner` (for `n = 2`,
  `ν ∂₁ div φ + (1 - ν) Σⱼ ∂ⱼ ε₁ⱼ = φ₁,₁₁ + (1 - ν)/2 φ₁,₂₂ + (1 + ν)/2 φ₂,₁₂`).

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §10.2.
* [Mindlin1951] R. D. Mindlin, *Influence of rotatory inertia and shear on flexural motions of
  isotropic elastic plates*, J. Appl. Mech. 18 (1951).
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Plates.MindlinEnergy

open Korn

variable {n : ℕ}

variable (D ν S : ℝ) (w v : (Fin n → ℝ) → ℝ) (φ ψ : Fin n → (Fin n → ℝ) → ℝ)

/-- The transverse shear strain `γᵢ = ∂ᵢw + φᵢ`. -/
def shear (i : Fin n) (x : Fin n → ℝ) : ℝ := pd w i x + φ i x

/-- The **Mindlin–Reissner bilinear form**. -/
def form : ℝ :=
  D * (∫ x, ν * (div φ x * div ψ x) + (1 - ν) * ∑ i, ∑ j, strain φ i j x * strain ψ i j x) +
    S * ∫ x, ∑ i, shear w φ i x * shear v ψ i x

/-- The residual of the transverse equilibrium equation, `-S div γ`. -/
def resW (x : Fin n → ℝ) : ℝ := -S * ∑ i, pd (shear w φ i) i x

/-- The residual of the `i`-th moment equilibrium equation,
`-D (ν ∂ᵢ div φ + (1 - ν) Σⱼ ∂ⱼ εᵢⱼ(φ)) + S γᵢ`. -/
def resPhi (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  -D * (ν * pd (div φ) i x + (1 - ν) * ∑ j, pd (strain φ i j) j x) + S * shear w φ i x

/-- `(w, φ)` is **stationary** with load `q` in `U`: `a((w, φ), (v, ψ)) = ∫ q v` for all smooth
test fields compactly supported in `U`. -/
def IsStationary (q : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) : Prop :=
  ∀ (v : (Fin n → ℝ) → ℝ) (ψ : Fin n → (Fin n → ℝ) → ℝ),
    ContDiff ℝ ∞ v → HasCompactSupport v → tsupport v ⊆ U →
    (∀ i, ContDiff ℝ ∞ (ψ i)) → (∀ i, HasCompactSupport (ψ i)) → (∀ i, tsupport (ψ i) ⊆ U) →
    form D ν S w v φ ψ = ∫ x, q x * v x

variable {D ν S w v φ ψ}

/-- The Mindlin–Reissner energy is nonnegative for `D, S ≥ 0` and `0 ≤ ν ≤ 1`. -/
theorem form_self_nonneg (hD : 0 ≤ D) (hS : 0 ≤ S) (hν₀ : 0 ≤ ν) (hν₁ : ν ≤ 1) :
    0 ≤ form D ν S w w φ φ := by
  unfold form
  refine add_nonneg (mul_nonneg hD (integral_nonneg fun x => ?_))
    (mul_nonneg hS (integral_nonneg fun x => Finset.sum_nonneg fun i _ => mul_self_nonneg _))
  exact add_nonneg (mul_nonneg hν₀ (mul_self_nonneg _)) (mul_nonneg (by linarith)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _))

section Regularity

variable (hw : ContDiff ℝ 2 w) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
include hw hφ

theorem contDiff_shear (i : Fin n) : ContDiff ℝ 1 (shear w φ i) :=
  (contDiff_pd hw i).add ((hφ i).of_le (by norm_num))

theorem continuous_resW : Continuous (resW S w φ) :=
  continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_pd (contDiff_shear hw hφ i) i)

theorem continuous_resPhi (i : Fin n) : Continuous (resPhi D ν S w φ i) :=
  (continuous_const.mul ((continuous_const.mul (continuous_pd (contDiff_div hφ) i)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_pd (contDiff_strain hφ i j) j)))).add
    (continuous_const.mul (contDiff_shear hw hφ i).continuous)

/-- `R_w = -S (Δw + div φ)`. -/
theorem resW_eq : resW S w φ = fun x => -S * (lap w x + div φ x) := by
  funext x
  have hd : ∀ i, Differentiable ℝ (pd w i) := fun i =>
    (contDiff_pd hw i).differentiable one_ne_zero
  have hp : ∀ i, Differentiable ℝ (φ i) := fun i => (hφ i).differentiable (by norm_num)
  simp only [resW, lap, div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change pd (pd w i + φ i) i x = _
  rw [pd_add (hd i) (hp i)]
  rfl

end Regularity

section Identity

variable (hw : ContDiff ℝ 2 w) (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hv : ContDiff ℝ 1 v)
  (hvc : HasCompactSupport v) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
include hw hφ hv hvc hψ hψc

theorem integral_shear_mul_shear :
    ∫ x, ∑ i, shear w φ i x * shear v ψ i x =
      -(∫ x, (∑ i, pd (shear w φ i) i x) * v x) + ∑ i, ∫ x, shear w φ i x * ψ i x := by
  have cg := fun i => (contDiff_shear hw hφ i).continuous
  have I1 : ∀ i, Integrable fun x => shear w φ i x * pd v i x := fun i =>
    integrable_mul_cs (cg i) (continuous_pd hv i) (hasCompactSupport_pd hvc i)
  have I2 : ∀ i, Integrable fun x => shear w φ i x * ψ i x := fun i =>
    integrable_mul_cs (cg i) (hψ i).continuous (hψc i)
  have e : ∀ x, ∑ i, shear w φ i x * shear v ψ i x =
      ∑ i, shear w φ i x * pd v i x + ∑ i, shear w φ i x * ψ i x := fun x => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [shear]; ring
  simp_rw [e]
  rw [integral_add (integrable_finsetSum _ fun i _ => I1 i)
      (integrable_finsetSum _ fun i _ => I2 i),
    integral_finsetSum _ fun i _ => I1 i, integral_finsetSum _ fun i _ => I2 i]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_mul_cs (continuous_pd (contDiff_shear hw hφ i) i)
    hv.continuous hvc, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => integral_mul_pd' (contDiff_shear hw hφ i) hv hvc i

/-- **Integration by parts of the Mindlin–Reissner form**:
`a((w, φ), (v, ψ)) = ∫ R_w v + Σᵢ ∫ Rᵢ ψᵢ`. -/
theorem form_eq :
    form D ν S w v φ ψ =
      (∫ x, resW S w φ x * v x) + ∑ i, ∫ x, resPhi D ν S w φ i x * ψ i x := by
  have iA := integrable_div_mul_div hφ hψ hψc
  have iB := integrable_strain_mul_strain hφ hψ hψc
  have cv := hv.continuous
  have cψ := fun i => (hψ i).continuous
  have hRW : ∫ x, resW S w φ x * v x = -S * ∫ x, (∑ i, pd (shear w φ i) i x) * v x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [resW]; ring)
  have hRP : ∀ i, ∫ x, resPhi D ν S w φ i x * ψ i x =
      -D * ν * (∫ x, pd (div φ) i x * ψ i x) +
        -D * (1 - ν) * (∫ x, (∑ j, pd (strain φ i j) j x) * ψ i x) +
          S * ∫ x, shear w φ i x * ψ i x := fun i => by
    have iP : Integrable fun x => pd (div φ) i x * ψ i x :=
      integrable_mul_cs (continuous_pd (contDiff_div hφ) i) (cψ i) (hψc i)
    have iQ : Integrable fun x => (∑ j, pd (strain φ i j) j x) * ψ i x :=
      integrable_mul_cs (continuous_finsetSum _ fun j _ => continuous_pd (contDiff_strain hφ i j) j)
        (cψ i) (hψc i)
    have iR : Integrable fun x => shear w φ i x * ψ i x :=
      integrable_mul_cs (contDiff_shear hw hφ i).continuous (cψ i) (hψc i)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iP.const_mul _) (iQ.const_mul _), ← integral_add _ (iR.const_mul _)]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [resPhi]; ring)
    · exact (iP.const_mul _).add (iQ.const_mul _)
  rw [form, integral_add (iA.const_mul ν) (iB.const_mul (1 - ν)), integral_const_mul,
    integral_const_mul, integral_div_mul_div hφ hψ hψc, integral_strain_mul_strain hφ hψ hψc,
    integral_shear_mul_shear hw hφ hv hvc hψ hψc, hRW, Finset.sum_congr rfl fun i _ => hRP i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Identity

/-- **Strong ⇔ stationary** for Mindlin–Reissner plates: `(w, φ)` is stationary in the open set
`U` iff it satisfies the equilibrium equations `-S div γ = q` and
`-D (ν ∂ᵢ div φ + (1 - ν) Σⱼ ∂ⱼ εᵢⱼ(φ)) + S γᵢ = 0` there. -/
theorem isStationary_iff {q : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hw : ContDiff ℝ 2 w)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) (hq : Continuous q) (hU : IsOpen U) :
    IsStationary D ν S w φ q U ↔
      (∀ x ∈ U, resW S w φ x = q x) ∧ ∀ i, ∀ x ∈ U, resPhi D ν S w φ i x = 0 := by
  have h1 : ∀ {g : (Fin n → ℝ) → ℝ}, ContDiff ℝ ∞ g → ContDiff ℝ 1 g := fun hg => hg.of_le (by simp)
  constructor
  · intro h
    refine ⟨fun x hx => sub_eq_zero.mp (eq_zero_on_of_integral
      ((continuous_resW hw hφ).sub hq) hU (fun g hg hgc hgU => ?_) x hx),
      fun i x hx => eq_zero_on_of_integral (continuous_resPhi hw hφ i) hU
        (fun g hg hgc hgU => ?_) x hx⟩
    · -- test with `v = g`, `ψ = 0`
      have e := h g 0 hg hgc hgU (fun _ => contDiff_zero_fun) (fun _ => HasCompactSupport.zero)
        (fun _ => by simp)
      rw [form_eq (ψ := 0) hw hφ (h1 hg) hgc (fun _ => contDiff_zero_fun)
        (fun _ => HasCompactSupport.zero)] at e
      simp only [Pi.zero_apply, mul_zero, integral_zero, Finset.sum_const_zero, add_zero] at e
      have i1 := integrable_mul_cs (continuous_resW (S := S) hw hφ) (h1 hg).continuous hgc
      have i2 := integrable_mul_cs hq (h1 hg).continuous hgc
      calc ∫ x, g x * (resW S w φ - q) x = ∫ x, (resW S w φ x * g x - q x * g x) :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by
              simp only [Pi.sub_apply]; ring)
        _ = 0 := by rw [integral_sub i1 i2, e, sub_self]
    · -- test with `v = 0`, `ψ = gδᵢ`
      set ψ : Fin n → (Fin n → ℝ) → ℝ := fun k => if k = i then g else 0 with hψ
      have cψ : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k => by
        by_cases hk : k = i
        · simp [ψ, hk, hg]
        · simp only [ψ, hk, ite_false]
          exact contDiff_zero_fun
      have sψ : ∀ k, HasCompactSupport (ψ k) := fun k => by
        by_cases hk : k = i <;> simp [ψ, hk, hgc, HasCompactSupport.zero]
      have tψ : ∀ k, tsupport (ψ k) ⊆ U := fun k => by
        by_cases hk : k = i <;> simp [ψ, hk, hgU]
      have e := h 0 ψ contDiff_zero_fun HasCompactSupport.zero (by simp) cψ sψ tψ
      rw [form_eq (v := 0) hw hφ contDiff_zero_fun HasCompactSupport.zero (fun k => h1 (cψ k)) sψ]
        at e
      simp only [Pi.zero_apply, mul_zero, integral_zero, zero_add] at e
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [ψ, hk]) (by simp)] at e
      simp only [ψ, ite_true] at e
      simpa only [mul_comm (g _)] using e
  · rintro ⟨hW, hP⟩ v ψ hv hvc hvU hψ hψc hψU
    rw [form_eq hw hφ (h1 hv) hvc (fun k => h1 (hψ k)) hψc, integral_mul_congr_on hvU hW,
      Finset.sum_eq_zero fun i _ => by
        rw [integral_mul_congr_on (hψU i) (hP i)]
        simp, add_zero]

end ContinuumMechanics.Plates.MindlinEnergy
