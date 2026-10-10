import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import ContinuumMechanics.Tensor.Contraction

/-!
# Divergence, the divergence theorem as a hypothesis, and local equilibrium

The **divergence** of a vector field is `div v = tr ∇v`; the divergence of a tensor field `σ` is
the vector field with `div σ · a = div (σᵀ a)` for every constant `a` ([Gurtin1981], §4).

Mathlib proves the divergence theorem only on boxes, so it enters here as a hypothesis on the
regions under consideration (`DivergenceRegion`; see `GAPS.md`). From it we derive the classical
**localisation**: if the forces on every small part of a body balance,
`∫_∂P σ n dA + ∫_P b dV = 0`, then the local equilibrium equation `div σ + b = 0` holds
pointwise ([Gurtin1981], §14; [Ciarlet1988], §2.2). (Dynamics only replaces `b` by `b - ρ a`.)

## Main definitions

* `vdiv v`, `tdiv σ`: divergence of vector and tensor fields.
* `DivergenceRegion E`: a region with a surface measure and an outer normal for which the
  divergence theorem holds (hypothesis structure).

## Main results

* `inner_tdiv`: `div σ · a = div (σᵀ a)`.
* `DivergenceRegion.integral_traction`: `∫_∂P σ n dA = ∫_P div σ dV`.
* `eq_zero_of_integral_regions`: localisation over small regions.
* `local_equilibrium`: integral equilibrium of all small parts ⇒ `div σ + b = 0`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§4, 14.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §2.2.
-/

open MeasureTheory Metric Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **divergence** of a vector field, `div v = tr ∇v`. [Gurtin1981], §4. -/
noncomputable def vdiv (v : E → E) (x : E) : ℝ := Lin.tr (fderiv ℝ v x)

/-- The **divergence** of a tensor field, characterised by `div σ · a = div (σᵀ a)`
(`inner_tdiv`). [Gurtin1981], §4. -/
noncomputable def tdiv (σ : E → Lin E) (x : E) : E :=
  ∑ i, vdiv (fun y => (σ y)ᵀ (stdOrthonormalBasis ℝ E i)) x • stdOrthonormalBasis ℝ E i

/-- `∇(σᵀ a) = (∇σ)ᵀ a`: the derivative of `y ↦ σ(y)ᵀ a`. -/
theorem fderiv_transpose_apply {σ : E → Lin E} {x : E} (hσ : DifferentiableAt ℝ σ x) (a : E) :
    fderiv ℝ (fun y => (σ y)ᵀ a) x =
      ((ContinuousLinearMap.apply ℝ E a).comp
        (starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap).comp (fderiv ℝ σ x) := by
  have h : (fun y => (σ y)ᵀ a) =
      ((ContinuousLinearMap.apply ℝ E a).comp
        (starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap) ∘ σ := by
    ext y; simp
  rw [h, fderiv_comp x (ContinuousLinearMap.differentiableAt _) hσ, ContinuousLinearMap.fderiv]

/-- `div σ · a = div (σᵀ a)`. [Gurtin1981], §4. -/
theorem inner_tdiv {σ : E → Lin E} {x : E} (hσ : DifferentiableAt ℝ σ x) (a : E) :
    ⟪tdiv σ x, a⟫_ℝ = vdiv (fun y => (σ y)ᵀ a) x := by
  set b := stdOrthonormalBasis ℝ E
  -- `a ↦ div (σᵀ a)` is linear
  let ℓ : E →ₗ[ℝ] ℝ :=
    { toFun := fun a => vdiv (fun y => (σ y)ᵀ a) x
      map_add' := fun a c => by
        change Lin.tr (fderiv ℝ (fun y => (σ y)ᵀ (a + c)) x) =
          Lin.tr (fderiv ℝ (fun y => (σ y)ᵀ a) x) + Lin.tr (fderiv ℝ (fun y => (σ y)ᵀ c) x)
        rw [fderiv_transpose_apply hσ, fderiv_transpose_apply hσ, fderiv_transpose_apply hσ,
          map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.add_comp, map_add]
      map_smul' := fun r a => by
        change Lin.tr (fderiv ℝ (fun y => (σ y)ᵀ (r • a)) x) =
          r * Lin.tr (fderiv ℝ (fun y => (σ y)ᵀ a) x)
        rw [fderiv_transpose_apply hσ, fderiv_transpose_apply hσ, map_smul,
          ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp, map_smul, smul_eq_mul] }
  have ha : a = ∑ i, ⟪b i, a⟫_ℝ • b i := (b.sum_repr' a).symm
  calc ⟪tdiv σ x, a⟫_ℝ = ∑ i, ℓ (b i) * ⟪b i, a⟫_ℝ := by
        simp only [tdiv, sum_inner, inner_smul_left, RCLike.conj_to_real]; rfl
    _ = ℓ (∑ i, ⟪b i, a⟫_ℝ • b i) := by
        rw [map_sum]; simp only [map_smul, smul_eq_mul, mul_comm]
    _ = vdiv (fun y => (σ y)ᵀ a) x := by rw [← ha]; rfl

/-- **Product rule**: `div (σᵀ (W y)) = div σ · W y + σ : W` for a constant tensor `W`. -/
theorem vdiv_transpose_apply_linear {σ : E → Lin E} {x : E} (hσ : DifferentiableAt ℝ σ x)
    (W : Lin E) :
    vdiv (fun y => (σ y)ᵀ (W y)) x = ⟪tdiv σ x, W x⟫_ℝ + σ x ⊡ W := by
  have hc : HasFDerivAt (fun y => (σ y)ᵀ)
      ((starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap.comp (fderiv ℝ σ x)) x :=
    (starL' ℝ : Lin E ≃L[ℝ] Lin E).hasFDerivAt.comp x hσ.hasFDerivAt
  have h := hc.clm_apply W.hasFDerivAt
  rw [vdiv, h.fderiv, map_add, inner_tdiv hσ, vdiv, fderiv_transpose_apply hσ, add_comm,
    Lin.dcontr_apply]
  rfl

section Continuity

theorem continuous_dcontr_right (W : Lin E) : Continuous fun A : Lin E => A ⊡ W := by
  let b := stdOrthonormalBasis ℝ E
  have : (fun A : Lin E => A ⊡ W) = fun A => ∑ i, ⟪A (b i), W (b i)⟫_ℝ :=
    funext fun A => Lin.dcontr_eq_sum b A W
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    (ContinuousLinearMap.apply ℝ E (b i)).continuous.inner continuous_const

theorem continuous_vdiv {v : E → E} (hv : ContDiff ℝ 1 v) : Continuous (vdiv v) :=
  (LinearMap.toContinuousLinearMap (Lin.tr : Lin E →ₗ[ℝ] ℝ)).continuous.comp
    (hv.continuous_fderiv one_ne_zero)

theorem contDiff_transpose_apply {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) (a : E) :
    ContDiff ℝ 1 (fun y => (σ y)ᵀ a) := by
  have : (fun y => (σ y)ᵀ a) = ((ContinuousLinearMap.apply ℝ E a).comp
      (starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap) ∘ σ := by ext y; simp
  rw [this]; exact (ContinuousLinearMap.contDiff _).comp hσ

theorem continuous_tdiv {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) : Continuous (tdiv σ) := by
  unfold tdiv
  exact continuous_finsetSum _ fun i _ =>
    (continuous_vdiv (contDiff_transpose_apply hσ _)).smul continuous_const

end Continuity

variable [MeasurableSpace E] [BorelSpace E]

/-- A **region on which the divergence theorem holds** (hypothesis structure): a measurable set
with compact closure, a finite surface measure and an outer normal such that
`∫_P div v dV = ∫_∂P v · n dA` for every `C¹` vector field, and fluxes of continuous tensor
fields are surface-integrable. Mathlib only provides the divergence theorem for boxes;
see `GAPS.md`. [Gurtin1981], §4. -/
structure DivergenceRegion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] where
  /-- The region `P`. -/
  carrier : Set E
  /-- The surface measure on `∂P`. -/
  surface : Measure E
  /-- The outer unit normal. -/
  normal : E → E
  measurableSet : MeasurableSet carrier
  isCompact_closure : IsCompact (closure carrier)
  /-- The divergence theorem. -/
  divergence : ∀ v : E → E, ContDiff ℝ 1 v →
    ∫ x in carrier, vdiv v x = ∫ x, ⟪v x, normal x⟫_ℝ ∂surface
  /-- Tractions of continuous stress fields are surface-integrable. -/
  integrable_traction : ∀ σ : E → Lin E, Continuous σ → Integrable (fun x => σ x (normal x)) surface

namespace DivergenceRegion

variable (P : DivergenceRegion E)

theorem volume_lt_top : volume P.carrier < ⊤ :=
  (measure_mono subset_closure).trans_lt P.isCompact_closure.measure_lt_top

theorem integrableOn {f : E → E} (hf : Continuous f) : IntegrableOn f P.carrier :=
  (hf.continuousOn.integrableOn_compact P.isCompact_closure).mono_set subset_closure

theorem integrableOn_real {f : E → ℝ} (hf : Continuous f) : IntegrableOn f P.carrier :=
  (hf.continuousOn.integrableOn_compact P.isCompact_closure).mono_set subset_closure

/-- **Divergence theorem for tensor fields**: `∫_∂P σ n dA = ∫_P div σ dV`. -/
theorem integral_traction {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) :
    ∫ x, σ x (P.normal x) ∂P.surface = ∫ x in P.carrier, tdiv σ x := by
  have hd : ∀ x, DifferentiableAt ℝ σ x := fun x => (hσ.differentiable one_ne_zero) x
  refine ext_inner_right ℝ fun a => ?_
  calc ⟪∫ x, σ x (P.normal x) ∂P.surface, a⟫_ℝ
      = ∫ x, ⟪a, σ x (P.normal x)⟫_ℝ ∂P.surface := by
        rw [real_inner_comm, integral_inner (P.integrable_traction σ hσ.continuous)]
    _ = ∫ x, ⟪(σ x)ᵀ a, P.normal x⟫_ℝ ∂P.surface := by
        congr 1; ext x; rw [Lin.inner_transpose_left]
    _ = ∫ x in P.carrier, vdiv (fun y => (σ y)ᵀ a) x :=
        (P.divergence _ (contDiff_transpose_apply hσ a)).symm
    _ = ∫ x in P.carrier, ⟪a, tdiv σ x⟫_ℝ := by
        congr 1; ext x; rw [real_inner_comm, inner_tdiv (hd x)]
    _ = ⟪∫ x in P.carrier, tdiv σ x, a⟫_ℝ := by
        rw [integral_inner (P.integrableOn (continuous_tdiv hσ)), real_inner_comm]

end DivergenceRegion

/-- **Localisation**: a continuous vector field whose integral over every small region in `Ω`
vanishes is zero on `Ω`. -/
theorem eq_zero_of_integral_regions {Ω : Set E} (parts : Set (DivergenceRegion E))
    (hsmall : ∀ x ∈ Ω, ∀ ε > 0, ∃ P ∈ parts, P.carrier ⊆ Ω ∩ ball x ε ∧ 0 < volume P.carrier)
    {f : E → E} (hf : Continuous f) (h : ∀ P ∈ parts, P.carrier ⊆ Ω → ∫ x in P.carrier, f x = 0) :
    ∀ x ∈ Ω, f x = 0 := by
  intro x hx
  by_contra hne
  set a := f x
  have ha : 0 < ‖a‖ ^ 2 := by positivity
  let g := fun y => ⟪a, f y⟫_ℝ
  have hg : Continuous g := continuous_const.inner hf
  have hgx : g x = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hg.continuousAt (‖a‖ ^ 2 / 2) (by positivity)
  obtain ⟨P, hP, hPsub, hPvol⟩ := hsmall x hx ε hε
  have hlow : ∀ y ∈ P.carrier, ‖a‖ ^ 2 / 2 ≤ g y := fun y hy => by
    have := hball (mem_ball.mp (hPsub hy).2)
    rw [Real.dist_eq, hgx] at this
    have := (abs_lt.mp this).1
    linarith
  have hint := setIntegral_ge_of_const_le P.measurableSet P.volume_lt_top.ne hlow
    (P.integrableOn_real hg)
  have hzero : ∫ y in P.carrier, g y = 0 := by
    simp only [g]
    rw [integral_inner (P.integrableOn hf), h P hP (fun y hy => (hPsub hy).1), inner_zero_right]
  rw [hzero, smul_eq_mul] at hint
  have : 0 < volume.real P.carrier := ENNReal.toReal_pos hPvol.ne' P.volume_lt_top.ne
  nlinarith

/-- Scalar localisation. -/
theorem eq_zero_of_integral_regions_real [Nontrivial E] {Ω : Set E}
    (parts : Set (DivergenceRegion E))
    (hsmall : ∀ x ∈ Ω, ∀ ε > 0, ∃ P ∈ parts, P.carrier ⊆ Ω ∩ ball x ε ∧ 0 < volume P.carrier)
    {g : E → ℝ} (hg : Continuous g) (h : ∀ P ∈ parts, P.carrier ⊆ Ω → ∫ x in P.carrier, g x = 0) :
    ∀ x ∈ Ω, g x = 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hc : Continuous fun y => g y • e := hg.smul continuous_const
  have := eq_zero_of_integral_regions parts hsmall hc fun P hP hPΩ => by
    rw [integral_smul_const, h P hP hPΩ, zero_smul]
  intro x hx
  exact (smul_eq_zero.mp (this x hx)).resolve_right he

/-- **Local equilibrium**: if the stress `σ` (`C¹`) and body force `b` (continuous) satisfy the
integral force balance `∫_∂P σ n dA + ∫_P b dV = 0` on every part `P` of a family containing
arbitrarily small parts around each point of `Ω`, then `div σ + b = 0` on `Ω`.
[Gurtin1981], §14. -/
theorem local_equilibrium {Ω : Set E} (parts : Set (DivergenceRegion E))
    (hsmall : ∀ x ∈ Ω, ∀ ε > 0, ∃ P ∈ parts, P.carrier ⊆ Ω ∩ ball x ε ∧ 0 < volume P.carrier)
    {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) {b : E → E} (hb : Continuous b)
    (hbal : ∀ P ∈ parts, P.carrier ⊆ Ω →
      (∫ x, σ x (P.normal x) ∂P.surface) + ∫ x in P.carrier, b x = 0) :
    ∀ x ∈ Ω, tdiv σ x + b x = 0 := by
  refine eq_zero_of_integral_regions parts hsmall ((continuous_tdiv hσ).add hb) fun P hP hPΩ => ?_
  rw [integral_add (P.integrableOn (continuous_tdiv hσ)) (P.integrableOn hb),
    ← P.integral_traction hσ]
  exact hbal P hP hPΩ

/-- **Balance of angular momentum ⇒ symmetry of the Cauchy stress.** If, in addition to the
force balance, the moments balance on every small part, in the coordinate-free form
`∫_∂P W x · σ n dA + ∫_P W x · b dV = 0` for every skew `W` (in three dimensions this is
`∫_∂P x × σ n + ∫_P x × b = 0`), then `σ` is symmetric on `Ω`. [Gurtin1981], §14. -/
theorem symmetric_of_moment_balance {Ω : Set E} (parts : Set (DivergenceRegion E))
    (hsmall : ∀ x ∈ Ω, ∀ ε > 0, ∃ P ∈ parts, P.carrier ⊆ Ω ∩ ball x ε ∧ 0 < volume P.carrier)
    {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) {b : E → E} (hb : Continuous b)
    (hbal : ∀ P ∈ parts, P.carrier ⊆ Ω →
      (∫ x, σ x (P.normal x) ∂P.surface) + ∫ x in P.carrier, b x = 0)
    (hmom : ∀ P ∈ parts, P.carrier ⊆ Ω → ∀ W ∈ Skw E,
      (∫ x, ⟪W x, σ x (P.normal x)⟫_ℝ ∂P.surface) + ∫ x in P.carrier, ⟪W x, b x⟫_ℝ = 0) :
    ∀ x ∈ Ω, σ x ∈ Sym E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro x _
    have : σ x = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
    rw [this]; exact (Sym E).zero_mem
  have hd : ∀ x, DifferentiableAt ℝ σ x := fun x => (hσ.differentiable one_ne_zero) x
  have heq := local_equilibrium parts hsmall hσ hb hbal
  -- `σ : W = 0` on `Ω` for every skew `W`
  have hW : ∀ W ∈ Skw E, ∀ x ∈ Ω, σ x ⊡ W = 0 := by
    intro W hWs
    have hcont : Continuous fun y => σ y ⊡ W :=
      (continuous_dcontr_right W).comp hσ.continuous
    refine eq_zero_of_integral_regions_real parts hsmall hcont fun P hP hPΩ => ?_
    have hv : ContDiff ℝ 1 (fun y => (σ y)ᵀ (W y)) :=
      (((starL' ℝ : Lin E ≃L[ℝ] Lin E).contDiff.comp hσ).clm_apply W.contDiff)
    have hWb : Continuous fun y => ⟪W y, b y⟫_ℝ := W.continuous.inner hb
    have h1 : ∫ x, ⟪W x, σ x (P.normal x)⟫_ℝ ∂P.surface =
        ∫ x in P.carrier, vdiv (fun y => (σ y)ᵀ (W y)) x := by
      rw [P.divergence _ hv]
      congr 1; ext x; rw [Lin.inner_transpose_left]
    have h2 : Set.EqOn (vdiv (fun y => (σ y)ᵀ (W y))) (fun y => σ y ⊡ W - ⟪W y, b y⟫_ℝ)
        P.carrier := fun y hy => by
      have e := heq y (hPΩ hy)
      rw [vdiv_transpose_apply_linear (hd y), eq_neg_of_add_eq_zero_left e, inner_neg_left,
        real_inner_comm]
      ring
    have hmomP := hmom P hP hPΩ W hWs
    rw [h1, setIntegral_congr_fun P.measurableSet h2,
      integral_sub (P.integrableOn_real hcont) (P.integrableOn_real hWb)] at hmomP
    linarith
  intro x hx
  have h := hW (Lin.skw (σ x)) (Lin.skw_mem _) x hx
  have hsplit : σ x ⊡ Lin.skw (σ x) = Lin.skw (σ x) ⊡ Lin.skw (σ x) := by
    have e : σ x ⊡ Lin.skw (σ x) = (Lin.sym (σ x) + Lin.skw (σ x)) ⊡ Lin.skw (σ x) := by
      rw [Lin.sym_add_skw]
    rw [e, map_add, LinearMap.add_apply, Lin.dcontr_sym_skw (Lin.sym_mem _) (Lin.skw_mem _),
      zero_add]
  rw [hsplit, Lin.dcontr_self_eq_zero] at h
  rw [← Lin.sym_add_skw (σ x), h, add_zero]
  exact Lin.sym_mem _

end ContinuumMechanics
