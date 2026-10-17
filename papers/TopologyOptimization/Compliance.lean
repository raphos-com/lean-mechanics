import DiscreteMechanics.Stiffness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Star.Real

/-!
# Compliance minimisation in density-based topology optimisation

In the density (SIMP) approach to topology optimisation of Bendsøe–Kikuchi, Bendsøe and Sigmund,
a structure is discretised into finite elements `e : ι` with element stiffness matrices
`Kₑ` (symmetric, positive semidefinite) acting on the degrees of freedom `D`. Each element
carries a **weight** `wₑ ≥ 0` and the global stiffness matrix is

`K(w) = Σₑ wₑ Kₑ`.

In the SIMP model (*solid isotropic material with penalisation*) the weights come from design
densities `xₑ ∈ (0, 1]` through the power law `wₑ = xₑ ^ p`, `p > 1`; for `p = 1` one recovers the
variable-thickness-sheet problem. Under a load `f` the displacement is `u = K(w)⁻¹ f` and the
**compliance** (the work of the load, the inverse of the global stiffness) is `c(w) = fᵀ u`.

## Main results

* `compliance_eq_energy`, `compliance_nonneg`, `compliance_pos`: `c = uᵀ K u ≥ 0`, and `c > 0`
  for `f ≠ 0`.
* `compliance_variational`, `compliance_isGreatest`, `compliance_eq_iSup`: the complementary
  energy characterisation `c(w) = sup_v (2 fᵀ v - Σₑ wₑ vᵀ Kₑ v)`, attained at `v = u`.
* `compliance_antitone`: adding material never increases compliance.
* `compliance_convexOn`, `compliance_convexOn_pos`: compliance is convex in the weights (the
  variable-thickness-sheet problem is a convex problem).
* `compliance_sub`: the exact finite-difference formula `c(w') - c(w) = -uᵀ K(w' - w) u'`.
* `hasDerivAt_compliance_line`, `hasDerivAt_compliance_single`: the sensitivity
  `∂c/∂wₑ = -uᵀ Kₑ u ≤ 0` (the self-adjoint adjoint method), and `hasDerivAt_simpCompliance`:
  the SIMP sensitivity `∂c/∂xₑ = -p xₑ ^ (p - 1) uᵀ Kₑ u` used in the 99-line code.
* `simp_penalization`: intermediate densities are penalised, `x ^ p < x` for `0 < x < 1 < p`;
  `volume_combo`: the volume `Σₑ xₑ` is linear.

## References

* [Bendsoe1988] M. P. Bendsøe, N. Kikuchi, *Generating optimal topologies in structural design
  using a homogenization method*, Comput. Methods Appl. Mech. Engrg. 71 (1988) 197–224.
* [Sigmund2000] O. Sigmund, *Topology optimization: a tool for the tailoring of structures and
  materials*, Phil. Trans. R. Soc. Lond. A 358 (2000) 211–227.
* [Sigmund2001] O. Sigmund, *A 99 line topology optimization code written in Matlab*, Struct.
  Multidisc. Optim. 21 (2001) 120–127.
* [BendsoeSigmund2003] M. P. Bendsøe, O. Sigmund, *Topology Optimization: Theory, Methods and
  Applications*, Springer (2003).
-/

open Matrix Filter Topology

namespace TopologyOptimization

variable {ι D : Type*} [Fintype ι]

/-! ### Stiffness, displacement and compliance -/

/-- The **global stiffness matrix** `K(w) = Σₑ wₑ Kₑ` assembled from element stiffness matrices
`Kₑ` with element weights `wₑ`. -/
def stiffness (Ke : ι → Matrix D D ℝ) (w : ι → ℝ) : Matrix D D ℝ := ∑ e, w e • Ke e

variable [Fintype D] [DecidableEq D] in
/-- The **displacement** `u = K(w)⁻¹ f` under the load `f`. -/
noncomputable def displacement (Ke : ι → Matrix D D ℝ) (w : ι → ℝ) (f : D → ℝ) : D → ℝ :=
  (stiffness Ke w)⁻¹ *ᵥ f

variable [Fintype D] [DecidableEq D] in
/-- The **compliance** `c(w) = fᵀ u = fᵀ K(w)⁻¹ f`. -/
noncomputable def compliance (Ke : ι → Matrix D D ℝ) (w : ι → ℝ) (f : D → ℝ) : ℝ :=
  f ⬝ᵥ displacement Ke w f

variable (Ke : ι → Matrix D D ℝ)

/-- The stiffness is additive in the weights. -/
theorem stiffness_add (w w' : ι → ℝ) :
    stiffness Ke (w + w') = stiffness Ke w + stiffness Ke w' := by
  simp [stiffness, add_smul, Finset.sum_add_distrib]

/-- The stiffness is subtractive in the weights. -/
theorem stiffness_sub (w w' : ι → ℝ) :
    stiffness Ke (w - w') = stiffness Ke w - stiffness Ke w' := by
  simp [stiffness, sub_smul, Finset.sum_sub_distrib]

/-- The stiffness is homogeneous in the weights. -/
theorem stiffness_smul (a : ℝ) (w : ι → ℝ) : stiffness Ke (a • w) = a • stiffness Ke w := by
  simp [stiffness, Finset.smul_sum, smul_smul]

/-- The stiffness for the unit weight on a single element is that element's stiffness. -/
theorem stiffness_single [DecidableEq ι] (e : ι) : stiffness Ke (Pi.single e 1) = Ke e := by
  simp [stiffness, Pi.single_apply]

variable [Fintype D]

/-- The strain energy is linear in the weights: `vᵀ K(w) v = Σₑ wₑ vᵀ Kₑ v`. -/
theorem dotProduct_stiffness_mulVec (w : ι → ℝ) (v : D → ℝ) :
    v ⬝ᵥ (stiffness Ke w *ᵥ v) = ∑ e, w e * (v ⬝ᵥ (Ke e *ᵥ v)) := by
  simp [stiffness, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul]

omit [Fintype D] in
/-- For positive semidefinite element matrices and nonnegative weights, `K(w)` is positive
semidefinite. -/
theorem stiffness_posSemidef [Finite D] (hKe : ∀ e, (Ke e).PosSemidef) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) :
    (stiffness Ke w).PosSemidef :=
  posSemidef_sum _ fun e _ => (hKe e).smul (hw e)

omit [Fintype D] in
/-- **Admissibility**: if every element stiffness is positive semidefinite, the unweighted
assembly `Σₑ Kₑ` is positive definite (the supported structure is kinematically determinate) and
all weights are positive, then `K(w)` is positive definite. -/
theorem stiffness_posDef [Finite D] (hKe : ∀ e, (Ke e).PosSemidef) (hsum : (∑ e, Ke e).PosDef)
    {w : ι → ℝ} (hw : ∀ e, 0 < w e) : (stiffness Ke w).PosDef := by
  cases nonempty_fintype D
  refine PosDef.of_dotProduct_mulVec_pos (stiffness_posSemidef Ke hKe fun e => (hw e).le).1 ?_
  intro x hx
  have h := hsum.dotProduct_mulVec_pos hx
  rw [star_trivial] at h ⊢
  rw [dotProduct_stiffness_mulVec]
  rw [sum_mulVec, dotProduct_sum] at h
  have hq : ∀ e, 0 ≤ x ⬝ᵥ (Ke e *ᵥ x) := fun e => by
    simpa using (hKe e).dotProduct_mulVec_nonneg x
  by_contra hc
  push Not at hc
  have hz : ∀ e ∈ Finset.univ, w e * (x ⬝ᵥ (Ke e *ᵥ x)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun e _ => mul_nonneg (hw e).le (hq e)).1
      (le_antisymm hc (Finset.sum_nonneg fun e _ => mul_nonneg (hw e).le (hq e)))
  have : ∑ e, x ⬝ᵥ (Ke e *ᵥ x) = 0 := Finset.sum_eq_zero fun e he => by
    rcases mul_eq_zero.1 (hz e he) with h0 | h0
    · exact absurd h0 (hw e).ne'
    · exact h0
  linarith

omit [Fintype D] in
/-- The set of weights with positive definite stiffness is convex. -/
theorem convex_admissible [Finite D] : Convex ℝ {w : ι → ℝ | (stiffness Ke w).PosDef} := by
  intro w₁ h₁ w₂ h₂ a b ha hb hab
  simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
  rw [stiffness_add, stiffness_smul, stiffness_smul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    simpa [hab] using h₂
  · exact (h₁.smul ha').add_posSemidef (h₂.posSemidef.smul hb)

variable {Ke} [DecidableEq D]

/-- An invertible stiffness matrix maps the displacement back to the load: `K u = f`. -/
theorem stiffness_mulVec_displacement {w : ι → ℝ} (h : IsUnit (stiffness Ke w).det)
    (f : D → ℝ) : stiffness Ke w *ᵥ displacement Ke w f = f := by
  rw [displacement, mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]

/-! ### Compliance as strain energy -/

/-- **Compliance equals twice the strain energy**: `c = fᵀ u = uᵀ K u`. -/
theorem compliance_eq_energy {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f : D → ℝ) :
    compliance Ke w f =
      displacement Ke w f ⬝ᵥ (stiffness Ke w *ᵥ displacement Ke w f) := by
  rw [stiffness_mulVec_displacement (isUnit_iff_isUnit_det _ |>.1 hK.isUnit), compliance,
    dotProduct_comm]

/-- The compliance is nonnegative. -/
theorem compliance_nonneg {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f : D → ℝ) :
    0 ≤ compliance Ke w f := by
  rw [compliance_eq_energy hK]
  simpa using hK.posSemidef.dotProduct_mulVec_nonneg (displacement Ke w f)

/-- The compliance is positive for a nonzero load. -/
theorem compliance_pos {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) {f : D → ℝ} (hf : f ≠ 0) :
    0 < compliance Ke w f := by
  simpa [compliance, displacement] using hK.inv.dotProduct_mulVec_pos hf

/-! ### The complementary energy (variational) characterisation -/

/-- **Variational principle**: for every virtual displacement `v`,
`2 fᵀ v - vᵀ K v ≤ c`. -/
theorem compliance_variational {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f v : D → ℝ) :
    2 * (f ⬝ᵥ v) - v ⬝ᵥ (stiffness Ke w *ᵥ v) ≤ compliance Ke w f := by
  have hu := stiffness_mulVec_displacement (isUnit_iff_isUnit_det _ |>.1 hK.isUnit) f
  have h := DiscreteMechanics.potentialEnergy_eq_add hK.isHermitian.isSymm hu v
  have hnn : 0 ≤ (v - displacement Ke w f) ⬝ᵥ
      (stiffness Ke w *ᵥ (v - displacement Ke w f)) := by
    simpa using hK.posSemidef.dotProduct_mulVec_nonneg (v - displacement Ke w f)
  have hc := compliance_eq_energy hK f
  simp only [DiscreteMechanics.potentialEnergy] at h
  rw [compliance] at hc ⊢
  linarith

/-- The variational bound is attained at the true displacement `v = u`. -/
theorem compliance_variational_eq {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f : D → ℝ) :
    2 * (f ⬝ᵥ displacement Ke w f) -
      displacement Ke w f ⬝ᵥ (stiffness Ke w *ᵥ displacement Ke w f) = compliance Ke w f := by
  rw [← compliance_eq_energy hK, compliance]
  ring

/-- The compliance is the **greatest** value of the complementary functional
`v ↦ 2 fᵀ v - Σₑ wₑ vᵀ Kₑ v`. -/
theorem compliance_isGreatest {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f : D → ℝ) :
    IsGreatest (Set.range fun v => 2 * (f ⬝ᵥ v) - ∑ e, w e * (v ⬝ᵥ (Ke e *ᵥ v)))
      (compliance Ke w f) := by
  refine ⟨⟨displacement Ke w f, ?_⟩, ?_⟩
  · simp only
    rw [← dotProduct_stiffness_mulVec, compliance_variational_eq hK]
  · rintro _ ⟨v, rfl⟩
    simp only
    rw [← dotProduct_stiffness_mulVec]
    exact compliance_variational hK f v

/-- `c(w) = sup_v (2 fᵀ v - Σₑ wₑ vᵀ Kₑ v)`. -/
theorem compliance_eq_iSup {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (f : D → ℝ) :
    compliance Ke w f = ⨆ v, (2 * (f ⬝ᵥ v) - ∑ e, w e * (v ⬝ᵥ (Ke e *ᵥ v))) :=
  ((compliance_isGreatest hK f).csSup_eq).symm

/-! ### Monotonicity and convexity -/

/-- **Adding material never makes the structure more compliant**: if `w ≤ w'` pointwise, the
element stiffnesses are positive semidefinite and `K(w)` is positive definite, then
`c(w') ≤ c(w)` (and `K(w')` is positive definite). -/
theorem compliance_antitone (hKe : ∀ e, (Ke e).PosSemidef) {w w' : ι → ℝ}
    (hK : (stiffness Ke w).PosDef) (hww : w ≤ w') (f : D → ℝ) :
    (stiffness Ke w').PosDef ∧ compliance Ke w' f ≤ compliance Ke w f := by
  have hd : (stiffness Ke (w' - w)).PosSemidef :=
    stiffness_posSemidef Ke hKe fun e => sub_nonneg.2 (hww e)
  have hK' : (stiffness Ke w').PosDef := by
    have := hK.add_posSemidef hd
    rwa [← stiffness_add, add_sub_cancel] at this
  refine ⟨hK', ?_⟩
  set u' := displacement Ke w' f
  have h1 := compliance_variational hK f u'
  have h2 := compliance_variational_eq hK' f
  have h3 : 0 ≤ u' ⬝ᵥ (stiffness Ke (w' - w) *ᵥ u') := by
    simpa using hd.dotProduct_mulVec_nonneg u'
  rw [stiffness_sub, sub_mulVec, dotProduct_sub] at h3
  linarith

/-- **Convexity of compliance** in the weights (the variable-thickness-sheet problem, `p = 1`):
`c` is convex on the set of admissible weights, being a supremum of affine functions. -/
theorem compliance_convexOn (f : D → ℝ) :
    ConvexOn ℝ {w : ι → ℝ | (stiffness Ke w).PosDef} fun w => compliance Ke w f := by
  refine ⟨convex_admissible Ke, ?_⟩
  intro w₁ h₁ w₂ h₂ a b ha hb hab
  have hw := convex_admissible Ke h₁ h₂ ha hb hab
  simp only [Set.mem_ofPred_eq, smul_eq_mul] at h₁ h₂ hw ⊢
  set u := displacement Ke (a • w₁ + b • w₂) f
  have h0 := compliance_variational_eq hw f
  have e1 := compliance_variational h₁ f u
  have e2 := compliance_variational h₂ f u
  rw [stiffness_add, stiffness_smul, stiffness_smul, add_mulVec, smul_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h0
  rw [← h0]
  have : 2 * (f ⬝ᵥ u) = a * (2 * (f ⬝ᵥ u)) + b * (2 * (f ⬝ᵥ u)) := by
    rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

/-- **Convexity on the positive orthant**: for positive semidefinite element stiffnesses whose
sum is positive definite, the compliance is convex on `{w | ∀ e, 0 < wₑ}`. -/
theorem compliance_convexOn_pos (hKe : ∀ e, (Ke e).PosSemidef) (hsum : (∑ e, Ke e).PosDef)
    (f : D → ℝ) : ConvexOn ℝ {w : ι → ℝ | ∀ e, 0 < w e} fun w => compliance Ke w f := by
  refine (compliance_convexOn f).subset (fun w hw => stiffness_posDef Ke hKe hsum hw) ?_
  intro w₁ h₁ w₂ h₂ a b ha hb hab e
  simp only [Set.mem_ofPred_eq] at h₁ h₂
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    simpa [hab] using h₂ e
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (h₁ e)) (mul_nonneg hb (h₂ e).le)

/-! ### Sensitivity analysis -/

/-- **Exact compliance difference**: if `K(w)` is positive definite and `K(w')` is invertible,
then `c(w') - c(w) = -uᵀ K(w' - w) u'` with `u = u(w)`, `u' = u(w')`. -/
theorem compliance_sub {w w' : ι → ℝ} (hK : (stiffness Ke w).PosDef)
    (hK' : IsUnit (stiffness Ke w').det) (f : D → ℝ) :
    compliance Ke w' f - compliance Ke w f =
      -(displacement Ke w f ⬝ᵥ (stiffness Ke (w' - w) *ᵥ displacement Ke w' f)) := by
  have hu := stiffness_mulVec_displacement (isUnit_iff_isUnit_det _ |>.1 hK.isUnit) f
  have hu' := stiffness_mulVec_displacement hK' f
  have hs := DiscreteMechanics.dotProduct_mulVec_comm_of_isSymm hK.isHermitian.isSymm
    (displacement Ke w f) (displacement Ke w' f)
  rw [hu] at hs
  rw [stiffness_sub, sub_mulVec, dotProduct_sub, hu', compliance, compliance, hs,
    dotProduct_comm f (displacement Ke w f)]
  rw [dotProduct_comm f (displacement Ke w' f)]
  ring

/-- **Sensitivity along a line**: the derivative of `t ↦ c(w + t d)` at `t = 0` is
`-uᵀ K(d) u = -Σₑ dₑ uᵀ Kₑ u` (no adjoint solve is needed: the problem is self-adjoint). -/
theorem hasDerivAt_compliance_line {w : ι → ℝ} (hK : (stiffness Ke w).PosDef) (d : ι → ℝ)
    (f : D → ℝ) :
    HasDerivAt (fun t : ℝ => compliance Ke (w + t • d) f)
      (-(displacement Ke w f ⬝ᵥ (stiffness Ke d *ᵥ displacement Ke w f))) 0 := by
  set u := displacement Ke w f with hu
  set A : ℝ → Matrix D D ℝ := fun t => stiffness Ke w + t • stiffness Ke d with hA
  have hAe : ∀ t : ℝ, stiffness Ke (w + t • d) = A t := fun t => by
    rw [stiffness_add, stiffness_smul]
  have hAc : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hA0 : A 0 = stiffness Ke w := by simp [hA]
  have hdet : (A 0).det ≠ 0 := by rw [hA0]; exact hK.det_pos.ne'
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (A t).det ≠ 0 :=
    hAc.matrix_det.continuousAt.eventually_ne hdet
  set φ : ℝ → ℝ := fun t => u ⬝ᵥ (stiffness Ke d *ᵥ ((A t)⁻¹ *ᵥ f)) with hφdef
  have hinv : ContinuousAt (fun t => (A t)⁻¹) 0 :=
    (continuousAt_matrix_inv (A 0)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)).comp hAc.continuousAt
  have hφ : ContinuousAt φ 0 := by
    have hc : Continuous fun M : Matrix D D ℝ => u ⬝ᵥ (stiffness Ke d *ᵥ (M *ᵥ f)) :=
      continuous_const.dotProduct
        (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))
    exact hc.continuousAt.comp hinv
  have hφ0 : φ 0 = u ⬝ᵥ (stiffness Ke d *ᵥ u) := by
    simp only [hφdef, hA0, hu, displacement]
  rw [hasDerivAt_iff_tendsto_slope]
  have key : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      -φ t = slope (fun t : ℝ => compliance Ke (w + t • d) f) 0 t := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with t ht hdt
    have ht' : t ≠ 0 := ht
    have hdisp : displacement Ke (w + t • d) f = (A t)⁻¹ *ᵥ f := by rw [displacement, hAe]
    have h := compliance_sub hK (w' := w + t • d)
      (by rw [hAe]; exact isUnit_iff_ne_zero.2 hdt) f
    rw [add_sub_cancel_left, stiffness_smul, smul_mulVec, dotProduct_smul, smul_eq_mul,
      hdisp] at h
    rw [slope_def_field, zero_smul, add_zero, h, sub_zero]
    field_simp
    rfl
  rw [← hφ0]
  exact (hφ.tendsto.neg.mono_left nhdsWithin_le_nhds).congr' key

/-- **Element sensitivity**: `∂c/∂wₑ = -uᵀ Kₑ u`. -/
theorem hasDerivAt_compliance_single [DecidableEq ι] {w : ι → ℝ}
    (hK : (stiffness Ke w).PosDef) (e : ι) (f : D → ℝ) :
    HasDerivAt (fun t : ℝ => compliance Ke (w + t • Pi.single e 1) f)
      (-(displacement Ke w f ⬝ᵥ (Ke e *ᵥ displacement Ke w f))) 0 := by
  have h := hasDerivAt_compliance_line hK (Pi.single e 1) f
  rwa [stiffness_single] at h

/-- The element sensitivity is nonpositive for a positive semidefinite element stiffness:
`-uᵀ Kₑ u ≤ 0`. -/
theorem sensitivity_nonpos {e : ι} (hKe : (Ke e).PosSemidef) (w : ι → ℝ) (f : D → ℝ) :
    -(displacement Ke w f ⬝ᵥ (Ke e *ᵥ displacement Ke w f)) ≤ 0 := by
  simpa using hKe.dotProduct_mulVec_nonneg (displacement Ke w f)

/-! ### The SIMP interpolation -/

/-- The **SIMP weights** `wₑ = xₑ ^ p` of the densities `x` with penalisation power `p`. -/
noncomputable def simpWeights (p : ℝ) (x : ι → ℝ) : ι → ℝ := fun e => x e ^ p

omit [Fintype ι] in
/-- Full material `x = 1` has unit SIMP weight. -/
theorem simpWeights_one (p : ℝ) : simpWeights p (1 : ι → ℝ) = 1 := by
  funext e
  simp [simpWeights]

/-- **SIMP sensitivity**: `∂c/∂xₑ = -p xₑ ^ (p - 1) uᵀ Kₑ u` for a positive density `xₑ`. -/
theorem hasDerivAt_simpCompliance [DecidableEq ι] {p : ℝ} {x : ι → ℝ} {e : ι}
    (hx : 0 < x e) (hK : (stiffness Ke (simpWeights p x)).PosDef) (f : D → ℝ) :
    HasDerivAt (fun t : ℝ => compliance Ke (simpWeights p (x + t • Pi.single e 1)) f)
      (-(p * x e ^ (p - 1) * (displacement Ke (simpWeights p x) f ⬝ᵥ
        (Ke e *ᵥ displacement Ke (simpWeights p x) f)))) 0 := by
  set ψ : ℝ → ℝ := fun t => (x e + t) ^ p - x e ^ p with hψ
  have hψd : HasDerivAt ψ (p * x e ^ (p - 1)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x e + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (x e)
    have h2 := (h1.rpow_const (p := p) (Or.inl (by simpa using hx.ne'))).sub_const (x e ^ p)
    convert h2 using 1
    simp
  have hg := hasDerivAt_compliance_single hK e f
  have hc := hg.comp_of_eq (h := ψ) 0 hψd (by simp [hψ])
  have hfun : (fun t : ℝ => compliance Ke (simpWeights p (x + t • Pi.single e 1)) f) =
      (fun t : ℝ => compliance Ke (simpWeights p x + t • Pi.single e 1) f) ∘ ψ := by
    funext t
    simp only [Function.comp]
    congr 1
    funext e'
    rcases eq_or_ne e' e with rfl | h
    · simp [simpWeights, hψ]
    · simp [simpWeights, h]
  rw [hfun]
  convert hc using 1
  ring

/-- The SIMP sensitivity is nonpositive for `p ≥ 0` and a positive density. -/
theorem simp_sensitivity_nonpos {p : ℝ} (hp : 0 ≤ p) {x : ι → ℝ} {e : ι} (hx : 0 < x e)
    (hKe : (Ke e).PosSemidef) (f : D → ℝ) :
    -(p * x e ^ (p - 1) * (displacement Ke (simpWeights p x) f ⬝ᵥ
        (Ke e *ᵥ displacement Ke (simpWeights p x) f))) ≤ 0 := by
  have h := sensitivity_nonpos hKe (simpWeights p x) f
  have hpx : 0 ≤ p * x e ^ (p - 1) := mul_nonneg hp (Real.rpow_nonneg hx.le _)
  nlinarith

/-- **SIMP penalisation**: for `0 < x < 1` and `p > 1`, `x ^ p < x`: an intermediate density
gives less stiffness than its share of material, so intermediate densities are uneconomical. -/
theorem simp_penalization {x p : ℝ} (h0 : 0 < x) (h1 : x < 1) (hp : 1 < p) : x ^ p < x :=
  Real.rpow_lt_self_of_lt_one h0 h1 hp

/-- The **material volume** `V(x) = Σₑ xₑ` of the densities `x` (equal element volumes). -/
def volume (x : ι → ℝ) : ℝ := ∑ e, x e

omit [Fintype D] [DecidableEq D] in
/-- The volume is linear in the densities. -/
theorem volume_combo (a b : ℝ) (x y : ι → ℝ) :
    volume (a • x + b • y) = a * volume x + b * volume y := by
  simp [volume, Finset.sum_add_distrib, Finset.mul_sum]

end TopologyOptimization
