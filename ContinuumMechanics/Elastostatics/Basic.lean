import Mathlib.MeasureTheory.Measure.OpenPos
import ContinuumMechanics.Stress.Balance
import ContinuumMechanics.Tensor.Fourth
import ContinuumMechanics.Kinematics.Rigid

/-!
# Linear elastostatics: work, Clapeyron, Betti, Kirchhoff

A linear elastic body occupies a region `B` (with the divergence theorem, `DivergenceRegion`),
has an elasticity tensor `ℂ` with major and minor symmetries, a displacement field `u`, the
infinitesimal strain `ε(u) = sym ∇u` and the stress `σ(u) = ℂ ε(u)`. Equilibrium under a body
force `b` is `div σ(u) + b = 0` in `B` ([Gurtin1981], §§30–33; [Ciarlet1988], §6.1).

## Main results

* `vdiv_transpose_apply`: `div (σᵀ u) = div σ · u + σ : ∇u`.
* `work_identity`: `∫_B σ : ε(u) = ∫_∂B u · σ n + ∫_B u · b` for symmetric `σ` in equilibrium.
* `clapeyron`: `2 U(u) = ∫_∂B u · σ(u) n + ∫_B u · b`, with strain energy
  `U(u) = ½ ∫_B ε(u) : ℂ ε(u)`. [Gurtin1981], §31.
* `betti`: **Betti's reciprocal theorem**
  `∫_∂B u₂ · σ₁ n + ∫_B u₂ · b₁ = ∫_∂B u₁ · σ₂ n + ∫_B u₁ · b₂`. [Gurtin1981], §32.
* `kirchhoff_uniqueness`: **Kirchhoff's uniqueness theorem** — if `ℂ` is positive definite and two
  solutions of the mixed problem produce no boundary work difference
  (`(u₁ - u₂) · σ(u₁ - u₂) n = 0` on `∂B`, as for prescribed displacements or tractions on
  complementary parts of `∂B`), they differ by an infinitesimal rigid displacement on a connected
  body. [Gurtin1981], §33.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§30–33.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.1.
-/

open MeasureTheory Metric Set
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Product rule**: `div (σᵀ u) = div σ · u + σ : ∇u`. -/
theorem vdiv_transpose_apply {σ : E → Lin E} {u : E → E} {x : E} (hσ : DifferentiableAt ℝ σ x)
    (hu : DifferentiableAt ℝ u x) :
    vdiv (fun y => (σ y)ᵀ (u y)) x = ⟪tdiv σ x, u x⟫_ℝ + σ x ⊡ fderiv ℝ u x := by
  have hc : HasFDerivAt (fun y => (σ y)ᵀ)
      ((starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap.comp (fderiv ℝ σ x)) x :=
    (starL' ℝ : Lin E ≃L[ℝ] Lin E).hasFDerivAt.comp x hσ.hasFDerivAt
  have h := hc.clm_apply hu.hasFDerivAt
  rw [vdiv, h.fderiv, map_add, inner_tdiv hσ, vdiv, fderiv_transpose_apply hσ, add_comm,
    Lin.dcontr_apply]
  rfl

/-- The **infinitesimal strain field** `ε(u) = sym ∇u`. -/
noncomputable def strainField (u : E → E) (x : E) : Lin E := Lin.sym (fderiv ℝ u x)

/-- The **stress field** `σ(u) = ℂ ε(u)` of a linear elastic material. -/
noncomputable def stressField (C : Lin4 E) (u : E → E) (x : E) : Lin E := C (strainField u x)

theorem contDiff_strainField {u : E → E} (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (strainField u) :=
  (LinearMap.toContinuousLinearMap (Lin.sym : Lin E →ₗ[ℝ] Lin E)).contDiff.comp
    (hu.fderiv_right (by norm_num))

theorem contDiff_stressField (C : Lin4 E) {u : E → E} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (stressField C u) :=
  C.contDiff.comp (contDiff_strainField hu)

variable [MeasurableSpace E] [BorelSpace E]

section Identities

variable (B : DivergenceRegion E)

/-- **Work identity**: for a symmetric stress field in equilibrium (`div σ + b = 0` on `B`),
`∫_B σ : ε(u) = ∫_∂B u · σ n + ∫_B u · b`. [Gurtin1981], §31. -/
theorem work_identity {σ : E → Lin E} (hσ : ContDiff ℝ 1 σ) (hsym : ∀ x, σ x ∈ Sym E)
    {b : E → E} (hb : Continuous b) (heq : ∀ x ∈ B.carrier, tdiv σ x + b x = 0)
    {u : E → E} (hu : ContDiff ℝ 1 u) :
    ∫ x in B.carrier, σ x ⊡ strainField u x =
      (∫ x, ⟪u x, σ x (B.normal x)⟫_ℝ ∂B.surface) + ∫ x in B.carrier, ⟪u x, b x⟫_ℝ := by
  have hdσ : ∀ x, DifferentiableAt ℝ σ x := fun x => (hσ.differentiable one_ne_zero) x
  have hdu : ∀ x, DifferentiableAt ℝ u x := fun x => (hu.differentiable one_ne_zero) x
  have hv : ContDiff ℝ 1 (fun y => (σ y)ᵀ (u y)) :=
    ((starL' ℝ : Lin E ≃L[ℝ] Lin E).contDiff.comp hσ).clm_apply hu
  have hflux : ∫ x, ⟪u x, σ x (B.normal x)⟫_ℝ ∂B.surface =
      ∫ x in B.carrier, vdiv (fun y => (σ y)ᵀ (u y)) x := by
    rw [B.divergence _ hv]
    congr 1; ext x; rw [Lin.inner_transpose_left]
  have hpt : EqOn (vdiv (fun y => (σ y)ᵀ (u y)))
      (fun x => σ x ⊡ strainField u x - ⟪u x, b x⟫_ℝ) B.carrier := fun x hx => by
    have h1 := vdiv_transpose_apply (hdσ x) (hdu x)
    have h2 : tdiv σ x = -b x := eq_neg_of_add_eq_zero_left (heq x hx)
    have h3 : σ x ⊡ fderiv ℝ u x = σ x ⊡ strainField u x :=
      Lin.dcontr_sym_of_mem_sym (hsym x) _
    simp only
    rw [h1, h2, h3, inner_neg_left, real_inner_comm (u x) (b x)]
    ring
  have hc1 : Continuous fun x => σ x ⊡ strainField u x := by
    have := (continuous_dcontr_right (E := E))
    have hs : Continuous (strainField u) := by
      unfold strainField
      exact (LinearMap.toContinuousLinearMap (Lin.sym : Lin E →ₗ[ℝ] Lin E)).continuous.comp
        (hu.continuous_fderiv one_ne_zero)
    -- `(A, S) ↦ A : S` is continuous (bilinear in finite dimension)
    let b := stdOrthonormalBasis ℝ E
    have e : (fun x => σ x ⊡ strainField u x) =
        fun x => ∑ i, ⟪σ x (b i), strainField u x (b i)⟫_ℝ :=
      funext fun x => Lin.dcontr_eq_sum b _ _
    rw [e]
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℝ E (b i)).continuous.comp hσ.continuous).inner
        ((ContinuousLinearMap.apply ℝ E (b i)).continuous.comp hs)
  have hc2 : Continuous fun x => ⟪u x, b x⟫_ℝ := hu.continuous.inner hb
  rw [hflux, setIntegral_congr_fun B.measurableSet hpt,
    integral_sub (B.integrableOn_real hc1) (B.integrableOn_real hc2)]
  ring

/-- The **strain energy** `U(u) = ½ ∫_B ε(u) : ℂ ε(u)`. [Gurtin1981], §31. -/
noncomputable def strainEnergy (C : Lin4 E) (u : E → E) : ℝ :=
  2⁻¹ * ∫ x in B.carrier, strainField u x ⊡ C (strainField u x)

/-- **Clapeyron's theorem**: `2 U(u) = ∫_∂B u · σ(u) n + ∫_B u · b` for an equilibrium
displacement. [Gurtin1981], §31. -/
theorem clapeyron {C : Lin4 E} (hC : C.HasMinorSymm) {u : E → E} (hu : ContDiff ℝ 2 u)
    {b : E → E} (hb : Continuous b)
    (heq : ∀ x ∈ B.carrier, tdiv (stressField C u) x + b x = 0) :
    2 * strainEnergy B C u =
      (∫ x, ⟪u x, stressField C u x (B.normal x)⟫_ℝ ∂B.surface) +
        ∫ x in B.carrier, ⟪u x, b x⟫_ℝ := by
  rw [strainEnergy, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul,
    ← work_identity B (contDiff_stressField C hu) (fun x => hC.1 _) hb heq (hu.of_le one_le_two)]
  congr 1; ext x; rw [stressField, Lin.dcontr_comm]

/-- **Betti's reciprocal theorem**: for two equilibrium displacements `u₁`, `u₂` with body forces
`b₁`, `b₂`, the work of the first load system on the second displacement equals the work of the
second on the first. [Gurtin1981], §32. -/
theorem betti {C : Lin4 E} (hCm : C.HasMinorSymm) (hCM : C.HasMajorSymm) {u₁ u₂ b₁ b₂ : E → E}
    (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂) (hb₁ : Continuous b₁) (hb₂ : Continuous b₂)
    (heq₁ : ∀ x ∈ B.carrier, tdiv (stressField C u₁) x + b₁ x = 0)
    (heq₂ : ∀ x ∈ B.carrier, tdiv (stressField C u₂) x + b₂ x = 0) :
    (∫ x, ⟪u₂ x, stressField C u₁ x (B.normal x)⟫_ℝ ∂B.surface)
        + ∫ x in B.carrier, ⟪u₂ x, b₁ x⟫_ℝ =
      (∫ x, ⟪u₁ x, stressField C u₂ x (B.normal x)⟫_ℝ ∂B.surface)
        + ∫ x in B.carrier, ⟪u₁ x, b₂ x⟫_ℝ := by
  rw [← work_identity B (contDiff_stressField C hu₁) (fun x => hCm.1 _) hb₁ heq₁
      (hu₂.of_le one_le_two),
    ← work_identity B (contDiff_stressField C hu₂) (fun x => hCm.1 _) hb₂ heq₂
      (hu₁.of_le one_le_two)]
  congr 1; ext x
  rw [stressField, stressField, hCM, Lin.dcontr_comm]

end Identities

/-! ### Kirchhoff's uniqueness theorem -/

omit [MeasurableSpace E] [BorelSpace E] in
theorem strainField_sub {u₁ u₂ : E → E} {x : E} (h₁ : DifferentiableAt ℝ u₁ x)
    (h₂ : DifferentiableAt ℝ u₂ x) :
    strainField (u₁ - u₂) x = strainField u₁ x - strainField u₂ x := by
  rw [strainField, strainField, strainField, fderiv_sub h₁ h₂, map_sub]

omit [MeasurableSpace E] [BorelSpace E] in
theorem tdiv_sub {σ₁ σ₂ : E → Lin E} {x : E} (h₁ : DifferentiableAt ℝ σ₁ x)
    (h₂ : DifferentiableAt ℝ σ₂ x) : tdiv (σ₁ - σ₂) x = tdiv σ₁ x - tdiv σ₂ x := by
  refine ext_inner_right ℝ fun a => ?_
  rw [inner_sub_left, inner_tdiv (h₁.sub h₂), inner_tdiv h₁, inner_tdiv h₂, vdiv, vdiv, vdiv,
    ← map_sub]
  congr 1
  have d : ∀ {σ : E → Lin E}, DifferentiableAt ℝ σ x →
      DifferentiableAt ℝ (fun y => (σ y)ᵀ a) x := fun hσ =>
    (((ContinuousLinearMap.apply ℝ E a).comp
      (starL' ℝ : Lin E ≃L[ℝ] Lin E).toContinuousLinearMap).differentiableAt).comp x hσ
  rw [← fderiv_sub (d h₁) (d h₂)]
  congr 1; ext y; simp [star_sub]

/-- **Kirchhoff's uniqueness theorem** (homogeneous form): if `ℂ` is positive definite on symmetric
tensors, `u` is a `C²` equilibrium displacement without body force on a connected open body, and
the boundary work density `u · σ(u) n` vanishes `dA`-a.e. (zero displacement or zero traction at
each boundary point), then `u` is an infinitesimal rigid displacement. [Gurtin1981], §33. -/
theorem rigid_of_zero_work (B : DivergenceRegion E) {C : Lin4 E} (hCm : C.HasMinorSymm)
    (hpos : C.PosDefOnSym) (hΩ : IsOpen B.carrier) (hconn : IsPreconnected B.carrier)
    {u : E → E} (hu : ContDiff ℝ 2 u) (heq : ∀ x ∈ B.carrier, tdiv (stressField C u) x = 0)
    (hbdry : ∀ᵐ x ∂B.surface, ⟪u x, stressField C u x (B.normal x)⟫_ℝ = 0) :
    ∃ (a : E) (W : Lin E), W ∈ Skw E ∧ ∀ x ∈ B.carrier, u x = a + W x := by
  -- the strain energy vanishes
  have hwork := work_identity B (contDiff_stressField C hu) (fun x => hCm.1 _) continuous_const
    (fun x hx => by rw [heq x hx, add_zero]) (hu.of_le one_le_two) (b := fun _ => 0)
  rw [integral_eq_zero_of_ae hbdry] at hwork
  simp only [inner_zero_right, integral_zero, add_zero] at hwork
  -- the energy density is a nonnegative continuous function with zero integral
  let g := fun x => stressField C u x ⊡ strainField u x
  have hε : Continuous (strainField u) := (contDiff_strainField hu).continuous
  have hg : Continuous g := by
    let b := stdOrthonormalBasis ℝ E
    have e : g = fun x => ∑ i, ⟪stressField C u x (b i), strainField u x (b i)⟫_ℝ :=
      funext fun x => Lin.dcontr_eq_sum b _ _
    rw [e]
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℝ E (b i)).continuous.comp
        (contDiff_stressField C hu).continuous).inner
        ((ContinuousLinearMap.apply ℝ E (b i)).continuous.comp hε)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    by_cases h : strainField u x = 0
    · simp [g, stressField, h]
    · exact (hpos _ (Lin.sym_mem _) h).le
  have hae : g =ᵐ[volume.restrict B.carrier] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hg0)
      (B.integrableOn_real hg)).mp hwork
  have hzero : EqOn g 0 B.carrier :=
    Measure.eqOn_open_of_ae_eq hae hΩ hg.continuousOn continuousOn_const
  -- hence the strain vanishes, and `u` is rigid
  refine eq_rigid_of_sym_fderiv_eq_zero hΩ hconn hu.contDiffOn fun x hx => ?_
  by_contra h
  have := hpos _ (Lin.sym_mem _) h
  have h0 := hzero hx
  simp only [g, stressField, strainField, Pi.zero_apply] at h0
  linarith

/-- **Kirchhoff's uniqueness theorem**: two `C²` solutions of the mixed problem with the same body
force, whose difference does no work on the boundary, differ by an infinitesimal rigid
displacement. [Gurtin1981], §33. -/
theorem kirchhoff_uniqueness (B : DivergenceRegion E) {C : Lin4 E} (hCm : C.HasMinorSymm)
    (hpos : C.PosDefOnSym) (hΩ : IsOpen B.carrier) (hconn : IsPreconnected B.carrier)
    {u₁ u₂ b : E → E} (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (heq₁ : ∀ x ∈ B.carrier, tdiv (stressField C u₁) x + b x = 0)
    (heq₂ : ∀ x ∈ B.carrier, tdiv (stressField C u₂) x + b x = 0)
    (hbdry : ∀ᵐ x ∂B.surface,
      ⟪(u₁ - u₂) x, stressField C (u₁ - u₂) x (B.normal x)⟫_ℝ = 0) :
    ∃ (a : E) (W : Lin E), W ∈ Skw E ∧ ∀ x ∈ B.carrier, u₁ x - u₂ x = a + W x := by
  have hu : ContDiff ℝ 2 (u₁ - u₂) := hu₁.sub hu₂
  have d₁ : ∀ x, DifferentiableAt ℝ u₁ x := fun x => (hu₁.differentiable (by norm_num)) x
  have d₂ : ∀ x, DifferentiableAt ℝ u₂ x := fun x => (hu₂.differentiable (by norm_num)) x
  have hσ : stressField C (u₁ - u₂) = stressField C u₁ - stressField C u₂ := by
    ext1 x; rw [Pi.sub_apply, stressField, strainField_sub (d₁ x) (d₂ x), map_sub]; rfl
  have heq : ∀ x ∈ B.carrier, tdiv (stressField C (u₁ - u₂)) x = 0 := fun x hx => by
    rw [hσ, tdiv_sub (((contDiff_stressField C hu₁).differentiable one_ne_zero) x)
      (((contDiff_stressField C hu₂).differentiable one_ne_zero) x)]
    rw [sub_eq_zero, eq_neg_of_add_eq_zero_left (heq₁ x hx),
      eq_neg_of_add_eq_zero_left (heq₂ x hx)]
  simpa using rigid_of_zero_work B hCm hpos hΩ hconn hu heq hbdry

end ContinuumMechanics
