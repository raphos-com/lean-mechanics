import Mathlib.MeasureTheory.Function.Jacobian
import ContinuumMechanics.Stress.BoxRegion

/-!
# Rescaled regions and small boxes

If `P` is a `DivergenceRegion`, so is its image `c + rP` under a homothety (`r > 0`), with surface
measure `r^(d-1)` times the pushed-forward one and the transported normal. Applied to the unit box
of `Stress/BoxRegion`, this gives arbitrarily small boxes around every point, which is exactly the
family of parts the localisation theorems of `Stress/Balance` require. Hence **force balance on
all small boxes in an open body implies `div σ + b = 0`**, with no hypothesis structure left
([Gurtin1981], §14).

## Main results

* `ContinuumMechanics.DivergenceRegion.homothety`: `c + rP`.
* `ContinuumMechanics.smallBoxes`: boxes `c + r·box`, and `exists_smallBox`.
* `ContinuumMechanics.local_equilibrium_of_boxes`: local equilibrium from balance on boxes.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
-/

open MeasureTheory Set Metric Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace DivergenceRegion

/-- The homothety `y ↦ c + r y` as a homeomorphism. -/
noncomputable def homothetyHomeo (c : E) {r : ℝ} (hr : 0 < r) : E ≃ₜ E :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c)

theorem homothetyHomeo_apply (c : E) {r : ℝ} (hr : 0 < r) (y : E) :
    homothetyHomeo c hr y = c + r • y := rfl

theorem hasFDerivAt_homothety (c : E) (r : ℝ) (y : E) :
    HasFDerivAt (fun y : E => c + r • y) (r • ContinuousLinearMap.id ℝ E) y :=
  ((hasFDerivAt_id y).const_smul r).const_add c

theorem det_homothety [FiniteDimensional ℝ E] (r : ℝ) :
    (r • ContinuousLinearMap.id ℝ E).det = r ^ finrank ℝ E := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **rescaled region** `c + rP` (`r > 0`): carrier `c + r P`, surface measure
`r^(d-1) · (c + r ·)_* dA`, normal `n((x - c)/r)`. -/
noncomputable def homothety (P : DivergenceRegion E) (c : E) {r : ℝ} (hr : 0 < r) :
    DivergenceRegion E where
  carrier := (fun y => c + r • y) '' P.carrier
  surface := ENNReal.ofReal (r ^ finrank ℝ E / r) • Measure.map (fun y => c + r • y) P.surface
  normal x := P.normal (r⁻¹ • (x - c))
  measurableSet :=
    (homothetyHomeo c hr).measurableEmbedding.measurableSet_image.2 P.measurableSet
  isCompact_closure := by
    have : (fun y => c + r • y) '' closure P.carrier =
        closure ((fun y => c + r • y) '' P.carrier) :=
      (homothetyHomeo c hr).image_closure P.carrier
    rw [← this]
    exact P.isCompact_closure.image (homothetyHomeo c hr).continuous
  divergence v hv := by
    have hT : MeasurableEmbedding (fun y : E => c + r • y) :=
      (homothetyHomeo c hr).measurableEmbedding
    have hinv : ∀ y : E, r⁻¹ • (c + r • y - c) = y := fun y => by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    -- the pulled-back field `w(y) = v(c + r y)` has `div w = r (div v)(c + r y)`
    set w : E → E := fun y => v (c + r • y)
    have hw : ContDiff ℝ 1 w := hv.comp (contDiff_const.add (contDiff_id.const_smul r))
    have hdw : ∀ y, vdiv w y = r * vdiv v (c + r • y) := fun y => by
      have hd := ((hv.differentiable one_ne_zero) (c + r • y)).hasFDerivAt.comp y
        (hasFDerivAt_homothety c r y)
      rw [vdiv, show w = v ∘ fun y => c + r • y from rfl, hd.fderiv,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, map_smul,
        smul_eq_mul, vdiv]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume P.measurableSet
        (fun y _ => (hasFDerivAt_homothety c r y).hasFDerivWithinAt)
        (homothetyHomeo c hr).injective.injOn,
      integral_smul_measure, hT.integral_map]
    simp only [det_homothety, hinv, abs_of_pos (pow_pos hr _), smul_eq_mul]
    have e : ∀ y, r ^ finrank ℝ E * vdiv v (c + r • y) = r ^ finrank ℝ E / r * vdiv w y :=
      fun y => by rw [hdw]; field_simp
    simp only [e]
    rw [integral_const_mul, P.divergence w hw, ENNReal.toReal_ofReal (by positivity),
      ← smul_eq_mul, ← integral_smul]
  integrable_traction σ hσ := by
    have hT : MeasurableEmbedding (fun y : E => c + r • y) :=
      (homothetyHomeo c hr).measurableEmbedding
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [hT.integrable_map_iff]
    have := P.integrable_traction (fun y => σ (c + r • y))
      (hσ.comp (continuous_const.add (continuous_const.smul continuous_id)))
    simpa [Function.comp_def, inv_smul_smul₀ hr.ne'] using this

theorem isOpen_homothety_carrier (P : DivergenceRegion E) (hP : IsOpen P.carrier) (c : E) {r : ℝ}
    (hr : 0 < r) : IsOpen (P.homothety c hr).carrier :=
  (homothetyHomeo c hr).isOpenMap _ hP

end DivergenceRegion

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin (n + 1)) ℝ E)

/-- The **small boxes** `c + r·box` (`r > 0`) of an orthonormal basis `e`. -/
noncomputable def smallBoxes : Set (DivergenceRegion E) :=
  range fun p : E × {r : ℝ // 0 < r} => (boxRegion e).homothety p.1 p.2.2

theorem isOpen_boxRegion_carrier : IsOpen (boxRegion e).carrier :=
  (BoxRegion.coord e).toHomeomorph.isOpenMap _ (BoxRegion.isOpen_openCube _)

/-- Every point of an open set has arbitrarily small boxes of positive volume around it inside the
set. -/
theorem exists_smallBox {Ω : Set E} (hΩ : IsOpen Ω) :
    ∀ x ∈ Ω, ∀ ε > 0, ∃ P ∈ smallBoxes e, P.carrier ⊆ Ω ∩ ball x ε ∧ 0 < volume P.carrier := by
  intro x hx ε hε
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨K, hK⟩ := (boxRegion e).isCompact_closure.isBounded.subset_closedBall 0
  set ρ := min δ ε
  have hρ : 0 < ρ := lt_min hδ hε
  set r := ρ / (2 * (|K| + 1))
  have hr : 0 < r := by positivity
  refine ⟨(boxRegion e).homothety x hr, ⟨(x, ⟨r, hr⟩), rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : ‖y‖ ≤ |K| := by
      have := hK (subset_closure hy)
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self K)
    have hlt : ‖r • y‖ < ρ := by
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      calc r * ‖y‖ ≤ r * |K| := mul_le_mul_of_nonneg_left hy' hr.le
        _ < ρ := by
          simp only [r]
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg K]
    have hmem : x + r • y ∈ ball x ρ := by
      rw [mem_ball, dist_self_add_left]; exact hlt
    exact ⟨hδΩ (ball_subset_ball (min_le_left _ _) hmem),
      ball_subset_ball (min_le_right _ _) hmem⟩
  · refine ((boxRegion e).isOpen_homothety_carrier (isOpen_boxRegion_carrier e) x hr).measure_pos
      volume ?_
    refine ⟨x + r • BoxRegion.coord e (fun _ => 2⁻¹), _, ⟨fun _ => 2⁻¹, ?_, rfl⟩, rfl⟩
    intro i _
    norm_num

/-- **Local equilibrium from balance on small boxes**: if the forces on every small box inside an
open body balance, then `div σ + b = 0` there. No hypothesis structure is involved.
[Gurtin1981], §14. -/
theorem local_equilibrium_of_boxes {Ω : Set E} (hΩ : IsOpen Ω) {σ : E → Lin E}
    (hσ : ContDiff ℝ 1 σ) {f : E → E} (hf : Continuous f)
    (hbal : ∀ P ∈ smallBoxes e, P.carrier ⊆ Ω →
      (∫ x, σ x (P.normal x) ∂P.surface) + ∫ x in P.carrier, f x = 0) :
    ∀ x ∈ Ω, tdiv σ x + f x = 0 :=
  local_equilibrium (smallBoxes e) (exists_smallBox e hΩ) hσ hf hbal

/-- **Symmetry of the Cauchy stress from moment balance on small boxes.** [Gurtin1981], §14. -/
theorem symmetric_of_moment_balance_of_boxes {Ω : Set E} (hΩ : IsOpen Ω) {σ : E → Lin E}
    (hσ : ContDiff ℝ 1 σ) {f : E → E} (hf : Continuous f)
    (hbal : ∀ P ∈ smallBoxes e, P.carrier ⊆ Ω →
      (∫ x, σ x (P.normal x) ∂P.surface) + ∫ x in P.carrier, f x = 0)
    (hmom : ∀ P ∈ smallBoxes e, P.carrier ⊆ Ω → ∀ W ∈ Skw E,
      (∫ x, ⟪W x, σ x (P.normal x)⟫_ℝ ∂P.surface) + ∫ x in P.carrier, ⟪W x, f x⟫_ℝ = 0) :
    ∀ x ∈ Ω, σ x ∈ Sym E :=
  symmetric_of_moment_balance (smallBoxes e) (exists_smallBox e hΩ) hσ hf hbal hmom

end ContinuumMechanics
