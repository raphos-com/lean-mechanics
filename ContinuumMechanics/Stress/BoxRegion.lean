import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import ContinuumMechanics.Stress.Balance

/-!
# Boxes satisfy the divergence theorem

`DivergenceRegion` packages the divergence theorem as a hypothesis (see `docs/GAPS.md`). This file
shows
that it is not vacuous: every **coordinate box** `{x | 0 < x · eᵢ < 1}` of an orthonormal basis
`e` is a `DivergenceRegion`. The surface measure is the sum of the Lebesgue measures of the
(open) faces, the outer normal is `±eᵢ` on the faces, and the divergence theorem is transferred
from Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` on
`[0,1]ⁿ⁺¹ ⊆ ℝⁿ⁺¹` ([Gurtin1981], §4).

## Main results

* `ContinuumMechanics.boxRegion`: the unit box of an orthonormal basis as a `DivergenceRegion`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §4.
-/

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E)

namespace BoxRegion

/-- Cartesian coordinates `ℝⁿ⁺¹ ≃ E` of the orthonormal basis `b`. -/
noncomputable def coord : (Fin (n + 1) → ℝ) ≃L[ℝ] E :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.trans
    b.repr.symm.toContinuousLinearEquiv

theorem inner_coord (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ⟪coord b y, b i⟫_ℝ = y i := by
  rw [real_inner_comm, ← b.repr_apply_apply]
  simp [coord]

theorem coord_symm_apply (x : E) (i : Fin (n + 1)) : (coord b).symm x i = ⟪b i, x⟫_ℝ := by
  rw [← b.repr_apply_apply]
  simp [coord]

theorem coord_single (i : Fin (n + 1)) : coord b (Pi.single i 1) = b i := by
  apply b.repr.injective
  ext j
  rw [b.repr_self]
  simp [coord]

/-- The open unit cube `(0,1)ᵏ`. -/
def openCube (k : ℕ) : Set (Fin k → ℝ) := pi univ fun _ => Ioo 0 1

theorem isOpen_openCube (k : ℕ) : IsOpen (openCube k) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem openCube_subset_Icc (k : ℕ) : openCube k ⊆ Icc 0 1 := fun y hy => by
  simp only [openCube, mem_pi, mem_univ, true_implies, mem_Ioo] at hy
  exact ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩

theorem openCube_ae_eq (k : ℕ) : openCube k =ᵐ[volume] Icc (0 : Fin k → ℝ) 1 := by
  rw [volume_pi]
  simpa [openCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin k => (volume : Measure ℝ)) (f := 0) (g := 1))

/-- The face `x · eᵢ = c` of the box, parametrised by `(0,1)ⁿ`. -/
noncomputable def faceMap (c : ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) : E :=
  coord b (Fin.insertNth i c y)

theorem continuous_faceMap (c : ℝ) (i : Fin (n + 1)) : Continuous (faceMap b c i) :=
  (coord b).continuous.comp (Continuous.finInsertNth i continuous_const continuous_id)

theorem measurableEmbedding_faceMap [MeasurableSpace E] [BorelSpace E] (c : ℝ) (i : Fin (n + 1)) :
    MeasurableEmbedding (faceMap b c i) := by
  refine (Function.LeftInverse.isClosedEmbedding (f := fun x => (coord b).symm x ∘ i.succAbove)
    (fun y => ?_) ?_ (continuous_faceMap b c i)).measurableEmbedding
  · funext k; simp [faceMap]
  · exact continuous_pi fun k => (continuous_apply _).comp (coord b).symm.continuous

/-- The outer unit normal: `eᵢ` where `x · eᵢ = 1`, `-eᵢ` where `x · eᵢ = 0`. -/
noncomputable def normal (x : E) : E :=
  ∑ j, (if ⟪x, b j⟫_ℝ = 1 then (1 : ℝ) else if ⟪x, b j⟫_ℝ = 0 then -1 else 0) • b j

theorem normal_faceMap {c : ℝ} (hc : c = 0 ∨ c = 1) (i : Fin (n + 1)) {y : Fin n → ℝ}
    (hy : y ∈ openCube n) :
    normal b (faceMap b c i y) = (if c = 1 then (1 : ℝ) else -1) • b i := by
  rw [normal, Finset.sum_eq_single i]
  · simp only [faceMap, inner_coord, Fin.insertNth_apply_same]
    rcases hc with rfl | rfl <;> simp
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    have hk := hy k (mem_univ k)
    simp only [faceMap, inner_coord, Fin.insertNth_apply_succAbove]
    simp [hk.2.ne, hk.1.ne']
  · simp

variable [MeasurableSpace E] [BorelSpace E]

/-- The surface measure of the box: Lebesgue measure on each of its `2(n+1)` open faces. -/
noncomputable def surface : Measure E :=
  ∑ i, (Measure.map (faceMap b 1 i) (volume.restrict (openCube n)) +
    Measure.map (faceMap b 0 i) (volume.restrict (openCube n)))

theorem face_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (h : E → E → G) (hh : ∀ m, Continuous fun x => h x m) {c : ℝ} (hc : c = 0 ∨ c = 1)
    (i : Fin (n + 1)) :
    Integrable (fun x => h x (normal b x))
        (Measure.map (faceMap b c i) (volume.restrict (openCube n))) ∧
      ∫ x, h x (normal b x) ∂Measure.map (faceMap b c i) (volume.restrict (openCube n)) =
        ∫ y in Icc 0 1, h (faceMap b c i y) ((if c = 1 then (1 : ℝ) else -1) • b i) := by
  have he := measurableEmbedding_faceMap b c i
  have hms : MeasurableSet (openCube n) := (isOpen_openCube n).measurableSet
  have heq : EqOn (fun y => h (faceMap b c i y) ((if c = 1 then (1 : ℝ) else -1) • b i))
      (fun y => h (faceMap b c i y) (normal b (faceMap b c i y))) (openCube n) := fun y hy => by
    simp only [normal_faceMap b hc i hy]
  have hcont : Continuous fun y => h (faceMap b c i y) ((if c = 1 then (1 : ℝ) else -1) • b i) :=
    (hh _).comp (continuous_faceMap b c i)
  refine ⟨?_, ?_⟩
  · rw [he.integrable_map_iff]
    exact ((hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (openCube_subset_Icc n)).congr_fun heq hms
  · rw [he.integral_map, ← setIntegral_congr_set (openCube_ae_eq n)]
    exact (setIntegral_congr_fun hms heq).symm

/-- Integrals over the surface of the box are sums of face integrals. -/
theorem surface_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (h : E → E → G) (hh : ∀ m, Continuous fun x => h x m) :
    Integrable (fun x => h x (normal b x)) (surface b) ∧
      ∫ x, h x (normal b x) ∂surface b =
        ∑ i, ((∫ y in Icc 0 1, h (faceMap b 1 i y) (b i)) +
          ∫ y in Icc 0 1, h (faceMap b 0 i y) (-b i)) := by
  have h1 := face_integral b h hh (Or.inr rfl)
  have h0 := face_integral b h hh (Or.inl rfl)
  refine ⟨integrable_finsetSum_measure.2 fun i _ => (h1 i).1.add_measure (h0 i).1, ?_⟩
  rw [surface, integral_finsetSum_measure fun i _ => (h1 i).1.add_measure (h0 i).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add_measure (h1 i).1 (h0 i).1, (h1 i).2, (h0 i).2]
  simp

variable [FiniteDimensional ℝ E]

theorem measurePreserving_coord : MeasurePreserving (coord b) volume volume :=
  (b.measurePreserving_repr_symm).comp (PiLp.volume_preserving_toLp _)

/-- **Divergence theorem on the box**. -/
theorem divergence {v : E → E} (hv : ContDiff ℝ 1 v) :
    ∫ x in coord b '' openCube (n + 1), vdiv v x = ∫ x, ⟪v x, normal b x⟫_ℝ ∂surface b := by
  -- pull the volume integral back to `[0,1]ⁿ⁺¹`
  rw [(measurePreserving_coord b).setIntegral_image_emb
      (coord b).toHomeomorph.measurableEmbedding,
    setIntegral_congr_set (openCube_ae_eq (n + 1)),
    (surface_integral b (fun x m => ⟪v x, m⟫_ℝ) fun m => hv.continuous.inner continuous_const).2]
  -- the field in coordinates
  let f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun y => (coord b).symm (v (coord b y))
  let f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ := fun y =>
    ((coord b).symm : E →L[ℝ] Fin (n + 1) → ℝ).comp
      ((fderiv ℝ v (coord b y)).comp (coord b : (Fin (n + 1) → ℝ) →L[ℝ] E))
  have hd : ∀ y, HasFDerivAt f (f' y) y := fun y =>
    (coord b).symm.hasFDerivAt.comp y
      (((hv.differentiable one_ne_zero) _).hasFDerivAt.comp y (coord b).hasFDerivAt)
  have hdiv : ∀ y, ∑ i, f' y (Pi.single i 1) i = vdiv v (coord b y) := fun y => by
    rw [vdiv, Lin.tr_eq_sum_inner b]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f', coord_symm_apply, coord_single]
  have hdt := integral_divergence_of_hasFDerivAt_off_countable 0 1 zero_le_one f f' ∅
    countable_empty (fun y _ => (hd y).continuousAt.continuousWithinAt)
    (fun y _ => hd y) (by
      simp only [hdiv]
      exact (continuous_vdiv hv).comp (coord b).continuous |>.continuousOn.integrableOn_compact
        isCompact_Icc)
  simp only [hdiv] at hdt
  rw [hdt]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [f, coord_symm_apply, Pi.zero_comp, Pi.one_comp, Pi.zero_apply, Pi.one_apply,
    faceMap, inner_neg_right, integral_neg, real_inner_comm (b i)]
  ring

end BoxRegion

open BoxRegion in
/-- The unit box `{x | 0 < x · eᵢ < 1}` of an orthonormal basis is a `DivergenceRegion`: the
hypothesis structure of `Stress/Balance` is satisfiable. -/
noncomputable def boxRegion [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    DivergenceRegion E where
  carrier := coord b '' openCube (n + 1)
  surface := surface b
  normal := normal b
  measurableSet := ((coord b).toHomeomorph.isOpenMap _ (isOpen_openCube _)).measurableSet
  isCompact_closure :=
    (isCompact_Icc.image (coord b).continuous).of_isClosed_subset isClosed_closure
      (closure_minimal (image_mono (openCube_subset_Icc _))
        (isCompact_Icc.image (coord b).continuous).isClosed)
  divergence := fun _ hv => divergence b hv
  integrable_traction := fun σ hσ =>
    (surface_integral b (fun x m => σ x m) fun m =>
      (ContinuousLinearMap.apply ℝ E m).continuous.comp hσ).1


end ContinuumMechanics
