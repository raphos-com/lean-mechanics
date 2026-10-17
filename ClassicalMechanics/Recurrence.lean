import ClassicalMechanics.LiouvilleFlow
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Poincaré recurrence for Hamiltonian flows

We connect Liouville's theorem (`PhaseFlow.measure_image`, `hamiltonian_volume`) with Mathlib's
measure-theoretic **Poincaré recurrence theorem**
(`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`).

* **Abstract setting** (`measurePreserving_restrict_of_image`): a measurable map `f` with
  `f '' D = D` that preserves the measure of measurable subsets of `D` (in the sense
  `μ (f '' B) = μ B`) is measure preserving for `μ.restrict D`. If `μ D < ∞` it is therefore
  conservative, and (`ae_frequently_iterate_mem`) almost every point of a measurable `A ⊆ D`
  returns to `A` infinitely often under the iterates of `f`.
* **Flows** (`iterate_eq_flow`, `ae_frequently_flow_mem`): for a flow `Φ` with `Φ 0 = id` and the
  group property `Φ (s + t) = Φ s ∘ Φ t`, the iterates of the time-`T` map are `Φ (n T)`, so a
  recurrence for `Φ T` yields arbitrarily large return times `t` with `Φ t x ∈ A`.
* **Divergence-free flows** (`PhaseFlow.ae_frequently_mem`): for a `PhaseFlow` of a
  divergence-free field with the group property, every `Φ t` is injective (with inverse
  `Φ (-t)`), so Liouville's theorem applies; an invariant region (`Φ t` maps `D` into `D` for
  all `t`) of finite Haar measure is then a recurrent region.
* **Hamiltonian flows** (`hamiltonian_recurrence`, `hamiltonian_recurrence_flow`): any measurable
  subset of a bounded measurable invariant region of phase space (e.g. a bounded energy shell
  `{E₁ ≤ H ≤ E₂}`) recurs, for the discrete time-`T` map and along the continuous flow.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §16.
* [Poincare1890] H. Poincaré, *Sur le problème des trois corps et les équations de la
  dynamique*, Acta Math. 13 (1890).
-/

open MeasureTheory Filter Set

noncomputable section

namespace ClassicalMechanics

/-! ### Abstract recurrence for measure-preserving maps of an invariant region -/

section Abstract

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {D : Set α}

/-- A measurable map `f` with `f '' D = D` that preserves the measure of every measurable subset
of `D` (`μ (f '' B) = μ B`) is measure preserving for the restricted measure `μ.restrict D`. -/
theorem measurePreserving_restrict_of_image (hf : Measurable f) (hfD : f '' D = D)
    (hvol : ∀ B ⊆ D, MeasurableSet B → μ (f '' B) = μ B) (hD : MeasurableSet D) :
    MeasurePreserving f (μ.restrict D) (μ.restrict D) := by
  refine ⟨hf, Measure.ext fun S hS => ?_⟩
  rw [Measure.map_apply hf hS, Measure.restrict_apply (hf hS), Measure.restrict_apply hS]
  calc μ (f ⁻¹' S ∩ D) = μ (f '' (f ⁻¹' S ∩ D)) :=
        (hvol _ inter_subset_right ((hf hS).inter hD)).symm
    _ = μ (S ∩ D) := by rw [image_preimage_inter, hfD]

/-- Under the hypotheses of `measurePreserving_restrict_of_image`, if `D` has finite measure then
`f` is **conservative** for `μ.restrict D`. -/
theorem conservative_restrict_of_image (hf : Measurable f) (hfD : f '' D = D)
    (hvol : ∀ B ⊆ D, MeasurableSet B → μ (f '' B) = μ B) (hD : MeasurableSet D)
    (hfin : μ D ≠ ⊤) : Conservative f (μ.restrict D) := by
  have : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  exact (measurePreserving_restrict_of_image hf hfD hvol hD).conservative

/-- **Poincaré recurrence** for a measure-preserving map of an invariant region `D` of finite
measure: almost every point of a measurable `A ⊆ D` returns to `A` infinitely often. -/
theorem ae_frequently_iterate_mem (hf : Measurable f) (hfD : f '' D = D)
    (hvol : ∀ B ⊆ D, MeasurableSet B → μ (f '' B) = μ B) (hD : MeasurableSet D)
    (hfin : μ D ≠ ⊤) {A : Set α} (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ n in atTop, f^[n] x ∈ A := by
  have h := (conservative_restrict_of_image hf hfD hvol hD hfin).ae_mem_imp_frequently_image_mem
    hA.nullMeasurableSet
  rw [ae_restrict_iff' hD] at h
  filter_upwards [h] with x hx hxA using hx (hAD hxA) hxA

end Abstract

/-! ### Flows with the group property -/

section Flow

variable {α : Type*} {Φ : ℝ → α → α}

/-- For a flow with `Φ 0 = id` and `Φ (s + t) = Φ s ∘ Φ t`, the `n`-th iterate of the time-`T`
map is the time-`n T` map. -/
theorem iterate_eq_flow (h0 : ∀ z, Φ 0 z = z) (hgroup : ∀ s t, Φ (s + t) = Φ s ∘ Φ t)
    (T : ℝ) (n : ℕ) : (Φ T)^[n] = Φ (n * T) := by
  induction n with
  | zero => simp only [Function.iterate_zero, Nat.cast_zero, zero_mul]; exact (funext h0).symm
  | succ n ih =>
    rw [Function.iterate_succ', ih, show ((n + 1 : ℕ) : ℝ) * T = T + n * T by push_cast; ring,
      hgroup]

/-- A flow with the group property has injective time-`t` maps (with inverse `Φ (-t)`). -/
theorem injective_flow (h0 : ∀ z, Φ 0 z = z) (hgroup : ∀ s t, Φ (s + t) = Φ s ∘ Φ t) (t : ℝ) :
    Function.Injective (Φ t) := by
  have h : Φ (-t) ∘ Φ t = id := by rw [← hgroup, neg_add_cancel]; exact funext h0
  exact Function.LeftInverse.injective (g := Φ (-t)) (congrFun h)

/-- For a flow with the group property, a region mapped into itself by every `Φ t` is exactly
invariant: `Φ t '' D = D`. -/
theorem image_flow_eq (h0 : ∀ z, Φ 0 z = z) (hgroup : ∀ s t, Φ (s + t) = Φ s ∘ Φ t)
    {D : Set α} (hinv : ∀ t, MapsTo (Φ t) D D) (t : ℝ) : Φ t '' D = D := by
  refine (hinv t).image_subset.antisymm fun z hz => ⟨Φ (-t) z, hinv (-t) hz, ?_⟩
  rw [← Function.comp_apply (f := Φ t), ← hgroup, add_neg_cancel, h0]

/-- From discrete recurrence to recurrence along the flow: if `x` returns to `A` infinitely often
under the time-`T` map (`T > 0`), then there are arbitrarily large times `t` with `Φ t x ∈ A`. -/
theorem frequently_flow_mem_of_iterate (h0 : ∀ z, Φ 0 z = z)
    (hgroup : ∀ s t, Φ (s + t) = Φ s ∘ Φ t) {T : ℝ} (hT : 0 < T) {A : Set α} {x : α}
    (hx : ∃ᶠ n in atTop, (Φ T)^[n] x ∈ A) : ∃ᶠ t in atTop, Φ t x ∈ A := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * T) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hT
  exact hlim.frequently (p := fun t => Φ t x ∈ A) (by simpa [iterate_eq_flow h0 hgroup] using hx)

variable [MeasurableSpace α] {μ : Measure α}

/-- **Poincaré recurrence along a flow**: if the time-`T` map (`T > 0`) is measurable and
preserves the measure of measurable subsets of an invariant region `D` of finite measure, then
for almost every `x ∈ A` (`A ⊆ D` measurable) there are arbitrarily large `t` with `Φ t x ∈ A`. -/
theorem ae_frequently_flow_mem (h0 : ∀ z, Φ 0 z = z) (hgroup : ∀ s t, Φ (s + t) = Φ s ∘ Φ t)
    {T : ℝ} (hT : 0 < T) (hf : Measurable (Φ T)) {D : Set α} (hfD : Φ T '' D = D)
    (hvol : ∀ B ⊆ D, MeasurableSet B → μ (Φ T '' B) = μ B) (hD : MeasurableSet D)
    (hfin : μ D ≠ ⊤) {A : Set α} (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ t in atTop, Φ t x ∈ A := by
  filter_upwards [ae_frequently_iterate_mem hf hfD hvol hD hfin hA hAD] with x hx hxA
  exact frequently_flow_mem_of_iterate h0 hgroup hT (hx hxA)

end Flow

/-! ### Divergence-free phase flows -/

namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {X : E → E} (φ : PhaseFlow X)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The time-`t` map of a phase flow is continuous. -/
theorem continuous_Φ (t : ℝ) : Continuous (φ.Φ t) := (φ.differentiable_Φ t).continuous

/-- **Volume preservation on an invariant region**: for a divergence-free field whose flow has
the group property, the time-`T` map is measure preserving for `μ.restrict D` whenever `D` is a
measurable region with `Φ t` mapping `D` into `D` for all `t`. -/
theorem measurePreserving_restrict (μ : Measure E) [μ.IsAddHaarMeasure]
    (hX : Differentiable ℝ X) (hdiv : ∀ x, divergence X x = 0)
    (hgroup : ∀ s t, φ.Φ (s + t) = φ.Φ s ∘ φ.Φ t) {D : Set E} (hD : MeasurableSet D)
    (hinv : ∀ t, MapsTo (φ.Φ t) D D) (T : ℝ) :
    MeasurePreserving (φ.Φ T) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_of_image (φ.continuous_Φ T).measurable
    (image_flow_eq φ.zero hgroup hinv T)
    (fun _ _ hB => φ.measure_image μ hX hdiv T hB (injective_flow φ.zero hgroup T).injOn) hD

/-- **Poincaré recurrence for divergence-free flows** (time-`T` map): let `D` be a measurable
invariant region of finite Haar measure. Then almost every point of a measurable `A ⊆ D`
returns to `A` infinitely often under the iterates of `Φ T`. -/
theorem ae_frequently_mem (μ : Measure E) [μ.IsAddHaarMeasure]
    (hX : Differentiable ℝ X) (hdiv : ∀ x, divergence X x = 0)
    (hgroup : ∀ s t, φ.Φ (s + t) = φ.Φ s ∘ φ.Φ t) {D : Set E} (hD : MeasurableSet D)
    (hinv : ∀ t, MapsTo (φ.Φ t) D D) (hfin : μ D ≠ ⊤) (T : ℝ) {A : Set E}
    (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ n in atTop, (φ.Φ T)^[n] x ∈ A :=
  ae_frequently_iterate_mem (φ.continuous_Φ T).measurable (image_flow_eq φ.zero hgroup hinv T)
    (fun _ _ hB => φ.measure_image μ hX hdiv T hB (injective_flow φ.zero hgroup T).injOn) hD
    hfin hA hAD

/-- **Poincaré recurrence for divergence-free flows** (continuous time): for almost every point
`x` of a measurable subset `A` of a measurable invariant region `D` of finite Haar measure, there
are arbitrarily large times `t` with `Φ t x ∈ A`. -/
theorem ae_frequently_flow_mem_of_divergence_free (μ : Measure E) [μ.IsAddHaarMeasure]
    (hX : Differentiable ℝ X) (hdiv : ∀ x, divergence X x = 0)
    (hgroup : ∀ s t, φ.Φ (s + t) = φ.Φ s ∘ φ.Φ t) {D : Set E} (hD : MeasurableSet D)
    (hinv : ∀ t, MapsTo (φ.Φ t) D D) (hfin : μ D ≠ ⊤) {A : Set E}
    (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ t in atTop, φ.Φ t x ∈ A := by
  filter_upwards [φ.ae_frequently_mem μ hX hdiv hgroup hD hinv hfin 1 hA hAD] with x hx hxA
  exact frequently_flow_mem_of_iterate φ.zero hgroup one_pos (hx hxA)

end PhaseFlow

/-! ### Hamiltonian flows -/

section Hamiltonian

variable {n : ℕ} {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

/-- A bounded subset of phase space `ℝⁿ × ℝⁿ` has finite volume. -/
theorem volume_ne_top_of_isBounded {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hb : Bornology.IsBounded D) : volume D ≠ ⊤ := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℝ))
    (volume : Measure (Fin n → ℝ))
  exact hb.measure_lt_top.ne

variable (hH : ContDiff ℝ 2 H)
include hH

/-- **Poincaré recurrence for Hamiltonian flows**: let `φ` be a `C²` flow of a `C²` Hamiltonian
with the group property `Φ (s + t) = Φ s ∘ Φ t`, and let `D` be a bounded measurable region of
phase space invariant under the flow (e.g. a bounded energy shell `{E₁ ≤ H ≤ E₂}`). Then for any
`T`, almost every point of a measurable `A ⊆ D` returns to `A` infinitely often under `Φ T`. -/
theorem hamiltonian_recurrence (φ : PhaseFlow (hamField H))
    (hgroup : ∀ s t, φ.Φ (s + t) = φ.Φ s ∘ φ.Φ t) {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) (hinv : ∀ t, MapsTo (φ.Φ t) D D)
    (T : ℝ) {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂volume, x ∈ A → ∃ᶠ k in atTop, (φ.Φ T)^[k] x ∈ A :=
  ae_frequently_iterate_mem (φ.continuous_Φ T).measurable (image_flow_eq φ.zero hgroup hinv T)
    (fun _ _ hB => hamiltonian_volume hH φ T hB (injective_flow φ.zero hgroup T).injOn) hD
    (volume_ne_top_of_isBounded hb) hA hAD

/-- **Poincaré recurrence for Hamiltonian flows** (continuous time): under the hypotheses of
`hamiltonian_recurrence`, for almost every `x ∈ A` there are arbitrarily large times `t` with
`Φ t x ∈ A`. -/
theorem hamiltonian_recurrence_flow (φ : PhaseFlow (hamField H))
    (hgroup : ∀ s t, φ.Φ (s + t) = φ.Φ s ∘ φ.Φ t) {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) (hinv : ∀ t, MapsTo (φ.Φ t) D D)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA : MeasurableSet A) (hAD : A ⊆ D) :
    ∀ᵐ x ∂volume, x ∈ A → ∃ᶠ t in atTop, φ.Φ t x ∈ A := by
  filter_upwards [hamiltonian_recurrence hH φ hgroup hD hb hinv 1 hA hAD] with x hx hxA
  exact frequently_flow_mem_of_iterate φ.zero hgroup one_pos (hx hxA)

end Hamiltonian

end ClassicalMechanics
