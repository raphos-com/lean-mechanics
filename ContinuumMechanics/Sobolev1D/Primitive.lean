import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitives of `L²` functions on an interval

On `(0, L]` let `L² = L²((0, L])`. The **primitive** of `v ∈ L²` is

`(P v)(x) = ∫₀ˣ v = ⟪χ_(0,x], v⟫`,

so `v ↦ (P v)(x)` is a continuous linear functional with `|(P v)(x)| ≤ √L ‖v‖`. The map `P`
identifies `L²` with `{u ∈ H¹(0, L) | u(0) = 0}` normed by `‖u'‖`. This is the model of the Sobolev
space used for the weak formulations of `Sobolev1D` and avoids weak derivatives altogether
([Brezis2011], Thm. 8.2).

## Main results

* `Sobolev1D.prim`, `Sobolev1D.primCLM`: the primitive and its evaluation functionals.
* `Sobolev1D.abs_prim_le`: `|(P v)(x)| ≤ √L ‖v‖` (`H¹ ↪ C`).
* `Sobolev1D.prim_eq_intervalIntegral`, `Sobolev1D.continuousOn_prim`.
* `Sobolev1D.toL2`: continuous functions as elements of `L²`.
* `Sobolev1D.integral_mul_prim`: **Fubini** `∫₀ᴸ f (P w) = ⟪∫_·ᴸ f, w⟫`.

## References

* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §8.2.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace ENNReal

namespace ContinuumMechanics.Sobolev1D

variable (L : ℝ)

/-- Lebesgue measure on `(0, L]`. -/
noncomputable abbrev μ : Measure ℝ := volume.restrict (Ioc 0 L)

/-- `L²((0, L])`. -/
abbrev L2 : Type := Lp ℝ 2 (μ L)

theorem μ_ne_top (s : Set ℝ) : μ L s ≠ ∞ := measure_ne_top _ _

/-- The indicator `χ_(0,x]` as an element of `L²`. -/
noncomputable def chi (x : ℝ) : L2 L :=
  indicatorConstLp 2 (measurableSet_Ioc (a := 0) (b := x)) (μ_ne_top L _) (1 : ℝ)

/-- Evaluation of the primitive at `x` as a continuous linear functional. -/
noncomputable def primCLM (x : ℝ) : L2 L →L[ℝ] ℝ := innerSL ℝ (chi L x)

variable {L}

/-- The **primitive** `(P v)(x) = ∫₀ˣ v`. -/
noncomputable def prim (v : L2 L) (x : ℝ) : ℝ := primCLM L x v

theorem prim_apply (v : L2 L) (x : ℝ) : prim v x = ⟪chi L x, v⟫_ℝ := rfl

theorem prim_eq_setIntegral (v : L2 L) (x : ℝ) : prim v x = ∫ t in Ioc 0 x, v t ∂μ L := by
  rw [prim_apply, chi, L2.inner_indicatorConstLp_one]

theorem integrable (v : L2 L) : Integrable v (μ L) :=
  (Lp.memLp v).integrable one_le_two

theorem prim_eq_intervalIntegral (v : L2 L) {x : ℝ} (hx : x ∈ Icc 0 L) :
    prim v x = ∫ t in (0 : ℝ)..x, v t := by
  rw [prim_eq_setIntegral, integral_of_le hx.1, Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc, max_self, min_eq_left hx.2]

theorem norm_chi_le {x : ℝ} (hL : 0 ≤ L) : ‖chi L x‖ ≤ √L := by
  rw [chi, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul]
  have h : (μ L).real (Ioc 0 x) ≤ L := by
    calc (μ L).real (Ioc 0 x) ≤ (μ L).real univ := measureReal_mono (subset_univ _)
      _ = L := by simp [hL]
  rw [show (1 : ℝ) / (2 : ℝ≥0∞).toReal = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt h

/-- **Sobolev embedding** `H¹ ↪ C`: `|(P v)(x)| ≤ √L ‖v‖`. -/
theorem abs_prim_le (hL : 0 ≤ L) (v : L2 L) (x : ℝ) : |prim v x| ≤ √L * ‖v‖ := by
  rw [prim_apply, ← Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_chi_le hL) (norm_nonneg _))

theorem continuousOn_prim (hL : 0 ≤ L) (v : L2 L) : ContinuousOn (prim v) (Icc 0 L) := by
  have hi : IntegrableOn v (Ioc 0 L) := by
    have := integrable v
    rwa [IntegrableOn]
  have hc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, v t) (Icc 0 L) := by
    have := (intervalIntegral.continuousOn_primitive_interval (a := 0) (b := L)
      (μ := volume) (f := v) (by rwa [uIcc_of_le hL, integrableOn_Icc_iff_integrableOn_Ioc]))
    rwa [uIcc_of_le hL] at this
  exact hc.congr fun x hx => prim_eq_intervalIntegral v hx

/-- **Poincaré inequality** on `H¹` functions vanishing at `0`: `∫₀ᴸ (P v)² ≤ L² ‖v‖²`. -/
theorem poincare (hL : 0 ≤ L) (v : L2 L) :
    ∫ x in (0 : ℝ)..L, prim v x ^ 2 ≤ L ^ 2 * ‖v‖ ^ 2 := by
  have hb : ∀ x ∈ Icc 0 L, prim v x ^ 2 ≤ L * ‖v‖ ^ 2 := fun x _ => by
    have h := abs_prim_le hL v x
    calc prim v x ^ 2 = |prim v x| ^ 2 := (sq_abs _).symm
      _ ≤ (√L * ‖v‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = L * ‖v‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hL]
  calc ∫ x in (0 : ℝ)..L, prim v x ^ 2 ≤ ∫ _x in (0 : ℝ)..L, L * ‖v‖ ^ 2 :=
        intervalIntegral.integral_mono_on hL
          (((continuousOn_prim hL v).pow 2).intervalIntegrable_of_Icc hL)
          intervalIntegrable_const hb
    _ = L ^ 2 * ‖v‖ ^ 2 := by simp; ring

theorem memLp_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : MemLp f 2 (μ L) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := L)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))

/-- A continuous function as an element of `L²((0, L])`. -/
noncomputable def toL2 {f : ℝ → ℝ} (hf : Continuous f) : L2 L := (memLp_of_continuous hf).toLp f

theorem toL2_ae_eq {f : ℝ → ℝ} (hf : Continuous f) : (toL2 (L := L) hf : ℝ → ℝ) =ᵐ[μ L] f :=
  MemLp.coeFn_toLp _

theorem inner_toL2 {f : ℝ → ℝ} (hf : Continuous f) (w : L2 L) :
    ⟪toL2 hf, w⟫_ℝ = ∫ t, f t * w t ∂μ L := by
  rw [L2.inner_def]
  refine integral_congr_ae ((toL2_ae_eq hf).mono fun t ht => ?_)
  simp only [ht]
  simp [mul_comm]

theorem toL2_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    toL2 (L := L) (hf.add hg) = toL2 hf + toL2 hg :=
  MemLp.toLp_add _ _

theorem toL2_smul (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    toL2 (L := L) (hf.const_smul c) = c • toL2 hf :=
  MemLp.toLp_const_smul _ _

theorem prim_toL2 {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (hx : x ∈ Icc 0 L) :
    prim (toL2 (L := L) hf) x = ∫ t in (0 : ℝ)..x, f t := by
  rw [prim_eq_intervalIntegral _ hx]
  refine intervalIntegral.integral_congr_ae ?_
  have := (ae_restrict_iff' measurableSet_Ioc).1 (toL2_ae_eq (L := L) hf)
  filter_upwards [this] with t ht htx
  rw [uIoc_of_le hx.1] at htx
  exact ht ⟨htx.1, htx.2.trans hx.2⟩

/-- The constant function `1` in `L²`. -/
noncomputable def oneL2 : L2 L := toL2 (f := fun _ => (1 : ℝ)) continuous_const

/-- `(P w)(L) = ⟪1, w⟫`. -/
theorem prim_end (w : L2 L) : prim w L = ⟪oneL2 (L := L), w⟫_ℝ := by
  rw [oneL2, inner_toL2, prim_eq_setIntegral, Measure.restrict_restrict measurableSet_Ioc,
    inter_self]
  simp

/-- The primitive as an integral over `(-∞, x]` (the measure lives on `(0, L]`). -/
theorem prim_eq_setIntegral_Iic (v : L2 L) (x : ℝ) : prim v x = ∫ t in Iic x, v t ∂μ L := by
  rw [prim_eq_setIntegral, Measure.restrict_restrict measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext t
  simp only [mem_inter_iff, mem_Ioc, mem_Iic]
  tauto

/-- **Fubini for primitives**: `∫₀ᴸ f (P w) = ∫₀ᴸ (∫_tᴸ f) w(t) dt`. -/
theorem integral_mul_prim {f : ℝ → ℝ} (hf : Continuous f) (w : L2 L) :
    ∫ x, f x * prim w x ∂μ L = ∫ t, (∫ x in Ici t, f x ∂μ L) * w t ∂μ L := by
  have hfi : Integrable f (μ L) := (memLp_of_continuous hf).integrable one_le_two
  set F : ℝ → ℝ → ℝ := fun x t => if t ≤ x then f x * w t else 0
  have hF : Integrable (Function.uncurry F) ((μ L).prod (μ L)) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    have := (hfi.mul_prod (integrable w)).indicator hS
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [indicator, mem_ofPred_eq, Function.uncurry, F]
  have h1 : ∀ x, ∫ t, F x t ∂μ L = f x * prim w x := fun x => by
    rw [prim_eq_setIntegral_Iic, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_indicator measurableSet_Iic]
    rfl
  have h2 : ∀ t, ∫ x, F x t ∂μ L = (∫ x in Ici t, f x ∂μ L) * w t := fun t => by
    rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_indicator measurableSet_Ici]
    rfl
  simp only [← h1, ← h2]
  exact integral_integral_swap hF

theorem setIntegral_Ici_eq {f : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc 0 L) :
    ∫ x in Ici t, f x ∂μ L = ∫ x in t..L, f x := by
  rw [Measure.restrict_restrict measurableSet_Ici, integral_of_le ht.2]
  rcases ht.1.eq_or_lt with h | h
  · subst h
    congr 2
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro h; exact ⟨h.1.le, h⟩
  · rw [show Ici t ∩ Ioc 0 L = Icc t L by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h.trans_le h1, h2⟩]
    exact integral_Icc_eq_integral_Ioc

end ContinuumMechanics.Sobolev1D
