import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual
import ContinuumMechanics.Sobolev1D.Primitive
import ContinuumMechanics.Beams.Bar

/-!
# Weak formulation of the axial bar

In the model `u = P v` (`v = u' ∈ L²`, see `Sobolev1D.Primitive`), the virtual-work (weak) form
of `EA u'' + f = 0` is

`EA ⟪v, w⟫ = ∫₀ᴸ f (P w) + P (P w)(L)`  for all `w`    (fixed–free, end load `P`),
`EA ⟪v, w⟫ = ∫₀ᴸ f (P w)`  for all `w` with `(P w)(L) = 0`  (fixed–fixed, on the closed subspace
`H¹₀ = {v | (P v)(L) = 0}`).

Both are **well posed** by the Lax–Milgram theorem (the energy form `EA ⟪·, ·⟫` is coercive), and a
classical `C²` solution is the weak solution ([Reddy2007], §3.2; [Brezis2011], §8.4).

## Main results

* `Sobolev1D.existsUnique_weak`: Lax–Milgram for `EA ⟪v, w⟫ = ℓ(w)`.
* `Beams.Bar.weakFixedFree_existsUnique`, `Beams.Bar.weakFixedFixed_existsUnique`.
* `Beams.Bar.weakFixedFree_of_classical`, `Beams.Bar.weakFixedFixed_of_classical`: classical
  solutions are weak solutions, and `P u' = u`.

## References

* [Reddy2007] J. N. Reddy, *An Introduction to the Finite Element Method*, §3.2.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §8.4.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace

namespace ContinuumMechanics

namespace Sobolev1D

/-- **Lax–Milgram** for the energy form `EA ⟪v, w⟫` (`EA > 0`): for every continuous linear load
`ℓ` there is exactly one `v` with `EA ⟪v, w⟫ = ℓ(w)` for all `w`. [Brezis2011], Cor. 5.8. -/
theorem existsUnique_weak {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {k : ℝ} (hk : 0 < k) (ℓ : V →L[ℝ] ℝ) :
    ∃! v : V, ∀ w, k * ⟪v, w⟫_ℝ = ℓ w := by
  set B : V →L[ℝ] V →L[ℝ] ℝ := k • innerSL ℝ
  have hB : ∀ v w, B v w = k * ⟪v, w⟫_ℝ := fun v w => by
    rw [show B v w = k * innerSL ℝ v w from rfl, innerSL_apply_apply]
  have hc : IsCoercive B := ⟨k, hk, fun u => by
    rw [hB, real_inner_self_eq_norm_mul_norm, mul_assoc]⟩
  set g := (InnerProductSpace.toDual ℝ V).symm ℓ
  have hg : ∀ w, ⟪g, w⟫_ℝ = ℓ w := fun w => InnerProductSpace.toDual_symm_apply
  refine ⟨hc.continuousLinearEquivOfBilin.symm g, fun w => ?_, fun v hv => ?_⟩
  · rw [← hB, ← hc.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hg]
  · have := hc.unique_continuousLinearEquivOfBilin (v := v) (f := g) fun w => by rw [hg, hB, hv]
    rw [this, ContinuousLinearEquiv.symm_apply_apply]

end Sobolev1D

namespace Beams.Bar

open Sobolev1D

variable (b : Bar)

/-- The load functional `w ↦ ∫₀ᴸ f (P w) + P (P w)(L)`. -/
noncomputable def load (f : ℝ → ℝ) (P : ℝ) (w : L2 b.L) : ℝ :=
  (∫ x, f x * prim w x ∂μ b.L) + P * prim w b.L

/-- The resultant `t ↦ ∫_tᴸ f`. -/
noncomputable def resultant (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in t..b.L, f x

theorem continuous_resultant {f : ℝ → ℝ} (hf : Continuous f) : Continuous (b.resultant f) := by
  have : b.resultant f = fun t => -∫ x in b.L..t, f x := funext fun t => integral_symm _ _
  rw [this]
  exact (continuous_primitive (fun _ _ => hf.intervalIntegrable _ _) _).neg

/-- `∫₀ᴸ f (P w) = ⟪∫_·ᴸ f, w⟫`: the distributed load is represented by its resultant. -/
theorem integral_mul_prim_eq {f : ℝ → ℝ} (hf : Continuous f) (w : L2 b.L) :
    ∫ x, f x * prim w x ∂μ b.L = ⟪toL2 (b.continuous_resultant hf), w⟫_ℝ := by
  rw [integral_mul_prim hf, inner_toL2]
  refine integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  change (∫ x in Ici t, f x ∂μ b.L) * w t = b.resultant f t * w t
  rw [setIntegral_Ici_eq (Ioc_subset_Icc_self ht), resultant]

/-- The load functional is continuous and linear. -/
noncomputable def loadCLM (f : ℝ → ℝ) (hf : Continuous f) (P : ℝ) : L2 b.L →L[ℝ] ℝ :=
  innerSL ℝ (toL2 (b.continuous_resultant hf) + P • oneL2)

theorem loadCLM_apply {f : ℝ → ℝ} (hf : Continuous f) (P : ℝ) (w : L2 b.L) :
    b.loadCLM f hf P w = b.load f P w := by
  simp only [loadCLM, innerSL_apply_apply, inner_add_left, real_inner_smul_left, load,
    b.integral_mul_prim_eq hf, prim_end]

/-- The **weak form** of the fixed–free bar with end load `P`. -/
def WeakFixedFree (f : ℝ → ℝ) (P : ℝ) (v : L2 b.L) : Prop :=
  ∀ w : L2 b.L, b.EA * ⟪v, w⟫_ℝ = b.load f P w

/-- **Well-posedness** of the fixed–free bar (Lax–Milgram). -/
theorem weakFixedFree_existsUnique {f : ℝ → ℝ} (hf : Continuous f) (P : ℝ) :
    ∃! v, b.WeakFixedFree f P v := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_weak b.EA_pos (b.loadCLM f hf P)
  exact ⟨v, fun w => (hv w).trans (b.loadCLM_apply hf P w),
    fun v' hv' => huniq v' fun w => (hv' w).trans (b.loadCLM_apply hf P w).symm⟩

/-- `EA u'(t) = EA u'(L) + ∫_tᴸ f` for a classical solution. -/
theorem axialForce_eq {f u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (heq : b.Equilibrium f u) {t : ℝ} (ht : t ∈ Icc 0 b.L) :
    b.EA * deriv u t = b.EA * deriv u b.L + b.resultant f t := by
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hftc := integral_eq_sub_of_hasDerivAt (a := t) (b := b.L)
    (fun x _ => ((hu1.differentiable one_ne_zero) x).hasDerivAt)
    ((hu1.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hcongr : ∫ x in t..b.L, f x = ∫ x in t..b.L, -(b.EA * deriv (deriv u) x) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le ht.2] at hx
    have := heq x ⟨ht.1.trans hx.1, hx.2⟩
    linarith
  rw [resultant, hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    hftc]
  ring

theorem continuous_deriv_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (deriv u) :=
  hu.continuous_deriv (by norm_num)

/-- The virtual-work identity of a classical solution:
`EA ⟪u', w⟫ = EA u'(L) (P w)(L) + ∫₀ᴸ f (P w)`. -/
theorem virtualWork {f u : ℝ → ℝ} (hf : Continuous f) (hu : ContDiff ℝ 2 u)
    (heq : b.Equilibrium f u) (w : L2 b.L) :
    b.EA * ⟪toL2 (continuous_deriv_of_contDiff hu), w⟫_ℝ =
      b.EA * deriv u b.L * prim w b.L + ∫ x, f x * prim w x ∂μ b.L := by
  rw [← real_inner_smul_left, b.integral_mul_prim_eq hf, prim_end, ← real_inner_smul_left,
    ← inner_add_left]
  congr 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul b.EA (toL2 (L := b.L) (continuous_deriv_of_contDiff hu)),
    Lp.coeFn_add ((b.EA * deriv u b.L) • oneL2 (L := b.L)) (toL2 (b.continuous_resultant hf)),
    Lp.coeFn_smul (b.EA * deriv u b.L) (oneL2 (L := b.L)),
    toL2_ae_eq (L := b.L) (continuous_deriv_of_contDiff hu),
    toL2_ae_eq (L := b.L) (b.continuous_resultant hf),
    toL2_ae_eq (L := b.L) (f := fun _ => (1 : ℝ)) continuous_const,
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 h4 h5 h6 ht
  have h6' : (oneL2 (L := b.L) : ℝ → ℝ) t = 1 := h6
  rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, h6', smul_eq_mul,
    smul_eq_mul, mul_one, b.axialForce_eq hu heq (Ioc_subset_Icc_self ht)]

/-- **Classical ⇒ weak** (fixed–free): `u'` solves the weak problem, and `P u' = u`. -/
theorem weakFixedFree_of_classical {f u : ℝ → ℝ} {P : ℝ} (hf : Continuous f)
    (hu : ContDiff ℝ 2 u) (heq : b.Equilibrium f u) (hbc : b.FixedFree P u) :
    b.WeakFixedFree f P (toL2 (continuous_deriv_of_contDiff hu)) ∧
      ∀ x ∈ Icc 0 b.L, prim (toL2 (L := b.L) (continuous_deriv_of_contDiff hu)) x = u x := by
  refine ⟨fun w => ?_, fun x hx => ?_⟩
  · rw [b.virtualWork hf hu heq, hbc.2, load]
    ring
  · rw [prim_toL2 _ hx, integral_deriv_eq_sub' u rfl (fun t _ =>
      (hu.differentiable (by norm_num)) t) (continuous_deriv_of_contDiff hu).continuousOn,
      hbc.1, sub_zero]

/-- `H¹₀ = {v | (P v)(L) = 0}`: derivatives of the `u ∈ H¹` with `u(0) = u(L) = 0`. -/
noncomputable def H10 : Submodule ℝ (L2 b.L) := LinearMap.ker (primCLM b.L b.L : L2 b.L →ₗ[ℝ] ℝ)

theorem mem_H10 {v : L2 b.L} : v ∈ b.H10 ↔ prim v b.L = 0 := Iff.rfl

instance : CompleteSpace b.H10 :=
  (ContinuousLinearMap.isClosed_ker (primCLM b.L b.L)).completeSpace_coe

/-- The **weak form** of the fixed–fixed bar. -/
def WeakFixedFixed (f : ℝ → ℝ) (v : L2 b.L) : Prop :=
  v ∈ b.H10 ∧ ∀ w ∈ b.H10, b.EA * ⟪v, w⟫_ℝ = ∫ x, f x * prim w x ∂μ b.L

/-- **Well-posedness** of the fixed–fixed bar (Lax–Milgram on `H¹₀`). -/
theorem weakFixedFixed_existsUnique {f : ℝ → ℝ} (hf : Continuous f) :
    ∃! v, b.WeakFixedFixed f v := by
  set ℓ : b.H10 →L[ℝ] ℝ := (innerSL ℝ (toL2 (b.continuous_resultant hf))).comp b.H10.subtypeL
  have hℓ : ∀ w : b.H10, ℓ w = ∫ x, f x * prim (w : L2 b.L) x ∂μ b.L := fun w => by
    simp [ℓ, b.integral_mul_prim_eq hf]
  obtain ⟨v, hv, huniq⟩ := existsUnique_weak b.EA_pos ℓ
  refine ⟨v, ⟨v.2, fun w hw => (hv ⟨w, hw⟩).trans (hℓ _)⟩, fun v' hv' => ?_⟩
  have := huniq ⟨v', hv'.1⟩ fun w => (hv'.2 w w.2).trans (hℓ w).symm
  rw [← this]

/-- **Classical ⇒ weak** (fixed–fixed): `u'` solves the weak problem, and `P u' = u`. -/
theorem weakFixedFixed_of_classical {f u : ℝ → ℝ} (hf : Continuous f) (hu : ContDiff ℝ 2 u)
    (heq : b.Equilibrium f u) (hbc : b.FixedFixed u) :
    b.WeakFixedFixed f (toL2 (continuous_deriv_of_contDiff hu)) ∧
      ∀ x ∈ Icc 0 b.L, prim (toL2 (L := b.L) (continuous_deriv_of_contDiff hu)) x = u x := by
  have hreal : ∀ x ∈ Icc 0 b.L, prim (toL2 (L := b.L) (continuous_deriv_of_contDiff hu)) x = u x :=
    fun x hx => by
      rw [prim_toL2 _ hx, integral_deriv_eq_sub' u rfl (fun t _ =>
        (hu.differentiable (by norm_num)) t) (continuous_deriv_of_contDiff hu).continuousOn,
        hbc.1, sub_zero]
  refine ⟨⟨?_, fun w hw => ?_⟩, hreal⟩
  · rw [mem_H10, hreal _ ⟨b.L_pos.le, le_rfl⟩, hbc.2]
  · rw [b.virtualWork hf hu heq, (b.mem_H10).1 hw, mul_zero, zero_add]

end Beams.Bar

end ContinuumMechanics
