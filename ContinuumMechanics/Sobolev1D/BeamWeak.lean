import ContinuumMechanics.Sobolev1D.BarWeak
import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Weak formulation of the Euler–Bernoulli cantilever

For a cantilever clamped at `0` (`w(0) = w'(0) = 0`), the deflection is the double primitive
`w = P (P κ)` of the curvature `κ = w'' ∈ L²` (see `Sobolev1D.Primitive`). The principle of
virtual work reads

`EI ⟪κ, η⟫ = ∫₀ᴸ q (P² η) + P_tip (P² η)(L)`  for all `η ∈ L²`,

which is **well posed** by Lax–Milgram. A classical `C⁴` solution of `EI w'''' = q` with the
cantilever boundary conditions is the weak solution, and `P² w'' = w` ([Reddy2007], §4.2).

The key identity is that the bending moment of a cantilever is
`EI w''(t) = P_tip (L - t) + ∫_tᴸ ∫_sᴸ q`, together with Fubini (`integral_mul_prim_eq`).

## Main results

* `Beams.EBBeam.weakCantilever_existsUnique`
* `Beams.EBBeam.moment_cantilever`
* `Beams.EBBeam.weakCantilever_of_classical`

## References

* [Reddy2007] J. N. Reddy, *An Introduction to the Finite Element Method*, §4.2.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §9.2.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace

namespace ContinuumMechanics

namespace Sobolev1D

variable {L : ℝ}

/-- `⟪∫_·ᴸ f, η⟫ = ⟪f, P η⟫`. -/
theorem inner_resultant_eq (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Continuous f) (η : L2 L) :
    ⟪toL2 (continuous_resultant (L := L) hf), η⟫_ℝ = ⟪toL2 hf, primL2 hL η⟫_ℝ := by
  rw [← integral_mul_prim_eq hf, inner_toL2]
  refine integral_congr_ae ((primL2_ae_eq hL η).mono fun t ht => ?_)
  simp only [ht]

/-- FTC from the right end: `g(t) = g(L) - ∫_tᴸ g'`. -/
theorem eq_sub_integral_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (t L : ℝ) :
    g t = g L - ∫ x in t..L, deriv g x := by
  rw [integral_deriv_eq_sub' g rfl (fun x _ => (hg.differentiable one_ne_zero) x)
    (hg.continuous_deriv le_rfl).continuousOn]
  ring

end Sobolev1D

namespace Beams.EBBeam

open Sobolev1D

variable (b : EBBeam)

/-- The cantilever load functional `η ↦ ∫₀ᴸ q (P² η) + P_tip (P² η)(L)`. -/
noncomputable def loadCantilever (q : ℝ → ℝ) (P : ℝ) (η : L2 b.L) : ℝ :=
  (∫ x, q x * prim (primL2 b.L_pos.le η) x ∂μ b.L) + P * prim (primL2 b.L_pos.le η) b.L

/-- The **weak form** of the cantilever with distributed load `q` and tip load `P`. -/
def WeakCantilever (q : ℝ → ℝ) (P : ℝ) (κ : L2 b.L) : Prop :=
  ∀ η : L2 b.L, b.EI * ⟪κ, η⟫_ℝ = b.loadCantilever q P η

/-- The load functional is continuous and linear. -/
noncomputable def loadCantileverCLM {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) :
    L2 b.L →L[ℝ] ℝ :=
  (innerSL ℝ (toL2 (continuous_resultant (L := b.L) hq) + P • oneL2)).comp (primL2 b.L_pos.le)

theorem loadCantileverCLM_apply {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) (η : L2 b.L) :
    b.loadCantileverCLM hq P η = b.loadCantilever q P η := by
  simp only [loadCantileverCLM, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    inner_add_left, real_inner_smul_left, loadCantilever, integral_mul_prim_eq hq, prim_end]

/-- **Well-posedness** of the cantilever (Lax–Milgram). -/
theorem weakCantilever_existsUnique {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) :
    ∃! κ, b.WeakCantilever q P κ := by
  obtain ⟨κ, hκ, huniq⟩ := existsUnique_weak b.EI_pos (b.loadCantileverCLM hq P)
  exact ⟨κ, fun η => (hκ η).trans (b.loadCantileverCLM_apply hq P η),
    fun κ' hκ' => huniq κ' fun η => (hκ' η).trans (b.loadCantileverCLM_apply hq P η).symm⟩

variable {b}

theorem contDiff_iteratedDeriv {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) {k n : ℕ} (hkn : n + k = 4) :
    ContDiff ℝ n (iteratedDeriv k w) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv' n k (by rw [hkn]; exact hw)

/-- The **bending moment of a cantilever**: `EI w''(t) = P (L - t) + ∫_tᴸ ∫_sᴸ q`.
[TimoshenkoGere1997], §9.2. -/
theorem moment_cantilever {q w : ℝ → ℝ} {P : ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w)
    (heq : b.Equation q w)
    (hbc : b.Cantilever P w) {t : ℝ} (ht : t ∈ Icc 0 b.L) :
    b.EI * iteratedDeriv 2 w t = P * (b.L - t) + resultant b.L (resultant b.L q) t := by
  have c2 : ContDiff ℝ 2 (iteratedDeriv 2 w) := contDiff_iteratedDeriv hw rfl
  have c3 : ContDiff ℝ 1 (iteratedDeriv 3 w) := contDiff_iteratedDeriv hw rfl
  have d2 : deriv (iteratedDeriv 2 w) = iteratedDeriv 3 w := (iteratedDeriv_succ).symm
  have d3 : deriv (iteratedDeriv 3 w) = iteratedDeriv 4 w := (iteratedDeriv_succ).symm
  -- shear force
  have hV : ∀ s ∈ Icc 0 b.L, b.EI * iteratedDeriv 3 w s = -P - resultant b.L q s := fun s hs => by
    rw [eq_sub_integral_deriv c3 s b.L, d3, mul_sub, hbc.2.2.2,
      ← intervalIntegral.integral_const_mul,
      resultant]
    have : ∫ x in s..b.L, b.EI * iteratedDeriv 4 w x = ∫ x in s..b.L, q x :=
      integral_congr fun x hx => by
        rw [uIcc_of_le hs.2] at hx
        exact heq x ⟨hs.1.trans hx.1, hx.2⟩
    rw [this]
  have hR : Continuous (resultant b.L q) := continuous_resultant hq
  rw [eq_sub_integral_deriv (c2.of_le one_le_two) t b.L, d2, hbc.2.2.1, zero_sub, mul_neg,
    ← intervalIntegral.integral_const_mul]
  have : ∫ x in t..b.L, b.EI * iteratedDeriv 3 w x = ∫ x in t..b.L, (-P - resultant b.L q x) :=
    integral_congr fun x hx => by
      rw [uIcc_of_le ht.2] at hx
      exact hV x ⟨ht.1.trans hx.1, hx.2⟩
  rw [this, intervalIntegral.integral_sub intervalIntegrable_const (hR.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul, resultant]
  ring

/-- **Classical ⇒ weak** (cantilever): the curvature `w''` of a classical solution solves the weak
problem, and `P² w'' = w`. -/
theorem weakCantilever_of_classical {q w : ℝ → ℝ} {P : ℝ} (hq : Continuous q)
    (hw : ContDiff ℝ 4 w) (heq : b.Equation q w) (hbc : b.Cantilever P w) :
    b.WeakCantilever q P (toL2 (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous) ∧
      ∀ x ∈ Icc 0 b.L, prim (primL2 b.L_pos.le
        (toL2 (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous)) x = w x := by
  have hL := b.L_pos.le
  set κ : L2 b.L := toL2 (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous
  have hR := continuous_resultant (L := b.L) hq
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  refine ⟨fun η => ?_, fun x hx => ?_⟩
  · -- `EI κ = P (L - ·) + ∫∫ q` in `L²`
    have hM : b.EI • κ = P • toL2 (continuous_resultant (L := b.L) h1) +
        toL2 (continuous_resultant (L := b.L) hR) := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_smul b.EI κ,
        Lp.coeFn_add (P • toL2 (continuous_resultant (L := b.L) h1))
          (toL2 (continuous_resultant (L := b.L) hR)),
        Lp.coeFn_smul P (toL2 (continuous_resultant (L := b.L) h1)),
        toL2_ae_eq (L := b.L) (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous,
        toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) h1),
        toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) hR),
        ae_restrict_mem measurableSet_Ioc] with t e1 e2 e3 e4 e5 e6 ht
      rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, Pi.smul_apply, e4, e5, e6, smul_eq_mul,
        smul_eq_mul, b.moment_cantilever hq hw heq hbc (Ioc_subset_Icc_self ht)]
      simp [resultant]
    rw [← real_inner_smul_left, hM, inner_add_left, real_inner_smul_left,
      inner_resultant_eq hL h1, inner_resultant_eq hL hR, loadCantilever, integral_mul_prim_eq hq,
      prim_end, add_comm]
    rfl
  · have hw1 : ContDiff ℝ 1 (deriv w) := by
      have := contDiff_iteratedDeriv hw (n := 3) (k := 1) rfl
      rw [iteratedDeriv_one] at this
      exact this.of_le (by norm_num)
    have hd2 : iteratedDeriv 2 w = deriv (deriv w) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hw0 : deriv w 0 = 0 := by rw [← iteratedDeriv_one]; exact hbc.2.1
    rw [primL2_apply, prim_toL2 (continuous_prim κ) hx]
    have : ∫ y in (0 : ℝ)..x, prim κ y = ∫ y in (0 : ℝ)..x, deriv w y :=
      integral_congr fun y hy => by
        rw [uIcc_of_le hx.1] at hy
        have hyL : y ∈ Icc 0 b.L := ⟨hy.1, hy.2.trans hx.2⟩
        rw [prim_toL2 _ hyL, hd2, integral_deriv_eq_sub' (deriv w) rfl
          (fun t _ => (hw1.differentiable one_ne_zero) t)
          (hw1.continuous_deriv le_rfl).continuousOn,
          hw0, sub_zero]
    rw [this, integral_deriv_eq_sub' w rfl (fun t _ => (hw.differentiable (by norm_num)) t)
      hw1.continuous.continuousOn, hbc.1, sub_zero]

end Beams.EBBeam

end ContinuumMechanics
