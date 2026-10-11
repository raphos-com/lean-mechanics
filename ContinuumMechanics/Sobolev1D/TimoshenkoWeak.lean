import ContinuumMechanics.Sobolev1D.BeamWeak
import ContinuumMechanics.Beams.Timoshenko.Basic

/-!
# Weak formulation of the Timoshenko cantilever

For a Timoshenko cantilever clamped at `0` (`w(0) = θ(0) = 0`) the unknowns are the bending
strain `φ = θ' ∈ L²` and the shear strain `γ = w' - θ ∈ L²`. The kinematic fields are recovered as
`θ = P φ` and `w = P (γ + P φ)` (see `Sobolev1D.Primitive`), so the clamped conditions are built
in. The principle of virtual work reads

`EI ⟪φ, φ̂⟫ + κGA ⟪γ, γ̂⟫ = ∫₀ᴸ q ŵ + P_tip ŵ(L)`,  `ŵ = P (γ̂ + P φ̂)`,
for all `(φ̂, γ̂) ∈ L² × L²`.

The energy form `EI ⟪φ, φ⟫ + κGA ⟪γ, γ⟫` is coercive and **decoupled**: the problem splits into
the two Riesz problems `EI ⟪φ, ·⟫ = ℓ ∘ P` and `κGA ⟪γ, ·⟫ = ℓ` with `ℓ(v) = ∫₀ᴸ q (P v) +
P_tip (P v)(L)`, so it is **well posed** by Lax–Milgram. A classical `C²` solution of the
Timoshenko equations with the cantilever boundary conditions gives the weak solution
`(θ', w' - θ)`, and `P θ' = θ`, `P (w' - θ + P θ') = w` ([Reddy2007], §3.4).

The key identities are the cantilever stress resultants `κGA (w' - θ)(t) = P_tip + ∫_tᴸ q` and
`EI θ'(t) = P_tip (L - t) + ∫_tᴸ ∫_sᴸ q`.

## Main results

* `Beams.TBeam.weakCantilever_existsUnique`
* `Beams.TBeam.shear_cantilever`, `Beams.TBeam.moment_cantilever`
* `Beams.TBeam.weakCantilever_of_classical`

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.4.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §8.4.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace

namespace ContinuumMechanics.Beams.TBeam

open Sobolev1D

variable (b : TBeam)

/-- The load functional on slopes `v = w'`: `v ↦ ∫₀ᴸ q (P v) + P_tip (P v)(L)`. -/
noncomputable def slopeLoadCLM {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) : L2 b.L →L[ℝ] ℝ :=
  innerSL ℝ (toL2 (continuous_resultant (L := b.L) hq) + P • oneL2)

/-- The cantilever load functional `(φ̂, γ̂) ↦ ∫₀ᴸ q ŵ + P_tip ŵ(L)` with `ŵ = P (γ̂ + P φ̂)`. -/
noncomputable def loadCantilever (q : ℝ → ℝ) (P : ℝ) (φ γ : L2 b.L) : ℝ :=
  (∫ x, q x * prim (γ + primL2 b.L_pos.le φ) x ∂μ b.L) + P * prim (γ + primL2 b.L_pos.le φ) b.L

/-- The cantilever load is the slope load evaluated at `ŵ' = γ̂ + P φ̂`. -/
theorem slopeLoadCLM_apply {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) (φ γ : L2 b.L) :
    b.slopeLoadCLM hq P (γ + primL2 b.L_pos.le φ) = b.loadCantilever q P φ γ := by
  simp only [slopeLoadCLM, innerSL_apply_apply, inner_add_left, real_inner_smul_left,
    loadCantilever, integral_mul_prim_eq hq, prim_end]

/-- The **weak form** of the Timoshenko cantilever with distributed load `q` and tip load `P`,
for the bending strain `φ = θ'` and the shear strain `γ = w' - θ`. -/
def WeakCantilever (q : ℝ → ℝ) (P : ℝ) (φ γ : L2 b.L) : Prop :=
  ∀ φ' γ' : L2 b.L, b.EI * ⟪φ, φ'⟫_ℝ + b.kGA * ⟪γ, γ'⟫_ℝ = b.loadCantilever q P φ' γ'

/-- **Well-posedness** of the Timoshenko cantilever (Lax–Milgram, the energy form being
coercive with constant `min EI κGA` and decoupled). -/
theorem weakCantilever_existsUnique {q : ℝ → ℝ} (hq : Continuous q) (P : ℝ) :
    ∃! p : L2 b.L × L2 b.L, b.WeakCantilever q P p.1 p.2 := by
  set ℓ := b.slopeLoadCLM hq P
  have hsplit : ∀ φ' γ', b.loadCantilever q P φ' γ' = ℓ (primL2 b.L_pos.le φ') + ℓ γ' :=
    fun φ' γ' => by rw [← b.slopeLoadCLM_apply hq P, map_add, add_comm]
  obtain ⟨φ, hφ, uφ⟩ := existsUnique_weak b.EI_pos (ℓ.comp (primL2 b.L_pos.le))
  obtain ⟨γ, hγ, uγ⟩ := existsUnique_weak b.kGA_pos ℓ
  refine ⟨(φ, γ), fun φ' γ' => ?_, fun p hp => ?_⟩
  · rw [hsplit, hφ, hγ]
    rfl
  · refine Prod.ext (uφ _ fun φ' => ?_) (uγ _ fun γ' => ?_)
    · have := hp φ' 0
      rw [inner_zero_right, mul_zero, add_zero, hsplit, map_zero, add_zero] at this
      exact this
    · have := hp 0 γ'
      rw [inner_zero_right, mul_zero, zero_add, hsplit, map_zero, map_zero, zero_add] at this
      exact this

/-! ### Classical solutions are weak solutions -/

/-- The bending strain `θ'` of a `C²` rotation, as an element of `L²`. -/
noncomputable def bendingStrain {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ) : L2 b.L :=
  toL2 (hθ.continuous_deriv (by norm_num))

/-- The shear strain `w' - θ` of `C²` fields, as an element of `L²`. -/
noncomputable def shearStrain {w θ : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (hθ : ContDiff ℝ 2 θ) :
    L2 b.L :=
  toL2 ((hw.continuous_deriv (by norm_num)).sub hθ.continuous)

variable {b}

/-- The **shear force of a cantilever**: `κGA (w' - θ)(t) = P + ∫_tᴸ q`. -/
theorem shear_cantilever {q w θ : ℝ → ℝ} {P : ℝ} (hw : ContDiff ℝ 2 w) (hθ : ContDiff ℝ 2 θ)
    (heq : b.Equations q w θ) (hbc : b.Cantilever P w θ) {t : ℝ} (ht : t ∈ Icc 0 b.L) :
    b.kGA * (deriv w t - θ t) = P + resultant b.L q t := by
  have hw1 : ContDiff ℝ 1 (deriv w) := hw.deriv' (n := 1)
  have hθ1 : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hFTC : ∫ x in t..b.L, (deriv (deriv w) x - deriv θ x) =
      (deriv w b.L - θ b.L) - (deriv w t - θ t) :=
    integral_eq_sub_of_hasDerivAt (f := fun x => deriv w x - θ x)
      (fun x _ => ((hw1.differentiable one_ne_zero) x).hasDerivAt.sub
        ((hθ.differentiable (by norm_num)) x).hasDerivAt)
      (((hw1.continuous_deriv le_rfl).sub hθ1.continuous).intervalIntegrable _ _)
  have hcongr : ∫ x in t..b.L, q x =
      ∫ x in t..b.L, -(b.kGA * (deriv (deriv w) x - deriv θ x)) :=
    integral_congr fun x hx => by
      rw [uIcc_of_le ht.2] at hx
      have := (heq x ⟨ht.1.trans hx.1, hx.2⟩).2
      rw [iteratedDeriv_succ, iteratedDeriv_one] at this
      linarith
  rw [resultant, hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    hFTC, ← hbc.2.2.2]
  ring

/-- The **bending moment of a cantilever**: `EI θ'(t) = P (L - t) + ∫_tᴸ ∫_sᴸ q`. -/
theorem moment_cantilever {q w θ : ℝ → ℝ} {P : ℝ} (hq : Continuous q) (hw : ContDiff ℝ 2 w)
    (hθ : ContDiff ℝ 2 θ) (heq : b.Equations q w θ) (hbc : b.Cantilever P w θ) {t : ℝ}
    (ht : t ∈ Icc 0 b.L) :
    b.EI * deriv θ t = P * (b.L - t) + resultant b.L (resultant b.L q) t := by
  have hθ1 : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hR : Continuous (resultant b.L q) := continuous_resultant hq
  rw [eq_sub_integral_deriv hθ1 t b.L, hbc.2.2.1, zero_sub, mul_neg,
    ← intervalIntegral.integral_const_mul]
  have : ∫ x in t..b.L, b.EI * deriv (deriv θ) x = ∫ x in t..b.L, -(P + resultant b.L q x) :=
    integral_congr fun x hx => by
      rw [uIcc_of_le ht.2] at hx
      have hx' : x ∈ Icc 0 b.L := ⟨ht.1.trans hx.1, hx.2⟩
      have h1 := (heq x hx').1
      rw [iteratedDeriv_succ, iteratedDeriv_one] at h1
      have h2 := shear_cantilever hw hθ heq hbc hx'
      linarith
  rw [this, intervalIntegral.integral_neg,
    intervalIntegral.integral_add intervalIntegrable_const (hR.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul,
    show resultant b.L (resultant b.L q) t = ∫ x in t..b.L, resultant b.L q x from rfl]
  ring

/-- **Classical ⇒ weak** (Timoshenko cantilever): `(θ', w' - θ)` of a classical solution solves
the weak problem, and `P θ' = θ`, `P (w' - θ + P θ') = w`. -/
theorem weakCantilever_of_classical {q w θ : ℝ → ℝ} {P : ℝ} (hq : Continuous q)
    (hw : ContDiff ℝ 2 w) (hθ : ContDiff ℝ 2 θ) (heq : b.Equations q w θ)
    (hbc : b.Cantilever P w θ) :
    b.WeakCantilever q P (b.bendingStrain hθ) (b.shearStrain hw hθ) ∧
      (∀ x ∈ Icc 0 b.L, prim (b.bendingStrain hθ) x = θ x) ∧
      ∀ x ∈ Icc 0 b.L,
        prim (b.shearStrain hw hθ + primL2 b.L_pos.le (b.bendingStrain hθ)) x = w x := by
  have hL := b.L_pos.le
  have hR := continuous_resultant (L := b.L) hq
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  have hone : ∀ v : L2 b.L, ⟪toL2 (L := b.L) h1, v⟫_ℝ = prim v b.L := fun v => (prim_end v).symm
  have hw1 : ContDiff ℝ 1 (deriv w) := hw.deriv' (n := 1)
  have hθ1 : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hφ : b.EI • b.bendingStrain hθ = P • toL2 (continuous_resultant (L := b.L) h1) +
      toL2 (continuous_resultant (L := b.L) hR) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul b.EI (b.bendingStrain hθ),
      Lp.coeFn_add (P • toL2 (continuous_resultant (L := b.L) h1))
        (toL2 (continuous_resultant (L := b.L) hR)),
      Lp.coeFn_smul P (toL2 (continuous_resultant (L := b.L) h1)),
      toL2_ae_eq (L := b.L) (hθ.continuous_deriv (by norm_num)),
      toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) h1),
      toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) hR),
      ae_restrict_mem measurableSet_Ioc] with t e1 e2 e3 e4 e5 e6 ht
    rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, Pi.smul_apply, bendingStrain, e4, e5, e6,
      smul_eq_mul, smul_eq_mul, moment_cantilever hq hw hθ heq hbc (Ioc_subset_Icc_self ht)]
    simp [resultant]
  have hγ : b.kGA • b.shearStrain hw hθ = P • toL2 (L := b.L) h1 + toL2 hR := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul b.kGA (b.shearStrain hw hθ),
      Lp.coeFn_add (P • toL2 (L := b.L) h1) (toL2 hR),
      Lp.coeFn_smul P (toL2 (L := b.L) h1),
      toL2_ae_eq (L := b.L) ((hw.continuous_deriv (by norm_num)).sub hθ.continuous),
      toL2_ae_eq (L := b.L) h1, toL2_ae_eq (L := b.L) hR,
      ae_restrict_mem measurableSet_Ioc] with t e1 e2 e3 e4 e5 e6 ht
    rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, Pi.smul_apply, shearStrain, e4, e5, e6,
      smul_eq_mul, smul_eq_mul, Pi.sub_apply,
      shear_cantilever hw hθ heq hbc (Ioc_subset_Icc_self ht), mul_one]
  have hrotθ : ∀ x ∈ Icc 0 b.L, prim (b.bendingStrain hθ) x = θ x := fun x hx => by
    rw [bendingStrain, prim_toL2 _ hx, integral_deriv_eq_sub' θ rfl
      (fun t _ => (hθ.differentiable (by norm_num)) t) hθ1.continuous.continuousOn, hbc.2.1,
      sub_zero]
  refine ⟨fun φ' γ' => ?_, hrotθ, fun x hx => ?_⟩
  · rw [← real_inner_smul_left, ← real_inner_smul_left, hφ, hγ, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, inner_resultant_eq hL h1,
      inner_resultant_eq hL hR, loadCantilever, integral_mul_prim_eq hq, inner_add_right,
      prim_add, Pi.add_apply]
    simp only [hone]
    ring
  · rw [prim_add, Pi.add_apply, primL2_apply, prim_toL2 (continuous_prim _) hx, shearStrain,
      prim_toL2 _ hx]
    have : ∫ y in (0 : ℝ)..x, prim (b.bendingStrain hθ) y = ∫ y in (0 : ℝ)..x, θ y :=
      integral_congr fun y hy => by
        rw [uIcc_of_le hx.1] at hy
        exact hrotθ y ⟨hy.1, hy.2.trans hx.2⟩
    simp only [Pi.sub_apply]
    rw [this, intervalIntegral.integral_sub (hw1.continuous.intervalIntegrable _ _)
      (hθ.continuous.intervalIntegrable _ _), sub_add_cancel,
      integral_deriv_eq_sub' w rfl (fun t _ => (hw.differentiable (by norm_num)) t)
      hw1.continuous.continuousOn, hbc.1, sub_zero]

end ContinuumMechanics.Beams.TBeam
