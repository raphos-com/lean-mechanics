import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import ContinuumMechanics.Beams.Timoshenko.Basic
import ContinuumMechanics.Beams.EulerBernoulli.Solutions

/-!
# The Euler–Bernoulli limit of the Timoshenko beam

For statically determinate beams the Timoshenko solution is obtained from the Euler–Bernoulli one
in closed form: if `w` solves `EI w'''' = q`, then `θ = w'` and
`w_T = w - EI (w'' - c) / κGA` solve the Timoshenko equations, where the constant `c` is fixed by
the boundary conditions (`c = 0` simply supported, `c = w''(0)` for the cantilever); the
correction is the bending moment divided by the shear stiffness ([Reddy2007], §3.4.3;
[Wang1995], "Timoshenko beam-bending solutions in terms of Euler–Bernoulli solutions").
Combined with uniqueness (`TBeam.simplySupported_unique`, `TBeam.cantilever_unique`) this gives

* the rotation `θ` *equals* the Euler–Bernoulli slope `w'`, and
* `|w_T - w| ≤ 2 EI ‖w''‖_∞ / κGA` on `[0, L]`,

hence **uniform convergence `w_T → w` as `κGA → ∞`** for every `C⁴` Euler–Bernoulli solution.

## Main results

* `TBeam.equations_of_eb`: the Timoshenko solution built from an Euler–Bernoulli solution.
* `TBeam.simplySupported_eq_eb`, `TBeam.cantilever_eq_eb`: identification via uniqueness.
* `Beams.simplySupported_tendsto_eb`, `Beams.cantilever_tendsto_eb`: uniform convergence of the
  Timoshenko deflection to the Euler–Bernoulli deflection as `κGA → ∞`.
* Canonical cases with explicit shear corrections: `TBeam.ssUniform_midspan`
  (`5qL⁴/384EI + qL²/8κGA`) and `TBeam.cantileverTip_tip` (`PL³/3EI + PL/κGA`).

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.4.
* [Wang1995] C. M. Wang, J. Eng. Mech. 121 (1995) 763–765.
-/

open Set Filter Topology

namespace ContinuumMechanics.Beams

namespace TBeam

variable (b : TBeam)

/-- The Timoshenko deflection built from an Euler–Bernoulli deflection `w`:
`w_T = w - EI (w'' - c) / κGA`. -/
noncomputable def shearCorrected (w : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun x => w x - b.EI * (iteratedDeriv 2 w x - c) / b.kGA

private theorem i2 (f : ℝ → ℝ) (y : ℝ) : iteratedDeriv 2 f y = deriv (deriv f) y := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

private theorem i4 (f : ℝ → ℝ) (y : ℝ) :
    iteratedDeriv 4 f y = deriv (deriv (deriv (deriv f))) y := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]

section Construction

variable {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
include hw

theorem deriv_shearCorrected (c : ℝ) :
    deriv (b.shearCorrected w c) =
      fun x => deriv w x - b.EI * deriv (deriv (deriv w)) x / b.kGA := by
  have d0 : Differentiable ℝ w := hw.differentiable (by norm_num)
  have d2 : Differentiable ℝ (deriv (deriv w)) :=
    ((hw.iterate_deriv' 2 2 : ContDiff ℝ 2 (deriv^[2] w))).differentiable (by norm_num)
  ext x
  have h := (d0 x).hasDerivAt.sub ((((d2 x).hasDerivAt.sub_const c).const_mul b.EI).div_const b.kGA)
  have e : b.shearCorrected w c = (w - fun y => b.EI * (deriv (deriv w) y - c) / b.kGA) := by
    ext y; simp [shearCorrected, i2]
  rw [e, h.deriv]

/-- **Timoshenko solution from an Euler–Bernoulli solution**: if `EI w'''' = q`, then
`(w - EI (w'' - c)/κGA, w')` solves the Timoshenko equations. [Reddy2007], §3.4.3. -/
theorem equations_of_eb {q : ℝ → ℝ} (h : b.toEB.Equation q w) (c : ℝ) :
    b.Equations q (b.shearCorrected w c) (deriv w) := by
  have hS := b.kGA_pos.ne'
  have d1 : Differentiable ℝ (deriv w) :=
    ((hw.iterate_deriv' 3 1 : ContDiff ℝ 3 (deriv^[1] w))).differentiable (by norm_num)
  have d3 : Differentiable ℝ (deriv (deriv (deriv w))) :=
    ((hw.iterate_deriv' 1 3 : ContDiff ℝ 1 (deriv^[3] w))).differentiable (by norm_num)
  intro x hx
  have hq := h x hx
  rw [i4] at hq
  have dd : deriv (deriv (b.shearCorrected w c)) x =
      deriv (deriv w) x - b.EI * deriv (deriv (deriv (deriv w))) x / b.kGA := by
    rw [b.deriv_shearCorrected hw c]
    exact ((d1 x).hasDerivAt.sub (((d3 x).hasDerivAt.const_mul b.EI).div_const b.kGA)).deriv
  refine ⟨?_, ?_⟩
  · rw [i2, b.deriv_shearCorrected hw c]
    field_simp
    ring
  · rw [i2, dd]
    change b.toEB.EI * _ = q x at hq
    have : b.toEB.EI = b.EI := rfl
    rw [this] at hq
    field_simp
    linarith

end Construction

/-! ### Identification via uniqueness -/

/-- For a simply supported beam, the Timoshenko solution is `θ = w'`, `w_T = w - EI w''/κGA`,
where `w` is the Euler–Bernoulli solution. -/
theorem simplySupported_solution {q w : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
    (hEB : b.toEB.Equation q w) (hbc : b.toEB.SimplySupported w) :
    ContDiff ℝ 2 (b.shearCorrected w 0) ∧ ContDiff ℝ 2 (deriv w) ∧
      b.Equations q (b.shearCorrected w 0) (deriv w) ∧
      b.SimplySupported (b.shearCorrected w 0) (deriv w) := by
  have c2 : ContDiff ℝ 2 (iteratedDeriv 2 w) := by
    rw [iteratedDeriv_eq_iterate]; exact hw.iterate_deriv' 2 2
  have hc : ContDiff ℝ 2 (b.shearCorrected w 0) :=
    ContDiff.sub (hw.of_le (by norm_num))
      (ContDiff.div_const (ContDiff.mul contDiff_const (ContDiff.sub c2 contDiff_const)) _)
  have hd : ContDiff ℝ 2 (deriv w) := by
    have := hw.iterate_deriv' 3 1; simp only [Function.iterate_one] at this
    exact this.of_le (by norm_num)
  have i2' : ∀ y, iteratedDeriv 2 w y = deriv (deriv w) y := fun y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨hc, hd, b.equations_of_eb hw hEB 0, ?_⟩
  obtain ⟨h0, h20, hL, h2L⟩ := hbc
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [shearCorrected, h0, h20]
  · rw [← i2']; exact h20
  · simp only [shearCorrected]
    rw [show b.L = b.toEB.L from rfl, hL, h2L]
    simp
  · rw [← i2']; exact h2L

theorem simplySupported_eq_eb {q w wT θT : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
    (hEB : b.toEB.Equation q w) (hbc : b.toEB.SimplySupported w)
    (hwT : ContDiff ℝ 2 wT) (hθT : ContDiff ℝ 2 θT) (hT : b.Equations q wT θT)
    (hbcT : b.SimplySupported wT θT) :
    ∀ x ∈ Icc 0 b.L, wT x = b.shearCorrected w 0 x ∧ θT x = deriv w x := by
  obtain ⟨hc, hd, he, hb⟩ := b.simplySupported_solution hw hEB hbc
  exact b.simplySupported_unique hwT hθT hc hd hT he hbcT hb

/-- For a cantilever with tip load, the Timoshenko solution is `θ = w'`,
`w_T = w - EI (w'' - w''(0))/κGA`. -/
theorem cantilever_solution {q w : ℝ → ℝ} {P : ℝ} (hw : ContDiff ℝ 4 w)
    (hEB : b.toEB.Equation q w) (hbc : b.toEB.Cantilever P w) :
    ContDiff ℝ 2 (b.shearCorrected w (iteratedDeriv 2 w 0)) ∧ ContDiff ℝ 2 (deriv w) ∧
      b.Equations q (b.shearCorrected w (iteratedDeriv 2 w 0)) (deriv w) ∧
      b.Cantilever P (b.shearCorrected w (iteratedDeriv 2 w 0)) (deriv w) := by
  have hS := b.kGA_pos.ne'
  have hEI := b.EI_pos.ne'
  have c2 : ContDiff ℝ 2 (iteratedDeriv 2 w) := by
    rw [iteratedDeriv_eq_iterate]; exact hw.iterate_deriv' 2 2
  have hc : ContDiff ℝ 2 (b.shearCorrected w (iteratedDeriv 2 w 0)) :=
    ContDiff.sub (hw.of_le (by norm_num))
      (ContDiff.div_const (ContDiff.mul contDiff_const (ContDiff.sub c2 contDiff_const)) _)
  have hd : ContDiff ℝ 2 (deriv w) := by
    have := hw.iterate_deriv' 3 1; simp only [Function.iterate_one] at this
    exact this.of_le (by norm_num)
  have i2' : ∀ y, iteratedDeriv 2 w y = deriv (deriv w) y := fun y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have i3' : ∀ y, iteratedDeriv 3 w y = deriv (deriv (deriv w)) y := fun y => by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  refine ⟨hc, hd, b.equations_of_eb hw hEB _, ?_⟩
  obtain ⟨h0, h10, h2L, h3L⟩ := hbc
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [shearCorrected, h0]
  · rw [← iteratedDeriv_one]; exact h10
  · rw [← i2']; exact h2L
  · rw [b.deriv_shearCorrected hw]
    change b.EI * iteratedDeriv 3 w b.L = -P at h3L
    rw [i3'] at h3L
    field_simp
    linarith

theorem cantilever_eq_eb {q w wT θT : ℝ → ℝ} {P : ℝ} (hw : ContDiff ℝ 4 w)
    (hEB : b.toEB.Equation q w) (hbc : b.toEB.Cantilever P w)
    (hwT : ContDiff ℝ 2 wT) (hθT : ContDiff ℝ 2 θT) (hT : b.Equations q wT θT)
    (hbcT : b.Cantilever P wT θT) :
    ∀ x ∈ Icc 0 b.L,
      wT x = b.shearCorrected w (iteratedDeriv 2 w 0) x ∧ θT x = deriv w x := by
  obtain ⟨hc, hd, he, hb⟩ := b.cantilever_solution hw hEB hbc
  exact b.cantilever_unique hwT hθT hc hd hT he hbcT hb

/-- The size of the shear correction: `|w_T - w| = EI |w'' - c| / κGA`. -/
theorem abs_shearCorrected_sub (w : ℝ → ℝ) (c x : ℝ) :
    |b.shearCorrected w c x - w x| = b.EI * |iteratedDeriv 2 w x - c| / b.kGA := by
  rw [shearCorrected, sub_sub_cancel_left, abs_neg, abs_div, abs_mul, abs_of_pos b.EI_pos,
    abs_of_pos b.kGA_pos]

/-! ### Canonical cases with explicit shear corrections -/

/-- Simply supported Timoshenko beam under uniform load: midspan deflection
`5 q L⁴ / (384 EI) + q L² / (8 κGA)`. [Reddy2007], §3.4.3. -/
theorem ssUniform_midspan (q : ℝ) :
    b.shearCorrected (b.toEB.ssUniform q) 0 (b.L / 2) =
      5 * q * b.L ^ 4 / (384 * b.EI) + q * b.L ^ 2 / (8 * b.kGA) := by
  have hEI := b.EI_pos.ne'
  have hS := b.kGA_pos.ne'
  simp only [shearCorrected]
  unfold EBBeam.ssUniform EBBeam.ssUniformPoly
  simp only [show b.toEB.L = b.L from rfl, show b.toEB.EI = b.EI from rfl]
  beam_poly

/-- Timoshenko cantilever with tip load: tip deflection `P L³ / (3 EI) + P L / κGA`.
[Reddy2007], §3.4.3. -/
theorem cantileverTip_tip (P : ℝ) :
    b.shearCorrected (b.toEB.cantileverTip P) (iteratedDeriv 2 (b.toEB.cantileverTip P) 0) b.L =
      P * b.L ^ 3 / (3 * b.EI) + P * b.L / b.kGA := by
  have hEI := b.EI_pos.ne'
  have hS := b.kGA_pos.ne'
  have hL := b.L_pos.ne'
  simp only [shearCorrected]
  unfold EBBeam.cantileverTip EBBeam.cantileverTipPoly
  simp only [show b.toEB.L = b.L from rfl, show b.toEB.EI = b.EI from rfl]
  beam_poly

end TBeam

/-! ### Convergence as `κGA → ∞` -/

/-- The Timoshenko beam with length `L`, bending stiffness `EI` and shear stiffness `S`. -/
def tbeam (L EI : ℝ) (hL : 0 < L) (hEI : 0 < EI) (S : ℝ) (hS : 0 < S) : TBeam :=
  ⟨L, EI, S, hL, hEI, hS⟩

/-- A uniform bound for the second derivative of a `C²` function on `[0, L]`. -/
theorem exists_bound_iteratedDeriv_two {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) (L : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 L, |iteratedDeriv 2 w x| ≤ M := by
  have hc : Continuous (iteratedDeriv 2 w) := by
    rw [iteratedDeriv_eq_iterate]; exact (hw.iterate_deriv' 2 2).continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := L)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx => by
    rw [← Real.norm_eq_abs]; exact (hM x hx).trans (le_max_left _ _)⟩

/-- **Timoshenko → Euler–Bernoulli, simply supported, general load.** Let `w` be a `C⁴`
simply supported Euler–Bernoulli solution, and for each shear stiffness `S > 0` let `wT S`
be a `C²` simply supported Timoshenko solution (any rotation field). Then `wT S → w` uniformly on
`[0, L]` as `S → ∞`. -/
theorem simplySupported_tendsto_eb {L EI : ℝ} (hL : 0 < L) (hEI : 0 < EI) {q w : ℝ → ℝ}
    (hw : ContDiff ℝ 4 w) (hEB : (⟨L, EI, hL, hEI⟩ : EBBeam).Equation q w)
    (hbc : (⟨L, EI, hL, hEI⟩ : EBBeam).SimplySupported w)
    (wT θT : ℝ → ℝ → ℝ)
    (hT : ∀ S (hS : 0 < S), ContDiff ℝ 2 (wT S) ∧ ContDiff ℝ 2 (θT S) ∧
      (tbeam L EI hL hEI S hS).Equations q (wT S) (θT S) ∧
      (tbeam L EI hL hEI S hS).SimplySupported (wT S) (θT S)) :
    TendstoUniformlyOn wT w atTop (Icc 0 L) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDeriv_two hw L
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_gt_atTop (EI * M / ε), eventually_gt_atTop 0] with S hSε hS
  intro x hx
  set b := tbeam L EI hL hEI S hS
  obtain ⟨hwT, hθT, hTe, hTbc⟩ := hT S hS
  have e := (b.simplySupported_eq_eb hw hEB hbc hwT hθT hTe hTbc x hx).1
  rw [Real.dist_eq, e, abs_sub_comm, b.abs_shearCorrected_sub, sub_zero]
  have : b.EI * |iteratedDeriv 2 w x| ≤ EI * M := mul_le_mul_of_nonneg_left (hM x hx) hEI.le
  calc b.EI * |iteratedDeriv 2 w x| / b.kGA ≤ EI * M / S := div_le_div_of_nonneg_right this hS.le
    _ < ε := by
      rw [div_lt_iff₀ hS]
      have := (div_lt_iff₀ hε).mp hSε
      linarith

/-- **Timoshenko → Euler–Bernoulli, cantilever with tip load, general load.** -/
theorem cantilever_tendsto_eb {L EI P : ℝ} (hL : 0 < L) (hEI : 0 < EI) {q w : ℝ → ℝ}
    (hw : ContDiff ℝ 4 w) (hEB : (⟨L, EI, hL, hEI⟩ : EBBeam).Equation q w)
    (hbc : (⟨L, EI, hL, hEI⟩ : EBBeam).Cantilever P w)
    (wT θT : ℝ → ℝ → ℝ)
    (hT : ∀ S (hS : 0 < S), ContDiff ℝ 2 (wT S) ∧ ContDiff ℝ 2 (θT S) ∧
      (tbeam L EI hL hEI S hS).Equations q (wT S) (θT S) ∧
      (tbeam L EI hL hEI S hS).Cantilever P (wT S) (θT S)) :
    TendstoUniformlyOn wT w atTop (Icc 0 L) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDeriv_two hw L
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_gt_atTop (EI * (2 * M) / ε), eventually_gt_atTop 0] with S hSε hS
  intro x hx
  set b := tbeam L EI hL hEI S hS
  obtain ⟨hwT, hθT, hTe, hTbc⟩ := hT S hS
  have e := (b.cantilever_eq_eb hw hEB hbc hwT hθT hTe hTbc x hx).1
  rw [Real.dist_eq, e, abs_sub_comm, b.abs_shearCorrected_sub]
  have hb : |iteratedDeriv 2 w x - iteratedDeriv 2 w 0| ≤ 2 * M := by
    calc |iteratedDeriv 2 w x - iteratedDeriv 2 w 0|
        ≤ |iteratedDeriv 2 w x| + |iteratedDeriv 2 w 0| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM x hx) (hM 0 h0)
      _ = 2 * M := by ring
  have : b.EI * |iteratedDeriv 2 w x - iteratedDeriv 2 w 0| ≤ EI * (2 * M) :=
    mul_le_mul_of_nonneg_left hb hEI.le
  calc b.EI * |iteratedDeriv 2 w x - iteratedDeriv 2 w 0| / b.kGA ≤ EI * (2 * M) / S :=
        div_le_div_of_nonneg_right this hS.le
    _ < ε := by
      rw [div_lt_iff₀ hS]
      have := (div_lt_iff₀ hε).mp hSε
      linarith

/-- The hypotheses of `simplySupported_tendsto_eb` are satisfiable: the shear-corrected family
is a Timoshenko solution for every `S > 0`. -/
theorem simplySupported_family_exists {L EI : ℝ} (hL : 0 < L) (hEI : 0 < EI) {q w : ℝ → ℝ}
    (hw : ContDiff ℝ 4 w) (hEB : (⟨L, EI, hL, hEI⟩ : EBBeam).Equation q w)
    (hbc : (⟨L, EI, hL, hEI⟩ : EBBeam).SimplySupported w) :
    ∀ S (hS : 0 < S), ContDiff ℝ 2 ((tbeam L EI hL hEI S hS).shearCorrected w 0) ∧
      ContDiff ℝ 2 (deriv w) ∧
      (tbeam L EI hL hEI S hS).Equations q ((tbeam L EI hL hEI S hS).shearCorrected w 0) (deriv w) ∧
      (tbeam L EI hL hEI S hS).SimplySupported
        ((tbeam L EI hL hEI S hS).shearCorrected w 0) (deriv w) :=
  fun S hS => (tbeam L EI hL hEI S hS).simplySupported_solution hw hEB hbc

/-- The hypotheses of `cantilever_tendsto_eb` are satisfiable. -/
theorem cantilever_family_exists {L EI P : ℝ} (hL : 0 < L) (hEI : 0 < EI) {q w : ℝ → ℝ}
    (hw : ContDiff ℝ 4 w) (hEB : (⟨L, EI, hL, hEI⟩ : EBBeam).Equation q w)
    (hbc : (⟨L, EI, hL, hEI⟩ : EBBeam).Cantilever P w) (S : ℝ) (hS : 0 < S) :
    let b := tbeam L EI hL hEI S hS
    ContDiff ℝ 2 (b.shearCorrected w (iteratedDeriv 2 w 0)) ∧ ContDiff ℝ 2 (deriv w) ∧
      b.Equations q (b.shearCorrected w (iteratedDeriv 2 w 0)) (deriv w) ∧
      b.Cantilever P (b.shearCorrected w (iteratedDeriv 2 w 0)) (deriv w) :=
  (tbeam L EI hL hEI S hS).cantilever_solution hw hEB hbc

end ContinuumMechanics.Beams
