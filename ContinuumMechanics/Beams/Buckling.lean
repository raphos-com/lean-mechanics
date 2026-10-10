import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Euler buckling of a pinned–pinned column

A column of length `L` and bending stiffness `EI` under an axial compressive load `P > 0` has
lateral deflection `w` satisfying `EI w'''' + P w'' = 0` on `[0, L]`; pinned ends give
`w = w'' = 0` at `x = 0, L` ([TimoshenkoGere1961], §2.1). The trivial solution `w = 0` always
exists; the column **buckles** when a nontrivial solution exists.

## Main results

* `EBBeam.buckling_iff`: a nontrivial `C⁴` solution exists iff `P = n² π² EI / L²` for some
  integer `n ≥ 1` (the buckling loads), and then the mode is `w = c sin(nπx/L)`.
* `EBBeam.euler_critical_load`: the smallest buckling load is the **Euler load**
  `P_cr = π² EI / L²`.

The proof reduces the equation to `w'' + k² w = 0` (`k² = P/EI`) by integrating twice with the
boundary conditions, and identifies the solution through the conserved energy `w'² + k² w²`.

The Rayleigh-quotient characterisation of `P_cr` (needing Wirtinger's inequality) is a separate
milestone.

## References

* [TimoshenkoGere1961] S. P. Timoshenko, J. M. Gere, *Theory of Elastic Stability*, §2.1.
-/

open Set Real
open scoped Real

namespace ContinuumMechanics.Beams

namespace EBBeam

variable (b : EBBeam)

/-- The **buckling equation** `EI w'''' + P w'' = 0` on `[0, L]`. -/
def BucklingEquation (P : ℝ) (w : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 b.L, b.EI * iteratedDeriv 4 w x + P * iteratedDeriv 2 w x = 0

/-- Pinned (simply supported) ends: `w = w'' = 0` at both ends. Same as `SimplySupported`. -/
abbrev Pinned (w : ℝ → ℝ) : Prop := b.SimplySupported w

/-- Derivative of `x ↦ c sin(k x)`. -/
theorem hasDerivAt_sin_mul (c k x : ℝ) :
    HasDerivAt (fun y => c * sin (k * y)) (c * (k * cos (k * x))) x := by
  have := ((hasDerivAt_id' x).const_mul k).sin.const_mul c
  convert this using 1
  ring

theorem hasDerivAt_cos_mul (c k x : ℝ) :
    HasDerivAt (fun y => c * cos (k * y)) (-(c * (k * sin (k * x)))) x := by
  have := ((hasDerivAt_id' x).const_mul k).cos.const_mul c
  convert this using 1
  ring

/-- **Step 1**: a `C⁴` pinned solution of the buckling equation solves `w'' + (P/EI) w = 0`
on `[0, L]`. -/
theorem second_order_of_buckling {P : ℝ} {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
    (h : b.BucklingEquation P w) (hbc : b.Pinned w) :
    ∀ x ∈ Icc 0 b.L, deriv (deriv w) x = -(P / b.EI) * w x := by
  have hEI := b.EI_pos.ne'
  have d : ∀ k ≤ 3, Differentiable ℝ (deriv^[k] w) := fun k hk => by
    have hw' : ContDiff ℝ ((4 - k + k : ℕ) : WithTop ℕ∞) w := by
      rw [Nat.sub_add_cancel (by omega : k ≤ 4)]; exact_mod_cast hw
    exact (hw'.iterate_deriv' (4 - k) k).differentiable (by simp; omega)
  have d0 := d 0 (by norm_num); have d1 := d 1 (by norm_num)
  have d2 := d 2 (by norm_num); have d3 := d 3 (by norm_num)
  simp only [Function.iterate_zero, id, Function.iterate_succ, Function.comp_apply] at d0 d1 d2 d3
  -- `v = EI w'' + P w` has `v'' = 0`
  let v := fun x => b.EI * deriv (deriv w) x + P * w x
  let v' := fun x => b.EI * deriv (deriv (deriv w)) x + P * deriv w x
  have hv : ∀ x, HasDerivAt v (v' x) x := fun x =>
    ((d2 x).hasDerivAt.const_mul b.EI).add ((d0 x).hasDerivAt.const_mul P)
  have hv' : ∀ x ∈ Icc 0 b.L, HasDerivAt v' 0 x := fun x hx => by
    have := ((d3 x).hasDerivAt.const_mul b.EI).add ((d1 x).hasDerivAt.const_mul P)
    convert this using 1
    have e := h x hx
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at e
    linarith
  have hv'c : ∀ x ∈ Icc 0 b.L, v' x = v' 0 :=
    eqOn_Icc_of_hasDerivAt (F' := fun _ => 0) hv' (fun x _ => hasDerivAt_const x (v' 0)) rfl
  have hva : ∀ x ∈ Icc 0 b.L, v x = v 0 + v' 0 * x := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun _ => v' 0) (fun x hx => ?_) (fun x _ => ?_) (by simp)
    · rw [← hv'c x hx]; exact hv x
    · simpa using ((hasDerivAt_id x).const_mul (v' 0)).const_add (v 0)
  obtain ⟨h0, h20, hL, h2L⟩ := hbc
  have i2 : ∀ y, iteratedDeriv 2 w y = deriv (deriv w) y := fun y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hv0 : v 0 = 0 := by simp only [v]; rw [← i2, h20, h0]; ring
  have hvL : v b.L = 0 := by simp only [v]; rw [← i2, h2L, hL]; ring
  have hslope : v' 0 = 0 := by
    have := hva b.L ⟨b.L_pos.le, le_rfl⟩
    rw [hvL, hv0, zero_add] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h b.L_pos.ne'
  intro x hx
  have := hva x hx
  rw [hv0, hslope] at this
  simp only [v, zero_mul, add_zero] at this
  field_simp
  linarith

/-- **Step 2** (uniqueness for `u'' + k² u = 0`): if `u'' = -k² u` on `[0, L]` and
`u(0) = u'(0) = 0`, then `u = 0` on `[0, L]`, by conservation of `u'² + k² u²`. -/
theorem eq_zero_of_harmonic {k : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (h : ∀ x ∈ Icc 0 b.L, deriv (deriv u) x = -k ^ 2 * u x) (h0 : u 0 = 0) (h1 : deriv u 0 = 0) :
    ∀ x ∈ Icc 0 b.L, u x = 0 := by
  have du : Differentiable ℝ u := hu.differentiable (by norm_num)
  have ddu : Differentiable ℝ (deriv u) := (hu.deriv' (n := 1)).differentiable (by norm_num)
  let e := fun x => deriv u x ^ 2 + k ^ 2 * u x ^ 2
  have he : ∀ x ∈ Icc 0 b.L, e x = e 0 := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun _ => 0) (fun x hx => ?_)
      (fun x _ => hasDerivAt_const x (e 0)) rfl
    have := ((ddu x).hasDerivAt.pow 2).add (((du x).hasDerivAt.pow 2).const_mul (k ^ 2))
    convert this using 1
    rw [h x hx]
    push_cast
    ring
  intro x hx
  have hx' := he x hx
  simp only [e, h0, h1] at hx'
  norm_num at hx'
  by_cases hk : k = 0
  · -- `u'' = 0`, `u(0) = u'(0) = 0` ⇒ `u = 0`
    have : deriv u x = 0 := by nlinarith [sq_nonneg (deriv u x)]
    have h' : ∀ y ∈ Icc 0 b.L, deriv (deriv u) y = 0 := fun y hy => by rw [h y hy, hk]; ring
    have := eq_affine_of_deriv2_eq_zero hu h' x hx
    rw [this, h0, h1]; ring
  · have hk2 : 0 < k ^ 2 := by positivity
    have h3 : k ^ 2 * u x ^ 2 = 0 := by
      nlinarith [sq_nonneg (deriv u x), mul_nonneg hk2.le (sq_nonneg (u x))]
    have h4 : u x ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_left hk2.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h4

/-- **Buckling modes**: a nontrivial `C⁴` pinned solution of `EI w'''' + P w'' = 0` (`P > 0`)
exists iff `P = n² π² EI / L²` for some integer `n ≥ 1`; every solution is then
`w(x) = c sin(nπx/L)` on `[0, L]`. [TimoshenkoGere1961], §2.1. -/
theorem buckling_iff {P : ℝ} (hP : 0 < P) :
    (∃ w : ℝ → ℝ, ContDiff ℝ 4 w ∧ b.BucklingEquation P w ∧ b.Pinned w ∧
        ∃ x ∈ Icc 0 b.L, w x ≠ 0) ↔
      ∃ n : ℕ, 1 ≤ n ∧ P = n ^ 2 * π ^ 2 * b.EI / b.L ^ 2 := by
  have hEI := b.EI_pos
  have hL := b.L_pos
  constructor
  · rintro ⟨w, hw, h, hbc, x₀, hx₀, hne⟩
    set k := √(P / b.EI)
    have hk : 0 < k := Real.sqrt_pos.mpr (div_pos hP hEI)
    have hk2 : k ^ 2 = P / b.EI := Real.sq_sqrt (div_pos hP hEI).le
    have h2 := b.second_order_of_buckling hw h hbc
    -- `w = c sin(kx)` on `[0, L]`
    set c := deriv w 0 / k
    let u := fun x => w x - c * sin (k * x)
    have du : ∀ x, HasDerivAt u (deriv w x - c * (k * cos (k * x))) x := fun x =>
      ((hw.differentiable (by norm_num) x).hasDerivAt).sub (hasDerivAt_sin_mul c k x)
    have hdu : deriv u = fun x => deriv w x - c * (k * cos (k * x)) := funext fun x => (du x).deriv
    have ddu : ∀ x, HasDerivAt (deriv u) (deriv (deriv w) x + c * (k * (k * sin (k * x)))) x := by
      intro x
      rw [hdu]
      have := ((hw.deriv' (n := 3)).differentiable (by norm_num) x).hasDerivAt.sub
        ((hasDerivAt_cos_mul c k x).const_mul k)
      convert this using 1
      · ext y; simp; ring
      · ring
    have hu2 : ContDiff ℝ 2 u :=
      (hw.of_le (by norm_num)).sub (contDiff_const.mul ((contDiff_const.mul contDiff_id).sin))
    have hu : ∀ x ∈ Icc 0 b.L, u x = 0 := by
      refine b.eq_zero_of_harmonic (k := k) hu2 (fun x hx => ?_) (by simp [u, hbc.1]) ?_
      · rw [(ddu x).deriv, h2 x hx, ← hk2]
        simp only [u]
        ring
      · rw [hdu]; simp only [mul_zero, cos_zero, mul_one, c]; field_simp; ring
    have hwsin : ∀ x ∈ Icc 0 b.L, w x = c * sin (k * x) := fun x hx => by
      have := hu x hx; simp only [u] at this; linarith
    have hc : c ≠ 0 := by
      intro hc0
      apply hne
      rw [hwsin x₀ hx₀, hc0, zero_mul]
    have hsin : sin (k * b.L) = 0 := by
      have := hwsin b.L ⟨hL.le, le_rfl⟩
      rw [hbc.2.2.1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hc
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    have hnpos : 0 < (n : ℝ) := by
      have : 0 < (n : ℝ) * π := by rw [hn]; positivity
      exact pos_of_mul_pos_left this Real.pi_pos.le
    have hn1 : 1 ≤ n := by exact_mod_cast hnpos
    refine ⟨n.toNat, by omega, ?_⟩
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hcast]
    have : P = b.EI * k ^ 2 := by rw [hk2]; field_simp
    rw [this]
    have hkL : k = n * π / b.L := by rw [eq_div_iff hL.ne', hn]
    rw [hkL]
    field_simp
  · rintro ⟨n, hn, rfl⟩
    set k := n * π / b.L
    have hk : 0 < k := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨fun x => 1 * sin (k * x), ?_, ?_, ?_, ⟨b.L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩⟩
    · exact contDiff_const.mul ((contDiff_const.mul contDiff_id).sin)
    · -- derivatives of `sin(kx)`
      have d1 : deriv (fun x => 1 * sin (k * x)) = fun x => 1 * (k * cos (k * x)) :=
        funext fun x => (hasDerivAt_sin_mul 1 k x).deriv
      have d2 : deriv (fun x => 1 * (k * cos (k * x))) = fun x => -(k * (k * sin (k * x))) := by
        ext x
        have := (hasDerivAt_cos_mul k k x).const_mul 1
        rw [show (fun x => 1 * (k * cos (k * x))) = fun y => 1 * (k * cos (k * y)) from rfl,
          this.deriv]
        ring
      have d3 : deriv (fun x => -(k * (k * sin (k * x)))) =
          fun x => -(k * (k * (k * cos (k * x)))) := by
        ext x
        rw [show (fun x => -(k * (k * sin (k * x)))) = fun y => (-(k * k)) * sin (k * y) by
          ext y; ring, (hasDerivAt_sin_mul (-(k * k)) k x).deriv]
        ring
      have d4 : deriv (fun x => -(k * (k * (k * cos (k * x))))) =
          fun x => k * (k * (k * (k * sin (k * x)))) := by
        ext x
        rw [show (fun x => -(k * (k * (k * cos (k * x))))) =
            fun y => (-(k * k * k)) * cos (k * y) by
          ext y; ring, (hasDerivAt_cos_mul (-(k * k * k)) k x).deriv]
        ring
      intro x _
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, d1, d2, d3, d4]
      have hkk : k ^ 2 = (n : ℝ) ^ 2 * π ^ 2 / b.L ^ 2 := by simp only [k]; ring
      have : b.EI * k ^ 2 = (n : ℝ) ^ 2 * π ^ 2 * b.EI / b.L ^ 2 := by rw [hkk]; ring
      linear_combination (k ^ 2 * sin (k * x)) * this
    · have hsin : sin (k * b.L) = 0 := by
        rw [show k * b.L = (n : ℤ) * π by simp only [k]; push_cast; field_simp]
        exact Real.sin_int_mul_pi n
      refine ⟨by simp, ?_, by simp [hsin], ?_⟩
      · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
        rw [show deriv (deriv fun x => 1 * sin (k * x)) 0 = -(k * (k * sin (k * 0))) by
          rw [show deriv (fun x => 1 * sin (k * x)) = fun x => 1 * (k * cos (k * x)) from
            funext fun x => (hasDerivAt_sin_mul 1 k x).deriv]
          rw [((hasDerivAt_cos_mul k k 0).const_mul 1).deriv]; ring]
        simp
      · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
        rw [show deriv (fun x => 1 * sin (k * x)) = fun x => 1 * (k * cos (k * x)) from
          funext fun x => (hasDerivAt_sin_mul 1 k x).deriv]
        rw [((hasDerivAt_cos_mul k k b.L).const_mul 1).deriv, hsin]; ring
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have : k * (b.L / (2 * n)) = π / 2 := by
        simp only [k]; field_simp
      simp only [one_mul, this, Real.sin_pi_div_two]
      norm_num

/-- The set of **buckling loads**: compressive loads admitting a nontrivial pinned solution. -/
def bucklingLoads : Set ℝ :=
  {P | 0 < P ∧ ∃ w : ℝ → ℝ, ContDiff ℝ 4 w ∧ b.BucklingEquation P w ∧ b.Pinned w ∧
    ∃ x ∈ Icc 0 b.L, w x ≠ 0}

/-- **Euler's critical load**: the smallest buckling load of a pinned–pinned column is
`P_cr = π² EI / L²`. [TimoshenkoGere1961], §2.1. -/
theorem euler_critical_load : IsLeast b.bucklingLoads (π ^ 2 * b.EI / b.L ^ 2) := by
  have hEI := b.EI_pos
  have hL := b.L_pos
  have hpos : 0 < π ^ 2 * b.EI / b.L ^ 2 := by positivity
  refine ⟨⟨hpos, (b.buckling_iff hpos).mpr ⟨1, le_rfl, by simp⟩⟩, ?_⟩
  rintro P ⟨hP, hw⟩
  obtain ⟨n, hn, rfl⟩ := (b.buckling_iff hP).mp hw
  have hn' : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have hc : 0 < π ^ 2 * b.EI := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn' hc.le]

end EBBeam

end ContinuumMechanics.Beams
