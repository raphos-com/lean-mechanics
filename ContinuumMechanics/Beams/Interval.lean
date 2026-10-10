import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Factorial.Basic

/-!
# One-dimensional calculus on an interval

Helpers shared by the bar and beam theories. Displacement fields are functions `ℝ → ℝ` defined on
the whole line (only their values on `[0, L]` matter; see `ROADMAP.md`, review decision 2), so the
ordinary derivative `deriv` is used throughout, and `deriv^[k]` is the `k`-th derivative.

## Main results

* `Beams.eqOn_Icc_of_hasDerivAt`: two functions with the same derivative on `[a, b]` that agree
  at `a` agree on `[a, b]`.
* `Beams.eq_taylor_of_iterate_deriv_eq_zero`: if `w⁽ⁿ⁺¹⁾ = 0` on `[a, b]`, then `w` equals its
  Taylor polynomial of degree `n` at `a` on `[a, b]`. In particular `w'' = 0` makes `w` affine and
  `w'''' = 0` makes `w` cubic — the basis of every uniqueness proof for bars and beams.
-/

open Set

namespace ContinuumMechanics.Beams

variable {a b : ℝ}

/-- Two functions with the same derivative on `[a, b]` that agree at `a` agree on `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivAt {F G F' : ℝ → ℝ}
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (hG : ∀ x ∈ Icc a b, HasDerivAt G (F' x) x)
    (ha : F a = G a) : ∀ x ∈ Icc a b, F x = G x :=
  eq_of_has_deriv_right_eq (fun x hx => (hF x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => (hG x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hG x hx).continuousAt.continuousWithinAt) ha

/-- Derivative of the Taylor monomial `c (x - a)^(k+1) / (k+1)!`. -/
theorem hasDerivAt_taylor_monomial (c a x : ℝ) (k : ℕ) :
    HasDerivAt (fun y => c * (y - a) ^ (k + 1) / (k + 1).factorial)
      (c * (x - a) ^ k / k.factorial) x := by
  have h1 : HasDerivAt (fun y => (y - a) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (x - a) ^ k) x := by
    simpa using ((hasDerivAt_id x).sub_const a).fun_pow (k + 1)
  have h2 := (h1.const_mul c).div_const ((k + 1).factorial : ℝ)
  convert h2 using 1
  have : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

/-- **Taylor's theorem for vanishing higher derivative**: if `w` is `Cⁿ⁺¹` and `w⁽ⁿ⁺¹⁾ = 0` on
`[a, b]`, then `w(x) = ∑_{k ≤ n} w⁽ᵏ⁾(a) (x - a)ᵏ / k!` on `[a, b]`. -/
theorem eq_taylor_of_iterate_deriv_eq_zero :
    ∀ (n : ℕ) {w : ℝ → ℝ}, ContDiff ℝ (n + 1) w → (∀ x ∈ Icc a b, deriv^[n + 1] w x = 0) →
      ∀ x ∈ Icc a b, w x = ∑ k ∈ Finset.range (n + 1), deriv^[k] w a * (x - a) ^ k / k.factorial
  | 0, w, hw, h => by
    have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
    intro x hx
    have := eqOn_Icc_of_hasDerivAt (F := w) (G := fun _ => w a) (F' := fun _ => 0)
      (fun y hy => by
        have := (hd y).hasDerivAt
        rwa [show deriv w y = 0 from h y hy] at this)
      (fun y _ => hasDerivAt_const y (w a)) rfl x hx
    simpa using this
  | n + 1, w, hw, h => by
    have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
    have hw' : ContDiff ℝ (n + 1) (deriv w) := by
      have : ContDiff ℝ ((n + 1 : ℕ) + 1) w := by exact_mod_cast hw
      exact this.deriv'
    have h' : ∀ x ∈ Icc a b, deriv^[n + 1] (deriv w) x = 0 := fun x hx => by
      rw [← Function.iterate_succ_apply]; exact h x hx
    have ih := eq_taylor_of_iterate_deriv_eq_zero n hw' h'
    intro x hx
    have key := eqOn_Icc_of_hasDerivAt (F := w)
      (G := fun y => w a + ∑ k ∈ Finset.range (n + 1),
        deriv^[k + 1] w a * (y - a) ^ (k + 1) / (k + 1).factorial)
      (F' := fun y => ∑ k ∈ Finset.range (n + 1), deriv^[k + 1] w a * (y - a) ^ k / k.factorial)
      (fun y hy => by
        rw [show (∑ k ∈ Finset.range (n + 1), deriv^[k + 1] w a * (y - a) ^ k / k.factorial)
            = deriv w y by
          rw [ih y hy]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Function.iterate_succ_apply]]
        exact (hd y).hasDerivAt)
      (fun y _ => by
        have := (HasDerivAt.sum (u := Finset.range (n + 1))
          (A := fun k z => deriv^[k + 1] w a * (z - a) ^ (k + 1) / (k + 1).factorial)
          fun k _ => hasDerivAt_taylor_monomial _ a y k).const_add (w a)
        convert this using 1
        ext z
        simp [Finset.sum_apply])
      (by simp) x hx
    rw [key, Finset.sum_range_succ' _ (n + 1)]
    simp [add_comm]

/-- If `w'' = 0` on `[a, b]` then `w` is affine there. -/
theorem eq_affine_of_deriv2_eq_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w)
    (h : ∀ x ∈ Icc a b, deriv (deriv w) x = 0) :
    ∀ x ∈ Icc a b, w x = w a + deriv w a * (x - a) := by
  intro x hx
  have := eq_taylor_of_iterate_deriv_eq_zero 1 (by exact_mod_cast hw) (fun y hy => h y hy) x hx
  simpa [Finset.sum_range_succ] using this

/-- If `w'''' = 0` on `[a, b]` then `w` is a cubic there. -/
theorem eq_cubic_of_deriv4_eq_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
    (h : ∀ x ∈ Icc a b, deriv (deriv (deriv (deriv w))) x = 0) :
    ∀ x ∈ Icc a b, w x = w a + deriv w a * (x - a) + deriv (deriv w) a * (x - a) ^ 2 / 2
      + deriv (deriv (deriv w)) a * (x - a) ^ 3 / 6 := by
  intro x hx
  have := eq_taylor_of_iterate_deriv_eq_zero 3 (by exact_mod_cast hw) (fun y hy => h y hy) x hx
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at this
  rw [this]
  simp [Nat.factorial]

end ContinuumMechanics.Beams
