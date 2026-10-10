import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Polynomial deflections

Closed-form bar and beam solutions are polynomials. Writing them as `x ↦ p.eval x` with
`p : ℝ[X]` turns every derivative into the formal derivative `Polynomial.derivative`, which `simp`
computes symbolically.
-/

open Polynomial

namespace ContinuumMechanics.Beams

/-- The `k`-th derivative of a polynomial function is the polynomial function of the `k`-th formal
derivative. -/
theorem iteratedDeriv_eval (p : ℝ[X]) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y => p.eval y) x = (derivative^[k] p).eval x := by
  rw [iteratedDeriv_eq_iterate]
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,
      show deriv (fun y => p.eval y) = fun y => (derivative p).eval y from funext fun y => p.deriv,
      ih, ← Function.iterate_succ_apply]

theorem deriv_eval (p : ℝ[X]) (x : ℝ) :
    deriv (fun y => p.eval y) x = (derivative p).eval x := p.deriv

/-- Polynomial functions are smooth. -/
theorem contDiff_eval (p : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (fun y => p.eval y) := by
  simpa using p.contDiff_aeval (𝕜 := ℝ) n

/-- `beam_poly` closes identities about polynomial deflections `x ↦ p.eval x`: it rewrites iterated
derivatives as formal derivatives, evaluates, and finishes with `ring1` (after `field_simp` when
stiffness or length parameters appear in denominators; their nonvanishing must be in context). -/
macro "beam_poly" : tactic => `(tactic| (
  (try simp only [ContinuumMechanics.Beams.iteratedDeriv_eval, ContinuumMechanics.Beams.deriv_eval,
    Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]) <;>
  (try simp [Polynomial.derivative_mul, Polynomial.derivative_pow, -mul_eq_zero,
    -div_eq_zero_iff]) <;>
  first | ring1 | (field_simp; done) | (field_simp; ring1)))

end ContinuumMechanics.Beams
