import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Winding numbers of polynomial Bloch determinants

The topological invariants of Maxwell lattices ([KaneLubensky2014]) are winding numbers of the
determinant of the Bloch compatibility matrix around a cycle of the Brillouin zone. Along a cycle,
`z = e^{iθ}` runs over the unit circle; when the determinant is a polynomial in `z` (after
multiplying by a power of `z`), its winding number is

`ν(p) = (2πi)⁻¹ ∮_{|z|=1} p'(z) / p(z) dz`.

**Argument principle for polynomials** (`winding_eq_card_roots`): if `p ≠ 0` has no root on the
unit circle, `ν(p)` is the number of roots of `p` in the open unit disk, counted with multiplicity.
In particular it is a natural number, and `ν(p q) = ν(p) + ν(q)` (`winding_mul`).

## References

* [KaneLubensky2014] C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
  lattices*, Nature Physics 10 (2014).
-/

open Complex Polynomial Metric

noncomputable section

namespace DiscreteMechanics

/-- The winding number `(2πi)⁻¹ ∮_{|z|=1} p'(z)/p(z) dz` of a polynomial around the unit circle. -/
def winding (p : ℂ[X]) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(0, 1), p.derivative.eval z / p.eval z

/-- `(2πi)⁻¹ ∮ (z - a)⁻¹ dz` is `1` inside the unit circle and `0` outside. -/
theorem winding_linear {a : ℂ} (ha : ‖a‖ ≠ 1) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(0, 1), (z - a)⁻¹) = if ‖a‖ < 1 then 1 else 0 := by
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  split_ifs with h
  · rw [circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h), inv_mul_cancel₀ h2pi]
  · have hgt : 1 < ‖a‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm ha)
    have hne : ∀ z ∈ closedBall (0 : ℂ) 1, z - a ≠ 0 := fun z hz h0 => by
      rw [sub_eq_zero] at h0
      rw [mem_closedBall, dist_zero_right, h0] at hz
      linarith
    have hd : DiffContOnCl ℂ (fun z : ℂ => (z - a)⁻¹) (ball 0 1) := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · apply DifferentiableAt.differentiableWithinAt
        apply DifferentiableAt.inv
        · fun_prop
        · exact hne z (ball_subset_closedBall hz)
      · rw [closure_ball _ one_ne_zero] at hz
        exact ((continuousAt_id.sub continuousAt_const).inv₀ (hne z hz)).continuousWithinAt
    rw [hd.circleIntegral_eq_zero zero_le_one, mul_zero]

/-- `∏ (X - a)` over a multiset of roots. -/
def rootProd (s : Multiset ℂ) : ℂ[X] := (s.map fun a => X - C a).prod

theorem eval_rootProd_ne_zero {s : Multiset ℂ} {z : ℂ} (h : ∀ a ∈ s, a ≠ z) :
    (rootProd s).eval z ≠ 0 := by
  intro h0
  rw [rootProd, eval_multiset_prod, Multiset.prod_eq_zero_iff] at h0
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C, Multiset.mem_map,
    ] at h0
  obtain ⟨a, ha, h0⟩ := h0
  exact h a ha (sub_eq_zero.mp h0).symm

theorem continuousOn_logDeriv {p : ℂ[X]} (hp : ∀ z ∈ Metric.sphere (0 : ℂ) 1, p.eval z ≠ 0) :
    ContinuousOn (fun z => p.derivative.eval z / p.eval z) (Metric.sphere 0 1) :=
  (p.derivative.continuous.continuousOn).div p.continuous.continuousOn hp

/-- The argument principle for `∏ (X - a)`. -/
theorem winding_rootProd (s : Multiset ℂ) (hs : ∀ a ∈ s, ‖a‖ ≠ 1) :
    winding (rootProd s) = (Multiset.card (s.filter fun a => ‖a‖ < 1) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty =>
    have h := circleIntegral.integral_const_mul 0 (fun _ => 0) 0 1
    simp only [zero_mul] at h
    simp [winding, rootProd, h]
  | cons a s ih =>
    have ha : ‖a‖ ≠ 1 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, ‖b‖ ≠ 1 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have hQ : ∀ z ∈ Metric.sphere (0 : ℂ) 1, (rootProd s).eval z ≠ 0 := fun z hz =>
      eval_rootProd_ne_zero fun b hb h => hs' b hb (by rw [h]; simpa using hz)
    have hza : ∀ z ∈ Metric.sphere (0 : ℂ) 1, z - a ≠ 0 := fun z hz h => ha (by
      rw [sub_eq_zero] at h; rw [← h]; simpa using hz)
    -- on the circle, the log-derivative splits
    have hsplit : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
        (rootProd (a ::ₘ s)).derivative.eval z / (rootProd (a ::ₘ s)).eval z =
          (z - a)⁻¹ + (rootProd s).derivative.eval z / (rootProd s).eval z := fun z hz => by
      have h1 := hza z hz; have h2 := hQ z hz
      simp only [rootProd, Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
        derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
        eval_C] at h2 ⊢
      field_simp
    have i1 : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) 0 1 :=
      ((continuousOn_id.sub continuousOn_const).inv₀ hza).circleIntegrable zero_le_one
    have i2 : CircleIntegrable
        (fun z => (rootProd s).derivative.eval z / (rootProd s).eval z) 0 1 :=
      (continuousOn_logDeriv hQ).circleIntegrable zero_le_one
    have e : winding (rootProd (a ::ₘ s)) =
        (2 * Real.pi * I)⁻¹ * (∮ z in C(0, 1), (z - a)⁻¹) + winding (rootProd s) := by
      rw [winding, circleIntegral.integral_congr zero_le_one hsplit,
        circleIntegral.integral_add i1 i2, mul_add, winding]
    rw [e, winding_linear ha, ih hs', Multiset.filter_cons]
    split_ifs with h <;> simp [add_comm]

/-- **Argument principle for polynomials**: the winding number of `p ≠ 0` around the unit circle,
on which it does not vanish, is the number of its roots in the unit disk. -/
theorem winding_eq_card_roots {p : ℂ[X]} (hp : p ≠ 0)
    (hc : ∀ z ∈ Metric.sphere (0 : ℂ) 1, p.eval z ≠ 0) :
    winding p = (Multiset.card (p.roots.filter fun a => ‖a‖ < 1) : ℂ) := by
  have hroots : ∀ a ∈ p.roots, ‖a‖ ≠ 1 := fun a ha h =>
    hc a (by simpa using h) ((mem_roots hp).mp ha)
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p))
  rw [← winding_rootProd _ hroots]
  unfold winding
  congr 1
  refine circleIntegral.integral_congr zero_le_one fun z hz => ?_
  conv_lhs => rw [← hfac]
  simp only [rootProd, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  rw [mul_div_mul_left _ _ hlc]

/-- Winding numbers add under products. -/
theorem winding_mul {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpc : ∀ z ∈ Metric.sphere (0 : ℂ) 1, p.eval z ≠ 0)
    (hqc : ∀ z ∈ Metric.sphere (0 : ℂ) 1, q.eval z ≠ 0) :
    winding (p * q) = winding p + winding q := by
  have hpq : ∀ z ∈ Metric.sphere (0 : ℂ) 1, (p * q).eval z ≠ 0 := fun z hz => by
    rw [eval_mul]; exact mul_ne_zero (hpc z hz) (hqc z hz)
  rw [winding_eq_card_roots (mul_ne_zero hp hq) hpq, winding_eq_card_roots hp hpc,
    winding_eq_card_roots hq hqc, roots_mul (mul_ne_zero hp hq), Multiset.filter_add,
    Multiset.card_add]
  push_cast
  ring

end DiscreteMechanics
