import Mathlib.Analysis.Calculus.ContDiff.Operations
import ContinuumMechanics.Beams.Interval
import ContinuumMechanics.Beams.Poly

/-!
# Euler–Bernoulli beams: equation, boundary conditions, uniqueness

A prismatic Euler–Bernoulli beam of length `L > 0` and bending stiffness `EI > 0` under a
transverse load `q` (force per unit length, positive in the direction of positive deflection)
has deflection `w` satisfying `EI w'''' = q` on `[0, L]` ([TimoshenkoGere1997], §9.2;
[Reddy2007], §3.3). The bending moment is `M = -EI w''` and the shear force `V = -EI w'''`.

Derivatives are Mathlib's `iteratedDeriv k w` (`= deriv^[k] w`) of a function defined on all of
`ℝ` (see `ROADMAP.md`, review decision 2).

## Boundary conditions

* `SimplySupported`: `w = w'' = 0` at both ends.
* `Cantilever P`: clamped at `0` (`w = w' = 0`), free at `L` with tip load `P`
  (`w''(L) = 0`, `EI w'''(L) = -P`).
* `ClampedClamped`: `w = w' = 0` at both ends.
* `ClampedPinned`: `w = w' = 0` at `0`, `w = w'' = 0` at `L`.

## Main results

* `EBBeam.cubic_of_equation_zero`: solutions of `EI w'''' = 0` are cubics on `[0, L]`, with
  formulas for `w, w', w'', w'''`.
* Uniqueness of `C⁴` solutions for each boundary-condition set: `EBBeam.simplySupported_unique`,
  `EBBeam.cantilever_unique`, `EBBeam.clampedClamped_unique`, `EBBeam.clampedPinned_unique`.

## References

* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, Ch. 9.
* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.3.
-/

open Set

namespace ContinuumMechanics.Beams

/-- A prismatic **Euler–Bernoulli beam** of length `L` and bending stiffness `EI`. -/
structure EBBeam where
  /-- Length. -/
  L : ℝ
  /-- Bending stiffness `E I`. -/
  EI : ℝ
  L_pos : 0 < L
  EI_pos : 0 < EI

namespace EBBeam

variable (b : EBBeam)

/-- The **Euler–Bernoulli beam equation** `EI w'''' = q` on `[0, L]`. [TimoshenkoGere1997], §9.2. -/
def Equation (q w : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 b.L, b.EI * iteratedDeriv 4 w x = q x

/-- Simply supported (pinned–pinned) ends: `w = 0`, `M = -EI w'' = 0` at `x = 0, L`. -/
def SimplySupported (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ iteratedDeriv 2 w 0 = 0 ∧ w b.L = 0 ∧ iteratedDeriv 2 w b.L = 0

/-- Cantilever clamped at `0` and free at `L` with tip load `P`: `w(0) = w'(0) = 0`,
`M(L) = 0`, `V(L) = -EI w'''(L) = P`. -/
def Cantilever (P : ℝ) (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ iteratedDeriv 1 w 0 = 0 ∧ iteratedDeriv 2 w b.L = 0 ∧
    b.EI * iteratedDeriv 3 w b.L = -P

/-- Both ends clamped: `w = w' = 0` at `x = 0, L`. -/
def ClampedClamped (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ iteratedDeriv 1 w 0 = 0 ∧ w b.L = 0 ∧ iteratedDeriv 1 w b.L = 0

/-- Clamped at `0`, pinned at `L` (propped cantilever). -/
def ClampedPinned (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ iteratedDeriv 1 w 0 = 0 ∧ w b.L = 0 ∧ iteratedDeriv 2 w b.L = 0

/-! ### Homogeneous solutions are cubics -/

/-- If `w'''' = 0` on `[0, L]`, then `w, w', w'', w'''` are given there by the cubic Taylor
polynomial at `0`. -/
theorem cubic_of_iteratedDeriv_four_eq_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w)
    (h : ∀ x ∈ Icc 0 b.L, iteratedDeriv 4 w x = 0) (x : ℝ) (hx : x ∈ Icc 0 b.L) :
    w x = w 0 + iteratedDeriv 1 w 0 * x + iteratedDeriv 2 w 0 * x ^ 2 / 2
        + iteratedDeriv 3 w 0 * x ^ 3 / 6 ∧
      iteratedDeriv 1 w x = iteratedDeriv 1 w 0 + iteratedDeriv 2 w 0 * x
        + iteratedDeriv 3 w 0 * x ^ 2 / 2 ∧
      iteratedDeriv 2 w x = iteratedDeriv 2 w 0 + iteratedDeriv 3 w 0 * x ∧
      iteratedDeriv 3 w x = iteratedDeriv 3 w 0 := by
  simp only [iteratedDeriv_eq_iterate] at h ⊢
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have key : ∀ j n : ℕ, j + n = 3 → ∀ y ∈ Icc 0 b.L, deriv^[j] w y =
      ∑ k ∈ Finset.range (n + 1), deriv^[k + j] w 0 * (y - 0) ^ k / k.factorial := by
    intro j n hjn y hy
    have hc : ContDiff ℝ (n + 1) (deriv^[j] w) := by
      have : ContDiff ℝ ((n + 1 : ℕ) + j : ℕ) w := by
        rw [show n + 1 + j = 4 by omega]; exact_mod_cast hw
      exact_mod_cast this.iterate_deriv' (n + 1) j
    have := eq_taylor_of_iterate_deriv_eq_zero n hc (fun z hz => by
      rw [← Function.iterate_add_apply, show n + 1 + j = 4 by omega]; exact h z hz) y hy
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Function.iterate_add_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key 0 3 rfl x hx
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linear_combination this
  · have := key 1 2 rfl x hx
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linear_combination this
  · have := key 2 1 rfl x hx
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linear_combination this
  · have := key 3 0 rfl x hx
    simpa [Function.iterate_succ_apply'] using this

/-- The difference of two solutions with the same load solves the homogeneous equation. -/
theorem equation_sub {q w₁ w₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ 4 w₁) (hw₂ : ContDiff ℝ 4 w₂)
    (h₁ : b.Equation q w₁) (h₂ : b.Equation q w₂) :
    ∀ x ∈ Icc 0 b.L, iteratedDeriv 4 (w₁ - w₂) x = 0 := by
  intro x hx
  rw [iteratedDeriv_sub (hw₁.contDiffAt) (hw₂.contDiffAt)]
  have e₁ := h₁ x hx
  have e₂ := h₂ x hx
  have : b.EI * (iteratedDeriv 4 w₁ x - iteratedDeriv 4 w₂ x) = 0 := by rw [mul_sub]; linarith
  exact (mul_eq_zero.mp this).resolve_left b.EI_pos.ne'

theorem iteratedDeriv_sub_apply {w₁ w₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ 4 w₁) (hw₂ : ContDiff ℝ 4 w₂)
    (k : ℕ) (hk : k ≤ 4) (x : ℝ) :
    iteratedDeriv k (w₁ - w₂) x = iteratedDeriv k w₁ x - iteratedDeriv k w₂ x :=
  iteratedDeriv_sub ((hw₁.of_le (by exact_mod_cast hk)).contDiffAt)
    ((hw₂.of_le (by exact_mod_cast hk)).contDiffAt)

/-! ### Uniqueness -/

section Unique

variable {q w₁ w₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ 4 w₁) (hw₂ : ContDiff ℝ 4 w₂)
  (h₁ : b.Equation q w₁) (h₂ : b.Equation q w₂)
include hw₁ hw₂ h₁ h₂

/-- Shared step: with `d = w₁ - w₂`, the four Taylor coefficients `cₖ = d⁽ᵏ⁾(0)` determine `d`;
if all vanish then `w₁ = w₂` on `[0, L]`. -/
theorem eq_of_coeffs_eq_zero (c0 : (w₁ - w₂) 0 = 0) (c1 : iteratedDeriv 1 (w₁ - w₂) 0 = 0)
    (c2 : iteratedDeriv 2 (w₁ - w₂) 0 = 0) (c3 : iteratedDeriv 3 (w₁ - w₂) 0 = 0) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x := by
  intro x hx
  have hd : ContDiff ℝ 4 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have := (b.cubic_of_iteratedDeriv_four_eq_zero hd (b.equation_sub hw₁ hw₂ h₁ h₂) x hx).1
  rw [c0, c1, c2, c3] at this
  simpa [sub_eq_zero] using this

/-- **Uniqueness** for the simply supported beam. -/
theorem simplySupported_unique (bc₁ : b.SimplySupported w₁) (bc₂ : b.SimplySupported w₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x := by
  have hd : ContDiff ℝ 4 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  obtain ⟨e0, -, e2, -⟩ := b.cubic_of_iteratedDeriv_four_eq_zero hd (b.equation_sub hw₁ hw₂ h₁ h₂)
    b.L hL
  have s := iteratedDeriv_sub_apply hw₁ hw₂
  have c0 : (w₁ - w₂) 0 = 0 := by rw [Pi.sub_apply, bc₁.1, bc₂.1, sub_self]
  have c2 : iteratedDeriv 2 (w₁ - w₂) 0 = 0 := by
    rw [s _ (by norm_num), bc₁.2.1, bc₂.2.1, sub_self]
  have dL : (w₁ - w₂) b.L = 0 := by rw [Pi.sub_apply, bc₁.2.2.1, bc₂.2.2.1, sub_self]
  have d2L : iteratedDeriv 2 (w₁ - w₂) b.L = 0 := by
    rw [s _ (by norm_num), bc₁.2.2.2, bc₂.2.2.2, sub_self]
  rw [c0, c2, dL] at e0
  rw [c2, d2L] at e2
  have hL0 := b.L_pos.ne'
  have c3 : iteratedDeriv 3 (w₁ - w₂) 0 = 0 := by
    rcases mul_eq_zero.mp (by linarith : iteratedDeriv 3 (w₁ - w₂) 0 * b.L = 0) with h | h
    · exact h
    · exact absurd h hL0
  have c1 : iteratedDeriv 1 (w₁ - w₂) 0 = 0 := by
    rw [c3] at e0
    rcases mul_eq_zero.mp (by linarith : iteratedDeriv 1 (w₁ - w₂) 0 * b.L = 0) with h | h
    · exact h
    · exact absurd h hL0
  exact b.eq_of_coeffs_eq_zero hw₁ hw₂ h₁ h₂ c0 c1 c2 c3

/-- **Uniqueness** for the cantilever with tip load. -/
theorem cantilever_unique {P : ℝ} (bc₁ : b.Cantilever P w₁) (bc₂ : b.Cantilever P w₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x := by
  have hd : ContDiff ℝ 4 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  obtain ⟨-, -, e2, e3⟩ := b.cubic_of_iteratedDeriv_four_eq_zero hd
    (b.equation_sub hw₁ hw₂ h₁ h₂) b.L hL
  have s := iteratedDeriv_sub_apply hw₁ hw₂
  have c0 : (w₁ - w₂) 0 = 0 := by rw [Pi.sub_apply, bc₁.1, bc₂.1, sub_self]
  have c1 : iteratedDeriv 1 (w₁ - w₂) 0 = 0 := by
    rw [s _ (by norm_num), bc₁.2.1, bc₂.2.1, sub_self]
  have d2L : iteratedDeriv 2 (w₁ - w₂) b.L = 0 := by
    rw [s _ (by norm_num), bc₁.2.2.1, bc₂.2.2.1, sub_self]
  have d3L : iteratedDeriv 3 (w₁ - w₂) b.L = 0 := by
    rw [s _ (by norm_num)]
    have := bc₁.2.2.2.trans bc₂.2.2.2.symm
    have : b.EI * (iteratedDeriv 3 w₁ b.L - iteratedDeriv 3 w₂ b.L) = 0 := by
      rw [mul_sub]; linarith
    exact (mul_eq_zero.mp this).resolve_left b.EI_pos.ne'
  have c3 : iteratedDeriv 3 (w₁ - w₂) 0 = 0 := by rw [← e3, d3L]
  have c2 : iteratedDeriv 2 (w₁ - w₂) 0 = 0 := by rw [c3, d2L] at e2; linarith
  exact b.eq_of_coeffs_eq_zero hw₁ hw₂ h₁ h₂ c0 c1 c2 c3

/-- **Uniqueness** for the clamped–clamped beam. -/
theorem clampedClamped_unique (bc₁ : b.ClampedClamped w₁) (bc₂ : b.ClampedClamped w₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x := by
  have hd : ContDiff ℝ 4 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  obtain ⟨e0, e1, -, -⟩ := b.cubic_of_iteratedDeriv_four_eq_zero hd
    (b.equation_sub hw₁ hw₂ h₁ h₂) b.L hL
  have s := iteratedDeriv_sub_apply hw₁ hw₂
  have c0 : (w₁ - w₂) 0 = 0 := by rw [Pi.sub_apply, bc₁.1, bc₂.1, sub_self]
  have c1 : iteratedDeriv 1 (w₁ - w₂) 0 = 0 := by
    rw [s _ (by norm_num), bc₁.2.1, bc₂.2.1, sub_self]
  have dL : (w₁ - w₂) b.L = 0 := by rw [Pi.sub_apply, bc₁.2.2.1, bc₂.2.2.1, sub_self]
  have d1L : iteratedDeriv 1 (w₁ - w₂) b.L = 0 := by
    rw [s _ (by norm_num), bc₁.2.2.2, bc₂.2.2.2, sub_self]
  rw [c0, c1, dL] at e0
  rw [c1, d1L] at e1
  set c2 := iteratedDeriv 2 (w₁ - w₂) 0
  set c3 := iteratedDeriv 3 (w₁ - w₂) 0
  have hL0 : b.L ^ 3 ≠ 0 := pow_ne_zero 3 b.L_pos.ne'
  -- `0 = c₂ L²/2 + c₃ L³/6` and `0 = c₂ L + c₃ L²/2` force `c₃ L³ = 0`
  have h3 : c3 * b.L ^ 3 = 0 := by linear_combination 12 * e0 - 6 * b.L * e1
  have hc3 : c3 = 0 := (mul_eq_zero.mp h3).resolve_right hL0
  have hc2 : c2 = 0 := by
    rw [hc3] at e1
    rcases mul_eq_zero.mp (by linarith : c2 * b.L = 0) with h | h
    · exact h
    · exact absurd h b.L_pos.ne'
  exact b.eq_of_coeffs_eq_zero hw₁ hw₂ h₁ h₂ c0 c1 hc2 hc3

/-- **Uniqueness** for the clamped–pinned (propped cantilever) beam. -/
theorem clampedPinned_unique (bc₁ : b.ClampedPinned w₁) (bc₂ : b.ClampedPinned w₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x := by
  have hd : ContDiff ℝ 4 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  obtain ⟨e0, -, e2, -⟩ := b.cubic_of_iteratedDeriv_four_eq_zero hd
    (b.equation_sub hw₁ hw₂ h₁ h₂) b.L hL
  have s := iteratedDeriv_sub_apply hw₁ hw₂
  have c0 : (w₁ - w₂) 0 = 0 := by rw [Pi.sub_apply, bc₁.1, bc₂.1, sub_self]
  have c1 : iteratedDeriv 1 (w₁ - w₂) 0 = 0 := by
    rw [s _ (by norm_num), bc₁.2.1, bc₂.2.1, sub_self]
  have dL : (w₁ - w₂) b.L = 0 := by rw [Pi.sub_apply, bc₁.2.2.1, bc₂.2.2.1, sub_self]
  have d2L : iteratedDeriv 2 (w₁ - w₂) b.L = 0 := by
    rw [s _ (by norm_num), bc₁.2.2.2, bc₂.2.2.2, sub_self]
  rw [c0, c1, dL] at e0
  rw [d2L] at e2
  set c2 := iteratedDeriv 2 (w₁ - w₂) 0
  set c3 := iteratedDeriv 3 (w₁ - w₂) 0
  have hL0 : b.L ^ 3 ≠ 0 := pow_ne_zero 3 b.L_pos.ne'
  -- `0 = c₂ L²/2 + c₃ L³/6` and `0 = c₂ + c₃ L` force `c₃ L³ = 0`
  have h3 : c3 * b.L ^ 3 = 0 := by linear_combination 3 * e0 - (3 * b.L ^ 2 / 2) * e2
  have hc3 : c3 = 0 := (mul_eq_zero.mp h3).resolve_right hL0
  have hc2 : c2 = 0 := by rw [hc3] at e2; linarith
  exact b.eq_of_coeffs_eq_zero hw₁ hw₂ h₁ h₂ c0 c1 hc2 hc3

end Unique

end EBBeam

end ContinuumMechanics.Beams
