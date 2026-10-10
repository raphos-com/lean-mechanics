import Mathlib.Analysis.Calculus.ContDiff.Operations
import ContinuumMechanics.Beams.Interval

/-!
# The axial bar

A straight bar of length `L > 0` and constant axial stiffness `EA > 0` carrying a distributed
axial load `f` (force per unit length) is in equilibrium when its axial displacement `u` satisfies
`(EA u')' + f = 0`, i.e. `EA u'' + f = 0` on `[0, L]`; the axial force is `N = EA u'`
([TimoshenkoGere1997], Ch. 2; [Reddy2007], §3.2).

## Main definitions

* `Beams.Bar`: geometry and stiffness of a bar.
* `Bar.Equilibrium`: the strong form `EA u'' + f = 0` on `[0, L]`.
* `Bar.FixedFree P`: boundary conditions `u(0) = 0`, `EA u'(L) = P` (end load `P`).
* `Bar.FixedFixed`: boundary conditions `u(0) = 0 = u(L)`.

## Main results

* Closed-form solutions, proved to satisfy the equation and boundary conditions:
  `Bar.fixedFree_uniform` (uniform load `q` plus end load `P`),
  `Bar.fixedFree_linear` (linearly increasing load `q₀ x / L`),
  `Bar.fixedFixed_uniform` (uniform load `q`).
* `Bar.fixedFree_unique`, `Bar.fixedFixed_unique`: uniqueness of `C²` solutions.

## References

* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, Ch. 2.
* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.2.
-/

open Set

namespace ContinuumMechanics.Beams

/-- A straight **bar** of length `L` and constant axial stiffness `EA` (Young's modulus times
cross-sectional area). -/
structure Bar where
  /-- Length. -/
  L : ℝ
  /-- Axial stiffness `E A`. -/
  EA : ℝ
  L_pos : 0 < L
  EA_pos : 0 < EA

namespace Bar

variable (b : Bar)

/-- **Equilibrium of a bar** (strong form): `EA u'' + f = 0` on `[0, L]`.
[TimoshenkoGere1997], Ch. 2. -/
def Equilibrium (f u : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 b.L, b.EA * deriv (deriv u) x + f x = 0

/-- Fixed–free bar with end load `P`: `u(0) = 0`, `N(L) = EA u'(L) = P`. -/
def FixedFree (P : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = 0 ∧ b.EA * deriv u b.L = P

/-- Fixed–fixed bar: `u(0) = 0`, `u(L) = 0`. -/
def FixedFixed (u : ℝ → ℝ) : Prop :=
  u 0 = 0 ∧ u b.L = 0

/-! ### Closed-form solutions -/

/-- Displacement of a fixed–free bar under uniform load `q` and end load `P`:
`u(x) = ((P + q L) x - q x² / 2) / EA`. -/
noncomputable def fixedFreeUniformSol (q P : ℝ) (x : ℝ) : ℝ :=
  ((P + q * b.L) * x - q * x ^ 2 / 2) / b.EA

theorem deriv_fixedFreeUniformSol (q P : ℝ) :
    deriv (b.fixedFreeUniformSol q P) = fun x => ((P + q * b.L) - q * x) / b.EA := by
  ext x
  have h := ((((hasDerivAt_id x).const_mul (P + q * b.L)).sub
    (((hasDerivAt_pow 2 x).const_mul q).div_const 2)).div_const b.EA)
  rw [show deriv (b.fixedFreeUniformSol q P) x = _ from h.deriv]
  norm_num
  try ring

theorem fixedFree_uniform (q P : ℝ) :
    b.Equilibrium (fun _ => q) (b.fixedFreeUniformSol q P) ∧
      b.FixedFree P (b.fixedFreeUniformSol q P) := by
  have hEA := b.EA_pos.ne'
  have h2 : deriv (fun x => ((P + q * b.L) - q * x) / b.EA) = fun _ => -q / b.EA := by
    ext x
    have h : HasDerivAt (fun x => ((P + q * b.L) - q * x) / b.EA) ((0 - q * 1) / b.EA) x :=
      ((hasDerivAt_const x _).sub ((hasDerivAt_id x).const_mul q)).div_const b.EA
    rw [h.deriv]
    ring
  refine ⟨fun x _ => ?_, ?_, ?_⟩
  · rw [deriv_fixedFreeUniformSol, h2]
    field_simp
    ring
  · simp [fixedFreeUniformSol]
  · rw [deriv_fixedFreeUniformSol]
    field_simp
    ring

/-- Displacement of a fixed–fixed bar under uniform load `q`: `u(x) = q x (L - x) / (2 EA)`. -/
noncomputable def fixedFixedUniformSol (q : ℝ) (x : ℝ) : ℝ :=
  q * x * (b.L - x) / (2 * b.EA)

theorem fixedFixed_uniform (q : ℝ) :
    b.Equilibrium (fun _ => q) (b.fixedFixedUniformSol q) ∧
      b.FixedFixed (b.fixedFixedUniformSol q) := by
  have hEA := b.EA_pos.ne'
  have h1 : deriv (b.fixedFixedUniformSol q) = fun x => q * (b.L - 2 * x) / (2 * b.EA) := by
    ext x
    have h : HasDerivAt (b.fixedFixedUniformSol q)
        ((q * 1 * (b.L - x) + q * x * (0 - 1)) / (2 * b.EA)) x :=
      ((((hasDerivAt_id x).const_mul q).mul ((hasDerivAt_const x b.L).sub
        (hasDerivAt_id x))).div_const (2 * b.EA))
    rw [h.deriv]
    ring
  have h2 : deriv (fun x => q * (b.L - 2 * x) / (2 * b.EA)) = fun _ => -q / b.EA := by
    ext x
    have h : HasDerivAt (fun x => q * (b.L - 2 * x) / (2 * b.EA))
        (q * (0 - 2 * 1) / (2 * b.EA)) x :=
      (((hasDerivAt_const x b.L).sub ((hasDerivAt_id x).const_mul 2)).const_mul q).div_const _
    rw [h.deriv]
    field_simp
    try ring
  refine ⟨fun x _ => ?_, ?_, ?_⟩
  · rw [h1, h2]
    field_simp
    ring
  · simp [fixedFixedUniformSol]
  · simp [fixedFixedUniformSol]

/-- Displacement of a fixed–free bar under the linearly increasing load `f(x) = q₀ x / L`:
`u(x) = q₀ (L² x - x³ / 3) / (2 L EA)`. -/
noncomputable def fixedFreeLinearSol (q₀ : ℝ) (x : ℝ) : ℝ :=
  q₀ * (b.L ^ 2 * x - x ^ 3 / 3) / (2 * b.L * b.EA)

theorem fixedFree_linear (q₀ : ℝ) :
    b.Equilibrium (fun x => q₀ * x / b.L) (b.fixedFreeLinearSol q₀) ∧
      b.FixedFree 0 (b.fixedFreeLinearSol q₀) := by
  have hEA := b.EA_pos.ne'
  have hL := b.L_pos.ne'
  have h1 : deriv (b.fixedFreeLinearSol q₀) = fun x => q₀ * (b.L ^ 2 - x ^ 2) / (2 * b.L * b.EA) := by
    ext x
    have h := (((((hasDerivAt_id x).const_mul (b.L ^ 2)).sub
      ((hasDerivAt_pow 3 x).div_const 3)).const_mul q₀).div_const (2 * b.L * b.EA))
    rw [show deriv (b.fixedFreeLinearSol q₀) x = _ from h.deriv]
    norm_num
    try ring
  have h2 : deriv (fun x => q₀ * (b.L ^ 2 - x ^ 2) / (2 * b.L * b.EA)) =
      fun x => -q₀ * x / (b.L * b.EA) := by
    ext x
    have h : HasDerivAt (fun x => q₀ * (b.L ^ 2 - x ^ 2) / (2 * b.L * b.EA))
        (q₀ * (0 - 2 * x) / (2 * b.L * b.EA)) x := by
      have := (((hasDerivAt_const x (b.L ^ 2)).sub (hasDerivAt_pow 2 x)).const_mul q₀).div_const
        (2 * b.L * b.EA)
      simpa using this
    rw [h.deriv]
    field_simp
    ring
  refine ⟨fun x _ => ?_, ?_, ?_⟩
  · rw [h1, h2]
    field_simp
    ring
  · simp [fixedFreeLinearSol]
  · rw [h1]
    field_simp
    ring

/-! ### Uniqueness -/

/-- A `C²` solution of the homogeneous bar equation is affine on `[0, L]`. -/
theorem affine_of_equilibrium_zero {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (h : b.Equilibrium (fun _ => 0) u) :
    ∀ x ∈ Icc 0 b.L, u x = u 0 + deriv u 0 * x := by
  have h' : ∀ x ∈ Icc 0 b.L, deriv (deriv u) x = 0 := fun x hx => by
    have := h x hx
    rw [add_zero, mul_eq_zero] at this
    exact this.resolve_left b.EA_pos.ne'
  intro x hx
  simpa using eq_affine_of_deriv2_eq_zero hu h' x hx

theorem equilibrium_sub {f u₁ u₂ : ℝ → ℝ} (h₁ : b.Equilibrium f u₁) (h₂ : b.Equilibrium f u₂)
    (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂) :
    b.Equilibrium (fun _ => 0) (u₁ - u₂) := by
  have d₁ : Differentiable ℝ u₁ := hu₁.differentiable (by norm_num)
  have d₂ : Differentiable ℝ u₂ := hu₂.differentiable (by norm_num)
  have dd₁ : Differentiable ℝ (deriv u₁) := (hu₁.deriv' (n := 1)).differentiable (by norm_num)
  have dd₂ : Differentiable ℝ (deriv u₂) := (hu₂.deriv' (n := 1)).differentiable (by norm_num)
  intro x hx
  have e : deriv (u₁ - u₂) = deriv u₁ - deriv u₂ := by
    ext y; exact deriv_sub (d₁ y) (d₂ y)
  rw [e, deriv_sub (dd₁ x) (dd₂ x)]
  have := h₁ x hx
  have := h₂ x hx
  linarith [mul_sub b.EA (deriv (deriv u₁) x) (deriv (deriv u₂) x)]

/-- **Uniqueness** for the fixed–free bar: two `C²` solutions with the same load and end load
coincide on `[0, L]`. -/
theorem fixedFree_unique {f u₁ u₂ : ℝ → ℝ} {P : ℝ} (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (h₁ : b.Equilibrium f u₁) (h₂ : b.Equilibrium f u₂)
    (bc₁ : b.FixedFree P u₁) (bc₂ : b.FixedFree P u₂) :
    ∀ x ∈ Icc 0 b.L, u₁ x = u₂ x := by
  have hd : ContDiff ℝ 2 (u₁ - u₂) := ContDiff.sub hu₁ hu₂
  have hz := b.affine_of_equilibrium_zero hd (b.equilibrium_sub h₁ h₂ hu₁ hu₂)
  have d₁ : Differentiable ℝ u₁ := hu₁.differentiable (by norm_num)
  have d₂ : Differentiable ℝ u₂ := hu₂.differentiable (by norm_num)
  have e : deriv (u₁ - u₂) = deriv u₁ - deriv u₂ := by
    ext y; exact deriv_sub (d₁ y) (d₂ y)
  -- `(u₁ - u₂)'` is constant on `[0, L]` and vanishes at `L`
  have hc : ∀ x ∈ Icc 0 b.L, deriv (u₁ - u₂) x = deriv (u₁ - u₂) 0 := by
    have hdd := b.equilibrium_sub h₁ h₂ hu₁ hu₂
    have hw : ContDiff ℝ 1 (deriv (u₁ - u₂)) := (hd.deriv' (n := 1))
    intro x hx
    have := eq_taylor_of_iterate_deriv_eq_zero 0 (by simpa using hw) (fun y hy => by
      have := hdd y hy
      simp only [add_zero, mul_eq_zero] at this
      simpa using this.resolve_left b.EA_pos.ne') x hx
    simpa using this
  have hL : deriv (u₁ - u₂) b.L = 0 := by
    rw [e, Pi.sub_apply, sub_eq_zero]
    have := bc₁.2.trans bc₂.2.symm
    exact mul_left_cancel₀ b.EA_pos.ne' this
  have h0 : deriv (u₁ - u₂) 0 = 0 := by
    rw [← hc b.L ⟨b.L_pos.le, le_rfl⟩, hL]
  intro x hx
  have := hz x hx
  rw [h0, Pi.sub_apply, Pi.sub_apply, bc₁.1, bc₂.1] at this
  simpa [sub_eq_zero] using this

/-- **Uniqueness** for the fixed–fixed bar. -/
theorem fixedFixed_unique {f u₁ u₂ : ℝ → ℝ} (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (h₁ : b.Equilibrium f u₁) (h₂ : b.Equilibrium f u₂)
    (bc₁ : b.FixedFixed u₁) (bc₂ : b.FixedFixed u₂) :
    ∀ x ∈ Icc 0 b.L, u₁ x = u₂ x := by
  have hd : ContDiff ℝ 2 (u₁ - u₂) := ContDiff.sub hu₁ hu₂
  have hz := b.affine_of_equilibrium_zero hd (b.equilibrium_sub h₁ h₂ hu₁ hu₂)
  have hL := hz b.L ⟨b.L_pos.le, le_rfl⟩
  simp only [Pi.sub_apply, bc₁.1, bc₂.1, bc₁.2, bc₂.2, sub_zero, zero_add] at hL
  have hslope : deriv (u₁ - u₂) 0 = 0 := by
    rcases mul_eq_zero.mp hL.symm with h | h
    · exact h
    · exact absurd h b.L_pos.ne'
  intro x hx
  have := hz x hx
  rw [hslope, Pi.sub_apply, Pi.sub_apply, bc₁.1, bc₂.1] at this
  simpa [sub_eq_zero] using this

end Bar

section Examples

/-- A 2 m steel rod (`EA = 4.2 × 10⁷ N`) hanging under its own weight (`q = 157 N/m`) with a
`1000 N` tip load: the tip displacement is `(P L + q L²/2) / EA`. -/
example :
    let b : Bar := ⟨2, 4.2e7, by norm_num, by norm_num⟩
    b.fixedFreeUniformSol 157 1000 2 = (1000 * 2 + 157 * 2 ^ 2 / 2) / 4.2e7 := by
  simp only [Bar.fixedFreeUniformSol]
  norm_num

end Examples

end ContinuumMechanics.Beams
