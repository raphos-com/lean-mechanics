import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Euler–Bernoulli beams: closed-form solutions

The classical deflection formulas ([TimoshenkoGere1997], Ch. 9, Appendix G), each proved to
satisfy the beam equation and its boundary conditions. Deflections are polynomials
`x ↦ p.eval x`, so derivatives are computed symbolically (`Beams.iteratedDeriv_eval`).

| Case | Deflection `w(x)` | Characteristic value |
|---|---|---|
| simply supported, uniform `q` | `q x (L³ - 2L x² + x³) / 24EI` | `w(L/2) = 5qL⁴/384EI` |
| cantilever, uniform `q` | `q x² (6L² - 4Lx + x²) / 24EI` | `w(L) = qL⁴/8EI` |
| cantilever, tip load `P` | `P x² (3L - x) / 6EI` | `w(L) = PL³/3EI` |
| simply supported, point load `P` at `a` | piecewise cubic | `w(L/2) = PL³/48EI` for `a = L/2` |

Point loads are not smooth: the deflection is a pair of cubics `w₁` on `[0, a]` and `w₂` on
`[a, L]`, each solving the homogeneous equation, glued with `w, w', w''` continuous and a jump
`P` of the shear force `V = -EI w'''` at `a` (`Beams.EBBeam.SSPointLoad`).

## References

* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, Ch. 9, App. G.
-/

open Set Polynomial

namespace ContinuumMechanics.Beams

namespace EBBeam

variable (b : EBBeam)

/-! ### Simply supported beam, uniform load -/

/-- Deflection polynomial of a simply supported beam under uniform load `q`. -/
noncomputable def ssUniformPoly (q : ℝ) : ℝ[X] :=
  C (q / (24 * b.EI)) * (X ^ 4 - C (2 * b.L) * X ^ 3 + C (b.L ^ 3) * X)

/-- Simply supported beam, uniform load `q`: `w = q x (L³ - 2L x² + x³) / (24 EI)`.
[TimoshenkoGere1997], App. G, Case 1. -/
noncomputable def ssUniform (q : ℝ) : ℝ → ℝ := fun x => (b.ssUniformPoly q).eval x

theorem ssUniform_solves (q : ℝ) :
    b.Equation (fun _ => q) (b.ssUniform q) ∧ b.SimplySupported (b.ssUniform q) := by
  have hEI := b.EI_pos.ne'
  refine ⟨fun x _ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold ssUniform ssUniformPoly
  all_goals beam_poly

/-- Midspan deflection `5 q L⁴ / (384 EI)`. [TimoshenkoGere1997], App. G, Case 1. -/
theorem ssUniform_midspan (q : ℝ) : b.ssUniform q (b.L / 2) = 5 * q * b.L ^ 4 / (384 * b.EI) := by
  have hEI := b.EI_pos.ne'
  unfold ssUniform ssUniformPoly
  beam_poly

/-! ### Cantilever, uniform load -/

/-- Deflection polynomial of a cantilever under uniform load `q`. -/
noncomputable def cantileverUniformPoly (q : ℝ) : ℝ[X] :=
  C (q / (24 * b.EI)) * (X ^ 4 - C (4 * b.L) * X ^ 3 + C (6 * b.L ^ 2) * X ^ 2)

/-- Cantilever, uniform load `q`: `w = q x² (6L² - 4Lx + x²) / (24 EI)`.
[TimoshenkoGere1997], App. G, Case 1 (cantilevers). -/
noncomputable def cantileverUniform (q : ℝ) : ℝ → ℝ := fun x => (b.cantileverUniformPoly q).eval x

theorem cantileverUniform_solves (q : ℝ) :
    b.Equation (fun _ => q) (b.cantileverUniform q) ∧ b.Cantilever 0 (b.cantileverUniform q) := by
  have hEI := b.EI_pos.ne'
  refine ⟨fun x _ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold cantileverUniform cantileverUniformPoly
  all_goals beam_poly

/-- Tip deflection `q L⁴ / (8 EI)`. -/
theorem cantileverUniform_tip (q : ℝ) : b.cantileverUniform q b.L = q * b.L ^ 4 / (8 * b.EI) := by
  have hEI := b.EI_pos.ne'
  unfold cantileverUniform cantileverUniformPoly
  beam_poly

/-! ### Cantilever, tip load -/

/-- Deflection polynomial of a cantilever with tip load `P`. -/
noncomputable def cantileverTipPoly (P : ℝ) : ℝ[X] :=
  C (P / (6 * b.EI)) * (C (3 * b.L) * X ^ 2 - X ^ 3)

/-- Cantilever with tip load `P`: `w = P x² (3L - x) / (6 EI)`.
[TimoshenkoGere1997], App. G, Case 4 (cantilevers). -/
noncomputable def cantileverTip (P : ℝ) : ℝ → ℝ := fun x => (b.cantileverTipPoly P).eval x

theorem cantileverTip_solves (P : ℝ) :
    b.Equation (fun _ => 0) (b.cantileverTip P) ∧ b.Cantilever P (b.cantileverTip P) := by
  have hEI := b.EI_pos.ne'
  refine ⟨fun x _ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold cantileverTip cantileverTipPoly
  all_goals beam_poly

/-- Tip deflection `P L³ / (3 EI)`. -/
theorem cantileverTip_tip (P : ℝ) : b.cantileverTip P b.L = P * b.L ^ 3 / (3 * b.EI) := by
  have hEI := b.EI_pos.ne'
  unfold cantileverTip cantileverTipPoly
  beam_poly

/-! ### Simply supported beam, point load -/

/-- A **simply supported beam with a point load** `P` at `a ∈ (0, L)`: the deflection is `w₁` on
`[0, a]` and `w₂` on `[a, L]`; both solve `EI w'''' = 0`, the supports give
`w₁(0) = w₁''(0) = 0 = w₂(L) = w₂''(L)`, the deflection, slope and moment are continuous at `a`,
and the shear force `V = -EI w'''` jumps by `P` there. -/
def SSPointLoad (a P : ℝ) (w₁ w₂ : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc 0 a, iteratedDeriv 4 w₁ x = 0) ∧ (∀ x ∈ Icc a b.L, iteratedDeriv 4 w₂ x = 0) ∧
  w₁ 0 = 0 ∧ iteratedDeriv 2 w₁ 0 = 0 ∧ w₂ b.L = 0 ∧ iteratedDeriv 2 w₂ b.L = 0 ∧
  w₁ a = w₂ a ∧ iteratedDeriv 1 w₁ a = iteratedDeriv 1 w₂ a ∧
  iteratedDeriv 2 w₁ a = iteratedDeriv 2 w₂ a ∧
  b.EI * (iteratedDeriv 3 w₂ a - iteratedDeriv 3 w₁ a) = P

/-- Left piece (`0 ≤ x ≤ a`): `w₁ = P (L - a) x (L² - (L - a)² - x²) / (6 L EI)`. -/
noncomputable def ssPointLeftPoly (a P : ℝ) : ℝ[X] :=
  C (P * (b.L - a) / (6 * b.L * b.EI)) * (C (b.L ^ 2 - (b.L - a) ^ 2) * X - X ^ 3)

/-- Right piece (`a ≤ x ≤ L`): `w₂ = P a (L - x) (L² - a² - (L - x)²) / (6 L EI)`. -/
noncomputable def ssPointRightPoly (a P : ℝ) : ℝ[X] :=
  C (P * a / (6 * b.L * b.EI)) * (C (b.L ^ 2 - a ^ 2) * (C b.L - X) - (C b.L - X) ^ 3)

/-- The classical point-load solution satisfies the point-load problem.
[TimoshenkoGere1997], App. G, Case 5. -/
theorem ssPoint_solves (a P : ℝ) :
    b.SSPointLoad a P (fun x => (b.ssPointLeftPoly a P).eval x)
      (fun x => (b.ssPointRightPoly a P).eval x) := by
  have hEI := b.EI_pos.ne'
  have hL := b.L_pos.ne'
  refine ⟨fun x _ => ?_, fun x _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ssPointLeftPoly, ssPointRightPoly]
  all_goals beam_poly

/-- Central point load: midspan deflection `P L³ / (48 EI)`. [TimoshenkoGere1997], App. G. -/
theorem ssPoint_center (P : ℝ) :
    (b.ssPointLeftPoly (b.L / 2) P).eval (b.L / 2) = P * b.L ^ 3 / (48 * b.EI) := by
  have hEI := b.EI_pos.ne'
  have hL := b.L_pos.ne'
  unfold ssPointLeftPoly
  beam_poly

end EBBeam

section Examples

/-- A steel I-beam (`E = 200 GPa`, `I = 8.0 × 10⁻⁵ m⁴`, so `EI = 1.6 × 10⁷ N m²`), simply
supported over `6 m` with a uniform load of `10 kN/m`: midspan deflection `5qL⁴/384EI ≈ 10.5 mm`. -/
example :
    let b : EBBeam := ⟨6, 1.6e7, by norm_num, by norm_num⟩
    b.ssUniform 1e4 3 = 5 * 1e4 * 6 ^ 4 / (384 * 1.6e7) := by
  intro b
  have := b.ssUniform_midspan 1e4
  norm_num [b] at this ⊢
  linarith

end Examples

end ContinuumMechanics.Beams
