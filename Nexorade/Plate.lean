import ContinuumMechanics.Plates.Navier
import Nexorade.Parametric

/-!
# The degenerate equivalent plate of the nexorade and its Navier solution

The homogenized nexorade only carries **hydrostatic** bending moments `M = M I`
(`Nexorade.Cell.M11_eq_M22`), with complementary energy density `w* = ½ d M²`. Its dual
(strain) energy is the Legendre transform

`w(χ) = sup_M (M tr χ - ½ d M²) = ½ D (tr χ)²`,  `D = 1/d`,

so only the **mean curvature** carries energy: the deviatoric curvatures `diag(χ, -χ)` and the twist
are energy free ([Greco2013], App. 8). With `χ = -∇∇w`, the plate is governed by

`M = -D Δw`,  `ΔM + p = 0`,  hence `D Δ²w = p`,

with simply supported edges `w = 0`, `M = 0`. For the load `p₀ sin(πx/L₁) sin(πy/L₂)` the Navier
solution is ([Greco2013], (5.7)–(5.8))

`w = p₀ / (D (π²/L₁² + π²/L₂²)²) · sin sin`,  `M = p₀ / (π²/L₁² + π²/L₂²) · sin sin`,

and the localization gives the moment in the nexors, `m = (L / cos φ) M`.

## Main results

* `legendre_le`, `legendre_eq`: the strain energy `½ D (tr χ)²`.
* `DegeneratePlate.navier`: the Navier solution, equations and boundary conditions.
* `DegeneratePlate.nexor_moment_center`: the maximal nexor moment at the plate centre.

## References

* [Greco2013] L. Greco, *Nexorade* (homogenization of reciprocal systems), draft 2013, §5, App. 8.
-/

open Real Set
open scoped Real

noncomputable section

namespace ContinuumMechanics.Nexorade

open Plates

/-- **Legendre transform**: `M t - ½ d M² ≤ t² / (2d)` for `d > 0`. -/
theorem legendre_le {d : ℝ} (hd : 0 < d) (M t : ℝ) : M * t - d * M ^ 2 / 2 ≤ t ^ 2 / (2 * d) := by
  have h : t ^ 2 / (2 * d) - (M * t - d * M ^ 2 / 2) = (d * M - t) ^ 2 / (2 * d) := by
    field_simp; ring
  have : 0 ≤ (d * M - t) ^ 2 / (2 * d) := by positivity
  linarith

/-- The supremum is attained at `M = t / d`: the strain energy is `½ D t²` with `D = 1/d`,
`t = tr χ`. Deviatoric curvatures and twist (`tr χ = 0`) carry no energy. -/
theorem legendre_eq {d : ℝ} (hd : 0 < d) (t : ℝ) :
    (t / d) * t - d * (t / d) ^ 2 / 2 = d⁻¹ * t ^ 2 / 2 := by
  field_simp; ring

/-- The **degenerate plate** over `[0, L₁] × [0, L₂]` with stiffness `D` (only `tr χ` carries
energy). -/
structure DegeneratePlate where
  L₁ : ℝ
  L₂ : ℝ
  D : ℝ
  L₁_pos : 0 < L₁
  L₂_pos : 0 < L₂
  D_pos : 0 < D

namespace DegeneratePlate

variable (P : DegeneratePlate)

/-- The hydrostatic moment `M = -D Δw`. -/
def moment (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := -P.D * (dx (dx w) x y + dy (dy w) x y)

/-- Equilibrium `ΔM + p = 0` of a plate with hydrostatic moment `M`. -/
def Equilibrium (p w : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 P.L₁, ∀ y ∈ Icc 0 P.L₂,
    dx (dx (P.moment w)) x y + dy (dy (P.moment w)) x y + p x y = 0

/-- Simply supported edges: `w = 0` and `M = 0`. -/
def SimplySupported (w : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, w 0 y = 0 ∧ w P.L₁ y = 0 ∧ P.moment w 0 y = 0 ∧ P.moment w P.L₁ y = 0) ∧
    ∀ x, w x 0 = 0 ∧ w x P.L₂ = 0 ∧ P.moment w x 0 = 0 ∧ P.moment w x P.L₂ = 0

theorem moment_mode (A α β : ℝ) :
    P.moment (mode A α β) = mode (P.D * (α ^ 2 + β ^ 2) * A) α β := by
  funext x y
  simp only [moment, dx_dx_mode, dy_dy_mode, mode_apply]
  ring

/-- **Navier solution of the degenerate plate** under `p = p₀ sin(πx/L₁) sin(πy/L₂)`:
`w = p₀ / (D k⁴) sin sin`, `M = p₀ / k² sin sin`, `k² = π²/L₁² + π²/L₂²`.
[Greco2013], (5.7)–(5.8). -/
theorem navier (p₀ : ℝ) :
    let α := π / P.L₁
    let β := π / P.L₂
    let w := mode (p₀ / (P.D * (α ^ 2 + β ^ 2) ^ 2)) α β
    P.Equilibrium (mode p₀ α β) w ∧ P.SimplySupported w ∧
      P.moment w = mode (p₀ / (α ^ 2 + β ^ 2)) α β := by
  intro α β w
  have hα : 0 < α := div_pos pi_pos P.L₁_pos
  have hk : 0 < α ^ 2 + β ^ 2 := by positivity
  have hD := P.D_pos
  have hM : P.moment w = mode (p₀ / (α ^ 2 + β ^ 2)) α β := by
    simp only [w, moment_mode]
    congr 1
    field_simp
  have sa : sin (α * P.L₁) = 0 := by
    simp only [α]; rw [div_mul_cancel₀ _ P.L₁_pos.ne', sin_pi]
  have sb : sin (β * P.L₂) = 0 := by
    simp only [β]; rw [div_mul_cancel₀ _ P.L₂_pos.ne', sin_pi]
  refine ⟨fun x _ y _ => ?_, ⟨fun y => ?_, fun x => ?_⟩, hM⟩
  · rw [hM, dx_dx_mode, dy_dy_mode]
    simp only [mode_apply]
    field_simp
    ring
  · simp only [hM, w, mode_apply, sa]; simp
  · simp only [hM, w, mode_apply, sb]; simp

/-- The degenerate plate is the Kirchhoff–Love plate (`Plates.Plate`) with **Poisson ratio
`ν = 1`**: then `M_x = M_y = -D Δw` and the twisting moment `-D(1 - ν) w_xy` vanishes. -/
def toPlate : Plates.Plate := ⟨P.L₁, P.L₂, P.D, 1, P.L₁_pos, P.L₂_pos, P.D_pos⟩

theorem moment_eq_momentX (w : ℝ → ℝ → ℝ) (x y : ℝ) :
    P.moment w x y = P.toPlate.momentX w x y := by
  simp [moment, Plates.Plate.momentX, toPlate]

theorem moment_eq_momentY (w : ℝ → ℝ → ℝ) (x y : ℝ) :
    P.moment w x y = P.toPlate.momentY w x y := by
  simp only [moment, Plates.Plate.momentY, toPlate, one_mul]; ring

/-- The Navier solution of the degenerate plate solves the Kirchhoff–Love problem
`D Δ²w = p` with simply supported edges (`Plates.Plate.navier` with `ν = 1`). -/
theorem navier_kirchhoffLove (p₀ : ℝ) :
    let α := π / P.L₁
    let β := π / P.L₂
    let w := mode (p₀ / (P.D * (α ^ 2 + β ^ 2) ^ 2)) α β
    P.toPlate.Equation (mode p₀ α β) w ∧ P.toPlate.SimplySupported w := by
  have := P.toPlate.navier 1 1 one_pos p₀
  simpa [toPlate] using this

end DegeneratePlate

/-- **End-to-end**: for the plate made of nexorade cells `(L, φ)` under the first-mode load, the
maximal moment in the nexors at the plate centre is `(L / cos φ) · p₀ / (π²/L₁² + π²/L₂²)`
(localization (5.6) applied to the Navier moment (5.7)). -/
theorem nexor_moment_center {L EI GS φ : ℝ} (hL : 0 < L) (hEI : 0 < EI) (hGS : 0 < GS)
    (hφ₀ : 0 < φ) (hφ : φ ≤ π / 4) (P : DegeneratePlate) (p₀ : ℝ) :
    let c := cellOf L EI GS φ hL hEI hGS hφ₀ hφ
    let M := P.moment (mode (p₀ / (P.D * ((π / P.L₁) ^ 2 + (π / P.L₂) ^ 2) ^ 2))
      (π / P.L₁) (π / P.L₂)) (P.L₁ / 2) (P.L₂ / 2)
    M * c.area / (c.a * (c.a + c.b)) * c.a =
      L / cos φ * (p₀ / ((π / P.L₁) ^ 2 + (π / P.L₂) ^ 2)) := by
  intro c M
  have hM : M = p₀ / ((π / P.L₁) ^ 2 + (π / P.L₂) ^ 2) := by
    simp only [M, (P.navier p₀).2.2, mode_apply]
    have h1 : sin (π / P.L₁ * (P.L₁ / 2)) = 1 := by
      rw [show π / P.L₁ * (P.L₁ / 2) = π / 2 by field_simp [P.L₁_pos.ne']]; exact sin_pi_div_two
    have h2 : sin (π / P.L₂ * (P.L₂ / 2)) = 1 := by
      rw [show π / P.L₂ * (P.L₂ / 2) = π / 2 by field_simp [P.L₂_pos.ne']]; exact sin_pi_div_two
    rw [h1, h2]; ring
  rw [moment_cellOf hL hEI hGS hφ₀ hφ M, hM]
  ring

end ContinuumMechanics.Nexorade

end
