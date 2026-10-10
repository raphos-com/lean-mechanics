import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ContinuumMechanics.Plates.KirchhoffLove

/-!
# Navier solutions for simply supported rectangular plates

For a simply supported plate `[0, a] × [0, b]` under the sinusoidal load
`q(x, y) = q₀ sin(mπx/a) sin(nπy/b)`, the deflection

`w(x, y) = q₀ / (D π⁴ (m²/a² + n²/b²)²) · sin(mπx/a) sin(nπy/b)`

satisfies `D Δ²w = q` and the simply supported boundary conditions (**Navier's solution**,
[TimoshenkoWoinowsky1959], §28). Since `Δ²` is linear, finite double sine series of loads are
handled mode by mode.

## Main results

* `Plates.biharm_mode`: `Δ² (sin αx sin βy) = (α² + β²)² sin αx sin βy`.
* `Plates.Plate.navier`: the single-mode Navier solution.
* `Plates.Plate.navier_center`: central deflection of a square plate under the first mode,
  `w(a/2, a/2) = q₀ a⁴ / (4 π⁴ D)`.

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, §28.
-/

open Set Real
open scoped Real

namespace ContinuumMechanics.Plates

theorem dx_sinMul (c k : ℝ) (g : ℝ → ℝ) :
    dx (fun x y => c * sin (k * x) * g y) = fun x y => c * k * cos (k * x) * g y := by
  funext x y
  have := (((hasDerivAt_id' x).const_mul k).sin.const_mul c).mul_const (g y)
  rw [dx, this.deriv]
  ring

theorem dx_cosMul (c k : ℝ) (g : ℝ → ℝ) :
    dx (fun x y => c * cos (k * x) * g y) = fun x y => -(c * k) * sin (k * x) * g y := by
  funext x y
  have := (((hasDerivAt_id' x).const_mul k).cos.const_mul c).mul_const (g y)
  rw [dx, this.deriv]
  ring

theorem dy_sinMul (f : ℝ → ℝ) (c k : ℝ) :
    dy (fun x y => f x * (c * sin (k * y))) = fun x y => f x * (c * k * cos (k * y)) := by
  funext x y
  have := (((hasDerivAt_id' y).const_mul k).sin.const_mul c).const_mul (f x)
  rw [dy, this.deriv]
  ring

theorem dy_cosMul (f : ℝ → ℝ) (c k : ℝ) :
    dy (fun x y => f x * (c * cos (k * y))) = fun x y => f x * (-(c * k) * sin (k * y)) := by
  funext x y
  have := (((hasDerivAt_id' y).const_mul k).cos.const_mul c).const_mul (f x)
  rw [dy, this.deriv]
  ring

/-- The separable mode `A sin(αx) sin(βy)`. -/
noncomputable def mode (A α β : ℝ) (x y : ℝ) : ℝ := A * sin (α * x) * (1 * sin (β * y))

theorem mode_apply (A α β x y : ℝ) : mode A α β x y = A * sin (α * x) * sin (β * y) := by
  simp [mode]

theorem dx_dx_mode (A α β : ℝ) : dx (dx (mode A α β)) = fun x y => -α ^ 2 * mode A α β x y := by
  have e : mode A α β = fun x y => A * sin (α * x) * (1 * sin (β * y)) := rfl
  rw [e, dx_sinMul, dx_cosMul]
  funext x y; ring

theorem dy_dy_mode (A α β : ℝ) : dy (dy (mode A α β)) = fun x y => -β ^ 2 * mode A α β x y := by
  have e : mode A α β = fun x y => A * sin (α * x) * (1 * sin (β * y)) := rfl
  rw [e, dy_sinMul, dy_cosMul]
  funext x y; ring

/-- `Δ² (A sin αx sin βy) = (α² + β²)² A sin αx sin βy`. -/
theorem biharm_mode (A α β x y : ℝ) :
    biharm (mode A α β) x y = (α ^ 2 + β ^ 2) ^ 2 * mode A α β x y := by
  have e : mode A α β = fun x y => A * sin (α * x) * (1 * sin (β * y)) := rfl
  simp only [biharm, e, dx_sinMul, dx_cosMul, dy_sinMul, dy_cosMul]
  ring

namespace Plate

variable (p : Plate)

theorem mode_zero_left (A α β y : ℝ) : mode A α β 0 y = 0 := by simp [mode_apply]

theorem mode_zero_bottom (A α β x : ℝ) : mode A α β x 0 = 0 := by simp [mode_apply]

theorem mode_nat_right (A : ℝ) (m : ℕ) (β y : ℝ) : mode A (m * π / p.a) β p.a y = 0 := by
  rw [mode_apply, div_mul_cancel₀ _ p.a_pos.ne', sin_nat_mul_pi]; ring

theorem mode_nat_top (A α : ℝ) (n : ℕ) (x : ℝ) : mode A α (n * π / p.b) x p.b = 0 := by
  rw [mode_apply, div_mul_cancel₀ _ p.b_pos.ne', sin_nat_mul_pi]; ring

/-- **Navier's solution**: under `q = q₀ sin(mπx/a) sin(nπy/b)` (`m, n ≥ 1`) the deflection
`w = q₀ / (D (α² + β²)²) sin(αx) sin(βy)`, `α = mπ/a`, `β = nπ/b`, solves the simply supported
plate problem. [TimoshenkoWoinowsky1959], §28. -/
theorem navier (m n : ℕ) (hm : 0 < m) (q₀ : ℝ) :
    let α := m * π / p.a
    let β := n * π / p.b
    p.Equation (mode q₀ α β) (mode (q₀ / (p.D * (α ^ 2 + β ^ 2) ^ 2)) α β) ∧
      p.SimplySupported (mode (q₀ / (p.D * (α ^ 2 + β ^ 2) ^ 2)) α β) := by
  intro α β
  have hα : 0 < α := div_pos (mul_pos (Nat.cast_pos.mpr hm) pi_pos) p.a_pos
  have hD := p.D_pos
  set A := q₀ / (p.D * (α ^ 2 + β ^ 2) ^ 2)
  refine ⟨fun x _ y _ => ?_, fun y => ?_, fun x => ?_⟩
  · rw [biharm_mode, mode_apply, mode_apply]
    simp only [A]
    field_simp
  · have hR : mode A α β p.a y = 0 := p.mode_nat_right A m β y
    simp only [momentX, dx_dx_mode, dy_dy_mode, mode_zero_left, hR]
    simp
  · have hT : mode A α β x p.b = 0 := p.mode_nat_top A α n x
    simp only [momentY, dx_dx_mode, dy_dy_mode, mode_zero_bottom, hT]
    simp

/-- Central deflection of a square plate (`a = b`) under the first mode `q₀ sin(πx/a) sin(πy/a)`:
`w(a/2, a/2) = q₀ a⁴ / (4 π⁴ D)`. [TimoshenkoWoinowsky1959], §28. -/
theorem navier_center (q₀ : ℝ) (hab : p.a = p.b) :
    let α := (1 : ℕ) * π / p.a
    let β := (1 : ℕ) * π / p.b
    mode (q₀ / (p.D * (α ^ 2 + β ^ 2) ^ 2)) α β (p.a / 2) (p.b / 2) =
      q₀ * p.a ^ 4 / (4 * π ^ 4 * p.D) := by
  intro α β
  have ha := p.a_pos.ne'
  have hD := p.D_pos.ne'
  have hs : sin (α * (p.a / 2)) = 1 := by
    rw [show α * (p.a / 2) = π / 2 by simp only [α, Nat.cast_one, one_mul]; field_simp,
      sin_pi_div_two]
  have ht : sin (β * (p.b / 2)) = 1 := by
    rw [show β * (p.b / 2) = π / 2 by
      simp only [β, Nat.cast_one, one_mul]; field_simp [p.b_pos.ne'], sin_pi_div_two]
  rw [mode_apply, hs, ht]
  simp only [α, β, ← hab, Nat.cast_one, one_mul]
  field_simp
  ring

end Plate

end ContinuumMechanics.Plates
