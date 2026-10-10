import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Kirchhoff–Love plates on a rectangle

A thin rectangular plate `[0, a] × [0, b]` with flexural rigidity `D = E h³ / (12(1 - ν²))` and
Poisson ratio `ν` carrying a transverse load `q` deflects by `w(x, y)` satisfying the
**Kirchhoff–Love (Sophie Germain–Lagrange) equation**

`D Δ²w = D (w_xxxx + 2 w_xxyy + w_yyyy) = q`,

with bending moments `M_x = -D (w_xx + ν w_yy)`, `M_y = -D (w_yy + ν w_xx)`
([TimoshenkoWoinowsky1959], §§10, 25; [Reddy2007], Ch. 3). Partial derivatives are the
derivatives of the sections `s ↦ w(s, y)` and `t ↦ w(x, t)`.

## Main definitions

* `Plates.Plate`, `Plates.dx`, `Plates.dy`, `Plates.biharm`.
* `Plate.Equation`, `Plate.momentX`, `Plate.momentY`, `Plate.SimplySupported`.

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, §§10, 25.
* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, Ch. 3.
-/

open Set

namespace ContinuumMechanics.Plates

/-- A rectangular **Kirchhoff–Love plate** `[0, a] × [0, b]` with flexural rigidity `D` and
Poisson ratio `ν`. -/
structure Plate where
  /-- Side along `x`. -/
  a : ℝ
  /-- Side along `y`. -/
  b : ℝ
  /-- Flexural rigidity `D = E h³ / (12 (1 - ν²))`. -/
  D : ℝ
  /-- Poisson ratio. -/
  ν : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  D_pos : 0 < D

/-- Partial derivative `∂/∂x`. -/
noncomputable def dx (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun s => w s y) x

/-- Partial derivative `∂/∂y`. -/
noncomputable def dy (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun t => w x t) y

/-- The **biharmonic operator** `Δ²w = w_xxxx + 2 w_xxyy + w_yyyy`. -/
noncomputable def biharm (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y =>
  dx (dx (dx (dx w))) x y + 2 * dx (dx (dy (dy w))) x y + dy (dy (dy (dy w))) x y

namespace Plate

variable (p : Plate)

/-- The **Kirchhoff–Love plate equation** `D Δ²w = q` on the rectangle.
[TimoshenkoWoinowsky1959], §10. -/
def Equation (q w : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 p.a, ∀ y ∈ Icc 0 p.b, p.D * biharm w x y = q x y

/-- Bending moment `M_x = -D (w_xx + ν w_yy)`. -/
noncomputable def momentX (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -p.D * (dx (dx w) x y + p.ν * dy (dy w) x y)

/-- Bending moment `M_y = -D (w_yy + ν w_xx)`. -/
noncomputable def momentY (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -p.D * (dy (dy w) x y + p.ν * dx (dx w) x y)

/-- **Simply supported edges**: `w = 0` and zero normal bending moment on all four edges.
[TimoshenkoWoinowsky1959], §25. -/
def SimplySupported (w : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, w 0 y = 0 ∧ w p.a y = 0 ∧ p.momentX w 0 y = 0 ∧ p.momentX w p.a y = 0) ∧
    ∀ x, w x 0 = 0 ∧ w x p.b = 0 ∧ p.momentY w x 0 = 0 ∧ p.momentY w x p.b = 0

end Plate

/-! ### Separable fields -/

theorem dx_sep {f g : ℝ → ℝ} (hf : Differentiable ℝ f) :
    dx (fun x y => f x * g y) = fun x y => deriv f x * g y := by
  funext x y
  exact ((hf x).hasDerivAt.mul_const (g y)).deriv

theorem dy_sep {f g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    dy (fun x y => f x * g y) = fun x y => f x * deriv g y := by
  funext x y
  exact ((hg y).hasDerivAt.const_mul (f x)).deriv

end ContinuumMechanics.Plates
