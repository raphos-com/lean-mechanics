import ContinuumMechanics.Plates.Navier

/-!
# Mindlin–Reissner plates and the Kirchhoff limit

The **Mindlin–Reissner** (first-order shear deformation) plate has deflection `w` and rotations
`φ = (φ_x, φ_y)`; with bending rigidity `D`, shear stiffness `S = κ G h` and Poisson ratio `ν` the
equilibrium equations are ([Reddy2007], §10.2; [Mindlin1951])

* `S (Δw + ∇·φ) + q = 0`,
* `D (φ_x,xx + (1-ν)/2 φ_x,yy + (1+ν)/2 φ_y,xy) - S (w_x + φ_x) = 0`,
* `D (φ_y,yy + (1-ν)/2 φ_y,xx + (1+ν)/2 φ_x,xy) - S (w_y + φ_y) = 0`,

with moments `M_x = D (φ_x,x + ν φ_y,y)`, `M_y = D (φ_y,y + ν φ_x,x)`.

For a simply supported rectangle under the single-mode load `q₀ sin αx sin βy`, the Navier
solution is `φ = -∇w_K` and `w = W sin αx sin βy` with

`W = W_K (1 + D k² / S)`,  `W_K = q₀ / (D k⁴)`,  `k² = α² + β²`,

where `W_K` is the Kirchhoff–Love amplitude (`Plates/Navier`). Hence `w - w_K = q₀/(S k²) sin sin`,
and the Mindlin deflection converges to the Kirchhoff one as `S → ∞` with rate `O(1/S)`
(the plate analogue of `Beams/Timoshenko/Limit`).

## Main results

* `Plates.MindlinPlate.navier`: the single-mode Navier solution, equations and boundary
  conditions.
* `Plates.MindlinPlate.amplitude_sub`: `W - W_K = q₀ / (S k²)`.
* `Plates.MindlinPlate.tendsto_kirchhoff`: `W → W_K` as `S → ∞`.

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §10.2.
* [Mindlin1951] R. D. Mindlin, *Influence of rotatory inertia and shear on flexural motions of
  isotropic elastic plates*, J. Appl. Mech. 18 (1951).
-/

open Set Real Filter Topology
open scoped Real

namespace ContinuumMechanics.Plates

/-- A rectangular **Mindlin–Reissner plate**: a `Plate` with shear stiffness `S = κ G h`. -/
structure MindlinPlate extends Plate where
  /-- Shear stiffness `κ G h`. -/
  S : ℝ
  S_pos : 0 < S

namespace MindlinPlate

variable (p : MindlinPlate)

/-- The **Mindlin–Reissner equilibrium equations** on the rectangle. [Reddy2007], §10.2. -/
def Equations (q w φx φy : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 p.a, ∀ y ∈ Icc 0 p.b,
    p.S * (dx (dx w) x y + dy (dy w) x y + dx φx x y + dy φy x y) + q x y = 0 ∧
    p.D * (dx (dx φx) x y + (1 - p.ν) / 2 * dy (dy φx) x y + (1 + p.ν) / 2 * dx (dy φy) x y) -
      p.S * (dx w x y + φx x y) = 0 ∧
    p.D * (dy (dy φy) x y + (1 - p.ν) / 2 * dx (dx φy) x y + (1 + p.ν) / 2 * dx (dy φx) x y) -
      p.S * (dy w x y + φy x y) = 0

/-- Moment `M_x = D (φ_x,x + ν φ_y,y)`. -/
noncomputable def momentX (φx φy : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p.D * (dx φx x y + p.ν * dy φy x y)

/-- Moment `M_y = D (φ_y,y + ν φ_x,x)`. -/
noncomputable def momentY (φx φy : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p.D * (dy φy x y + p.ν * dx φx x y)

/-- **Hard simple supports**: `w = 0`, tangential rotation `= 0` and normal moment `= 0` on every
edge. -/
def SimplySupported (w φx φy : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, w 0 y = 0 ∧ w p.a y = 0 ∧ φy 0 y = 0 ∧ φy p.a y = 0 ∧
      p.momentX φx φy 0 y = 0 ∧ p.momentX φx φy p.a y = 0) ∧
    ∀ x, w x 0 = 0 ∧ w x p.b = 0 ∧ φx x 0 = 0 ∧ φx x p.b = 0 ∧
      p.momentY φx φy x 0 = 0 ∧ p.momentY φx φy x p.b = 0

/-- The Kirchhoff amplitude `W_K = q₀ / (D k⁴)`. -/
noncomputable def ampK (q₀ α β : ℝ) : ℝ := q₀ / (p.D * (α ^ 2 + β ^ 2) ^ 2)

/-- The Mindlin amplitude `W = W_K (1 + D k² / S)`. -/
noncomputable def ampM (q₀ α β : ℝ) : ℝ :=
  p.ampK q₀ α β * (1 + p.D * (α ^ 2 + β ^ 2) / p.S)

/-- The rotation mode `X cos αx sin βy`. -/
noncomputable def modeCS (X α β : ℝ) (x y : ℝ) : ℝ := X * cos (α * x) * (1 * sin (β * y))

/-- The rotation mode `Y sin αx cos βy`. -/
noncomputable def modeSC (Y α β : ℝ) (x y : ℝ) : ℝ := Y * sin (α * x) * (1 * cos (β * y))

/-- **Navier solution of the Mindlin plate**: `w = W sin αx sin βy`, `φ = -∇w_K`, with
`α = mπ/a`, `β = nπ/b`. [Reddy2007], §10.2. -/
theorem navier (m n : ℕ) (hm : 0 < m) (q₀ : ℝ) :
    let α := m * π / p.a
    let β := n * π / p.b
    p.Equations (mode q₀ α β) (mode (p.ampM q₀ α β) α β)
        (modeCS (-α * p.ampK q₀ α β) α β) (modeSC (-β * p.ampK q₀ α β) α β) ∧
      p.SimplySupported (mode (p.ampM q₀ α β) α β)
        (modeCS (-α * p.ampK q₀ α β) α β) (modeSC (-β * p.ampK q₀ α β) α β) := by
  intro α β
  have hα : 0 < α := div_pos (mul_pos (Nat.cast_pos.mpr hm) pi_pos) p.a_pos
  have hk : 0 < α ^ 2 + β ^ 2 := by positivity
  have hD := p.D_pos
  have hS := p.S_pos
  have em : ∀ A : ℝ, mode A α β = fun x y => A * sin (α * x) * (1 * sin (β * y)) := fun _ => rfl
  have ecs : ∀ X : ℝ, modeCS X α β = fun x y => X * cos (α * x) * (1 * sin (β * y)) :=
    fun _ => rfl
  have esc : ∀ Y : ℝ, modeSC Y α β = fun x y => Y * sin (α * x) * (1 * cos (β * y)) :=
    fun _ => rfl
  refine ⟨fun x _ y _ => ⟨?_, ?_, ?_⟩, fun y => ?_, fun x => ?_⟩
  · simp only [em, ecs, esc, dx_sinMul, dx_cosMul, dy_sinMul, dy_cosMul, ampM, ampK]
    field_simp
    ring
  · simp only [em, ecs, esc, dx_sinMul, dx_cosMul, dy_sinMul, dy_cosMul, ampM, ampK]
    field_simp
    ring
  · simp only [em, ecs, esc, dx_sinMul, dx_cosMul, dy_sinMul, dy_cosMul, ampM, ampK]
    field_simp
    ring
  · have sa : sin (α * p.a) = 0 := by
      simp only [α]; rw [div_mul_cancel₀ _ p.a_pos.ne', sin_nat_mul_pi]
    simp only [momentX, em, ecs, esc, dx_cosMul, dy_cosMul, mul_zero, sin_zero, sa]
    simp
  · have sb : sin (β * p.b) = 0 := by
      simp only [β]; rw [div_mul_cancel₀ _ p.b_pos.ne', sin_nat_mul_pi]
    simp only [momentY, em, ecs, esc, dx_cosMul, dy_cosMul, mul_zero, sin_zero, sb]
    simp

/-- The shear correction to the deflection: `W - W_K = q₀ / (S k²)`. -/
theorem amplitude_sub (q₀ α β : ℝ) (hk : α ^ 2 + β ^ 2 ≠ 0) :
    p.ampM q₀ α β - p.ampK q₀ α β = q₀ / (p.S * (α ^ 2 + β ^ 2)) := by
  have hD := p.D_pos.ne'
  have hS := p.S_pos.ne'
  simp only [ampM, ampK]
  field_simp
  ring

/-- **Kirchhoff limit**: as the shear stiffness `S → ∞` (other data fixed), the Mindlin amplitude
converges to the Kirchhoff–Love amplitude, with error `q₀ / (S k²)`. -/
theorem tendsto_kirchhoff (P : Plate) (q₀ α β : ℝ) :
    Tendsto (fun S : ℝ => q₀ / (P.D * (α ^ 2 + β ^ 2) ^ 2) * (1 + P.D * (α ^ 2 + β ^ 2) / S))
      atTop (𝓝 (q₀ / (P.D * (α ^ 2 + β ^ 2) ^ 2))) := by
  have h : Tendsto (fun S : ℝ => P.D * (α ^ 2 + β ^ 2) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add h).const_mul (q₀ / (P.D * (α ^ 2 + β ^ 2) ^ 2))
  simpa using this

end MindlinPlate

end ContinuumMechanics.Plates
