import ContinuumMechanics.Plates.Navier

/-!
# Orthotropic plates and beam grillages

An **orthotropic Kirchhoff–Love plate** with rigidities `D₁₁, D₂₂, D₁₂, D₆₆` has bending energy
density

`W(κ) = ½ (D₁₁ κ₁₁² + 2 D₁₂ κ₁₁ κ₂₂ + D₂₂ κ₂₂²) + 2 D₆₆ κ₁₂²`

and deflection equation `D₁₁ w_xxxx + 2H w_xxyy + D₂₂ w_yyyy = q` with `H = D₁₂ + 2 D₆₆`
([TimoshenkoWoinowsky1959], §§85–86; [Reddy2007], §5.1).

A **square grillage** of beams with spacing `ℓ`, bending stiffness `EI` and torsional stiffness
`GJ` in both directions, under a uniform curvature `κ`, stores in each `ℓ × ℓ` cell the energy of
one `x`-beam (curvature `κ₁₁`, twist `κ₁₂`) and one `y`-beam (curvature `κ₂₂`, twist `κ₁₂`). Per
unit area this is the orthotropic energy with (`grillage_energy`)

`D₁₁ = D₂₂ = EI/ℓ`, `D₁₂ = 0`, `D₆₆ = GJ/(2ℓ)`, so `2H = 2GJ/ℓ`,

the "gridwork" plate of [TimoshenkoWoinowsky1959], §86. This is the first-order
(Kirchhoff–Love) model of a beam lattice; [LebeeSab2013] show that capturing the thick-plate
(transverse shear) behaviour of such lattices requires the Bending-Gradient theory instead of
Reissner–Mindlin (see `papers/BendingGradient`).

## Main results

* `OrthoPlate.navier`: Navier's single-mode solution
  `w = q₀ / (D₁₁α⁴ + 2Hα²β² + D₂₂β⁴) sin αx sin βy` of the simply supported orthotropic plate.
* `grillage_energy`: the cell energy of the grillage per unit area.
* `Grillage.isIsotropic_iff`: the grillage is an isotropic Kirchhoff–Love plate iff `GJ = EI`
  (it then has Poisson ratio `0`); `Grillage.op_eq_biharm`: the equation is then `(EI/ℓ) Δ²w = q`.
* `Grillage.navier_center`: central deflection of a square grillage plate under the first mode,
  `w(a/2, a/2) = q₀ ℓ a⁴ / (2π⁴ (EI + GJ))`: torsion stiffens the grillage as much as bending.

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, §§85–86.
* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §5.1.
* [LebeeSab2013] A. Lebée, K. Sab, *Homogenization of a space frame as a thick plate: Application
  of the Bending-Gradient theory to a beam lattice*, Computers & Structures 127 (2013).
-/

open Set Real
open scoped Real

noncomputable section

namespace ContinuumMechanics.Plates

/-- A rectangular **orthotropic Kirchhoff–Love plate** `[0, a] × [0, b]`. -/
structure OrthoPlate where
  a : ℝ
  b : ℝ
  D₁₁ : ℝ
  D₂₂ : ℝ
  D₁₂ : ℝ
  D₆₆ : ℝ
  a_pos : 0 < a
  b_pos : 0 < b

namespace OrthoPlate

variable (p : OrthoPlate)

/-- The bending energy density `½ (D₁₁ κ₁₁² + 2 D₁₂ κ₁₁ κ₂₂ + D₂₂ κ₂₂²) + 2 D₆₆ κ₁₂²`. -/
def energy (κ₁₁ κ₂₂ κ₁₂ : ℝ) : ℝ :=
  (p.D₁₁ * κ₁₁ ^ 2 + 2 * p.D₁₂ * κ₁₁ * κ₂₂ + p.D₂₂ * κ₂₂ ^ 2) / 2 + 2 * p.D₆₆ * κ₁₂ ^ 2

/-- `H = D₁₂ + 2 D₆₆`. -/
def H : ℝ := p.D₁₂ + 2 * p.D₆₆

/-- The operator `D₁₁ w_xxxx + 2H w_xxyy + D₂₂ w_yyyy`. -/
noncomputable def op (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p.D₁₁ * dx (dx (dx (dx w))) x y + 2 * p.H * dx (dx (dy (dy w))) x y +
    p.D₂₂ * dy (dy (dy (dy w))) x y

/-- The plate equation `D₁₁ w_xxxx + 2H w_xxyy + D₂₂ w_yyyy = q`. -/
def Equation (q w : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 p.a, ∀ y ∈ Icc 0 p.b, p.op w x y = q x y

/-- Bending moments `M_x = -(D₁₁ w_xx + D₁₂ w_yy)`, `M_y = -(D₁₂ w_xx + D₂₂ w_yy)`. -/
noncomputable def momentX (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(p.D₁₁ * dx (dx w) x y + p.D₁₂ * dy (dy w) x y)

noncomputable def momentY (w : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(p.D₁₂ * dx (dx w) x y + p.D₂₂ * dy (dy w) x y)

/-- Simply supported edges: `w = 0` and zero normal moment on all four edges. -/
def SimplySupported (w : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, w 0 y = 0 ∧ w p.a y = 0 ∧ p.momentX w 0 y = 0 ∧ p.momentX w p.a y = 0) ∧
    ∀ x, w x 0 = 0 ∧ w x p.b = 0 ∧ p.momentY w x 0 = 0 ∧ p.momentY w x p.b = 0

theorem op_mode (A α β x y : ℝ) :
    p.op (mode A α β) x y =
      (p.D₁₁ * α ^ 4 + 2 * p.H * α ^ 2 * β ^ 2 + p.D₂₂ * β ^ 4) * mode A α β x y := by
  have e : mode A α β = fun x y => A * sin (α * x) * (1 * sin (β * y)) := rfl
  simp only [op, e, dx_sinMul, dx_cosMul, dy_sinMul, dy_cosMul]
  ring

/-- **Navier's solution** for the simply supported orthotropic plate under
`q₀ sin(mπx/a) sin(nπy/b)`. [TimoshenkoWoinowsky1959], §87. -/
theorem navier (m n : ℕ) (q₀ : ℝ)
    (hK : p.D₁₁ * (m * π / p.a) ^ 4 + 2 * p.H * (m * π / p.a) ^ 2 * (n * π / p.b) ^ 2 +
      p.D₂₂ * (n * π / p.b) ^ 4 ≠ 0) :
    let α := m * π / p.a
    let β := n * π / p.b
    let K := p.D₁₁ * α ^ 4 + 2 * p.H * α ^ 2 * β ^ 2 + p.D₂₂ * β ^ 4
    p.Equation (mode q₀ α β) (mode (q₀ / K) α β) ∧ p.SimplySupported (mode (q₀ / K) α β) := by
  intro α β K
  have hR : ∀ A y, mode A α β p.a y = 0 := fun A y => by
    rw [mode_apply, show α * p.a = m * π by simp only [α]; field_simp [p.a_pos.ne'],
      sin_nat_mul_pi]; ring
  have hT : ∀ A x, mode A α β x p.b = 0 := fun A x => by
    rw [mode_apply, show β * p.b = n * π by simp only [β]; field_simp [p.b_pos.ne'],
      sin_nat_mul_pi]; ring
  have h0 : ∀ A y, mode A α β 0 y = 0 := fun A y => by simp [mode_apply]
  have h0' : ∀ A x, mode A α β x 0 = 0 := fun A x => by simp [mode_apply]
  refine ⟨fun x _ y _ => ?_, fun y => ?_, fun x => ?_⟩
  · rw [op_mode, mode_apply, mode_apply,
      show p.D₁₁ * α ^ 4 + 2 * p.H * α ^ 2 * β ^ 2 + p.D₂₂ * β ^ 4 = K from rfl]
    have hK' : K ≠ 0 := hK
    field_simp
  · simp only [momentX, dx_dx_mode, dy_dy_mode, h0, hR]
    simp
  · simp only [momentY, dx_dx_mode, dy_dy_mode, h0', hT]
    simp

end OrthoPlate

/-- A square **beam grillage**: beams along `x` and `y` at spacing `ℓ`, with bending stiffness
`EI` and torsional stiffness `GJ`, on the rectangle `[0, a] × [0, b]`. -/
structure Grillage where
  a : ℝ
  b : ℝ
  ℓ : ℝ
  EI : ℝ
  GJ : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  ℓ_pos : 0 < ℓ

namespace Grillage

variable (g : Grillage)

/-- The equivalent orthotropic plate: `D₁₁ = D₂₂ = EI/ℓ`, `D₁₂ = 0`, `D₆₆ = GJ/(2ℓ)`. -/
noncomputable def plate : OrthoPlate where
  a := g.a
  b := g.b
  D₁₁ := g.EI / g.ℓ
  D₂₂ := g.EI / g.ℓ
  D₁₂ := 0
  D₆₆ := g.GJ / (2 * g.ℓ)
  a_pos := g.a_pos
  b_pos := g.b_pos

/-- Energy stored in one `ℓ × ℓ` cell under a uniform curvature `κ`: an `x`-beam bent by `κ₁₁`
and twisted by `κ₁₂`, and a `y`-beam bent by `κ₂₂` and twisted by `κ₁₂`, each of length `ℓ`. -/
def cellEnergy (κ₁₁ κ₂₂ κ₁₂ : ℝ) : ℝ :=
  (g.EI * κ₁₁ ^ 2 + g.GJ * κ₁₂ ^ 2) * g.ℓ / 2 + (g.EI * κ₂₂ ^ 2 + g.GJ * κ₁₂ ^ 2) * g.ℓ / 2

/-- **Homogenized grillage**: the cell energy per unit area is the energy density of the
orthotropic plate `g.plate`. [TimoshenkoWoinowsky1959], §86. -/
theorem grillage_energy (κ₁₁ κ₂₂ κ₁₂ : ℝ) :
    g.cellEnergy κ₁₁ κ₂₂ κ₁₂ / g.ℓ ^ 2 = g.plate.energy κ₁₁ κ₂₂ κ₁₂ := by
  have := g.ℓ_pos.ne'
  simp only [cellEnergy, OrthoPlate.energy, plate]
  field_simp
  ring

theorem plate_H : g.plate.H = g.GJ / g.ℓ := by
  have := g.ℓ_pos.ne'
  simp only [OrthoPlate.H, plate]
  field_simp
  ring

/-- The rigidities of an isotropic Kirchhoff–Love plate with rigidity `D` and Poisson ratio `ν`:
`D₁₁ = D₂₂ = D`, `D₁₂ = νD`, `D₆₆ = (1 - ν)D/2`. -/
def IsIsotropic (p : OrthoPlate) : Prop :=
  ∃ D ν : ℝ, p.D₁₁ = D ∧ p.D₂₂ = D ∧ p.D₁₂ = ν * D ∧ p.D₆₆ = (1 - ν) * D / 2

/-- The grillage behaves as an isotropic plate iff `GJ = EI` (assuming `EI ≠ 0`); its Poisson
ratio is then `0`. -/
theorem isIsotropic_iff (hEI : g.EI ≠ 0) : IsIsotropic g.plate ↔ g.GJ = g.EI := by
  have hℓ := g.ℓ_pos.ne'
  constructor
  · rintro ⟨D, ν, h11, -, h12, h66⟩
    simp only [plate] at h11 h12 h66
    have hD : D ≠ 0 := by rw [← h11]; exact div_ne_zero hEI hℓ
    have hν : ν = 0 := by
      rcases mul_eq_zero.mp h12.symm with h | h
      · exact h
      · exact absurd h hD
    rw [hν, ← h11] at h66
    field_simp at h66
    linarith
  · intro h
    refine ⟨g.EI / g.ℓ, 0, rfl, rfl, by simp [plate], ?_⟩
    simp only [plate, h]
    field_simp
    ring

/-- For `GJ = EI` the grillage equation is the isotropic plate equation `(EI/ℓ) Δ²w = q`. -/
theorem op_eq_biharm (h : g.GJ = g.EI) (w : ℝ → ℝ → ℝ) (x y : ℝ) :
    g.plate.op w x y = g.EI / g.ℓ * biharm w x y := by
  simp only [OrthoPlate.op, plate_H, h, biharm]
  simp only [plate]
  ring

/-- Central deflection of the first-mode Navier solution `sin(πx/a) sin(πy/a)` (the Navier solution
of `OrthoPlate.navier` for a square plate `a = b`): `w(a/2, a/2) = q₀ ℓ a⁴ / (2π⁴ (EI + GJ))`. -/
theorem navier_center (q₀ : ℝ) (hpos : 0 < g.EI + g.GJ) :
    let α := (1 : ℕ) * π / g.a
    let K := g.plate.D₁₁ * α ^ 4 + 2 * g.plate.H * α ^ 2 * α ^ 2 + g.plate.D₂₂ * α ^ 4
    mode (q₀ / K) α α (g.a / 2) (g.a / 2) = q₀ * g.ℓ * g.a ^ 4 / (2 * π ^ 4 * (g.EI + g.GJ)) := by
  intro α K
  have ha := g.a_pos.ne'
  have hℓ := g.ℓ_pos.ne'
  have hs : sin (α * (g.a / 2)) = 1 := by
    rw [show α * (g.a / 2) = π / 2 by simp only [α, Nat.cast_one, one_mul]; field_simp,
      sin_pi_div_two]
  rw [mode_apply, hs]
  simp only [K, plate_H, α, Nat.cast_one, one_mul]
  simp only [plate]
  have : g.EI + g.GJ ≠ 0 := hpos.ne'
  have h2 : g.EI * 2 + g.GJ * 2 ≠ 0 := by linarith
  field_simp
  ring_nf
  linear_combination q₀ * inv_mul_cancel₀ h2

end Grillage

end ContinuumMechanics.Plates

end
