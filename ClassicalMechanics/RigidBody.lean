import ClassicalMechanics.Vector
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Field

/-!
# Rigid bodies

A rigid body is a finite set of point masses `mᵢ ≥ 0` at positions `yᵢ` relative to a reference
point. Its **inertia tensor** is

`J ω = Σ mᵢ yᵢ × (ω × yᵢ) = Σ mᵢ (|yᵢ|² ω - (yᵢ · ω) yᵢ)`   (`inertia_eq`)

([Goldstein2002], §§5.3–5.6; [Arnold1989], §§26–29).

* `J` is linear, **symmetric** and **positive semidefinite**: `J ω · η = Σ mᵢ (ω × yᵢ)·(η × yᵢ)`
  (`inertia_dot`, `inertia_symm`, `inertia_nonneg`).
* **Parallel axis theorem** (Huygens–Steiner, `inertia_shift`): if the reference point is the
  centre of mass (`Σ mᵢ yᵢ = 0`), the inertia about the point `-d` is
  `J_d ω = J ω + M d × (ω × d)`.
* For a **rigid velocity field** `vᵢ = V + ω × yᵢ` about the centre of mass, the angular momentum
  is `Σ mᵢ yᵢ × vᵢ = J ω` (`angMom_rigid`) and the kinetic energy splits as
  `T = ½ M |V|² + ½ ω · J ω` (**König's theorem**, `kinetic_rigid`).
* **Euler's equations** of a torque-free body in principal axes,
  `I₁ ω̇₁ = (I₂ - I₃) ω₂ ω₃` (and cyclically), conserve the kinetic energy `½ Σ Iᵢ ωᵢ²` and the
  squared angular momentum `Σ Iᵢ² ωᵢ²` (`EulerTop.energy_const`, `EulerTop.angMomSq_const`);
  rotations about a principal axis are steady (`EulerTop.steady_principal`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§5.3–5.6.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§26–29.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- A rigid body: point masses `m i ≥ 0` at positions `y i` relative to a reference point. -/
structure RigidBody (ι : Type*) [Fintype ι] where
  m : ι → ℝ
  y : ι → Vec
  m_nonneg : ∀ i, 0 ≤ m i

namespace RigidBody

variable {ι : Type*} [Fintype ι] (B : RigidBody ι)

/-- Total mass. -/
def mass : ℝ := ∑ i, B.m i

/-- First moment `Σ mᵢ yᵢ`; it vanishes iff the reference point is the centre of mass. -/
def moment : Vec := ∑ i, B.m i • B.y i

/-- The **inertia tensor** `J ω = Σ mᵢ yᵢ × (ω × yᵢ)`. -/
def inertia (ω : Vec) : Vec := ∑ i, B.m i • (B.y i ⨯₃ (ω ⨯₃ B.y i))

/-- `J ω = Σ mᵢ (|yᵢ|² ω - (yᵢ · ω) yᵢ)`. -/
theorem inertia_eq (ω : Vec) :
    B.inertia ω = ∑ i, B.m i • ((B.y i ⬝ᵥ B.y i) • ω - (B.y i ⬝ᵥ ω) • B.y i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm ω (B.y i)]

theorem inertia_add (ω η : Vec) : B.inertia (ω + η) = B.inertia ω + B.inertia η := by
  simp only [inertia, map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]

theorem inertia_smul (c : ℝ) (ω : Vec) : B.inertia (c • ω) = c • B.inertia ω := by
  simp only [inertia, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_comm c]

/-- `J ω · η = Σ mᵢ (ω × yᵢ) · (η × yᵢ)`. -/
theorem inertia_dot (ω η : Vec) :
    B.inertia ω ⬝ᵥ η = ∑ i, B.m i * ((ω ⨯₃ B.y i) ⬝ᵥ (η ⨯₃ B.y i)) := by
  simp only [inertia, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cross_cross_eq_smul_sub_smul', sub_dotProduct, smul_dotProduct, smul_dotProduct,
    cross_dot_cross, smul_eq_mul, smul_eq_mul, dotProduct_comm (B.y i) η]
  ring

/-- The inertia tensor is **symmetric**. -/
theorem inertia_symm (ω η : Vec) : B.inertia ω ⬝ᵥ η = ω ⬝ᵥ B.inertia η := by
  rw [inertia_dot, dotProduct_comm, inertia_dot]
  exact Finset.sum_congr rfl fun i _ => by rw [dotProduct_comm]

/-- The inertia tensor is **positive semidefinite**. -/
theorem inertia_nonneg (ω : Vec) : 0 ≤ B.inertia ω ⬝ᵥ ω := by
  rw [inertia_dot]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (B.m_nonneg i) (normSq_nonneg _)

/-- The body seen from the point `-d`: positions `yᵢ + d`. -/
def shift (d : Vec) : RigidBody ι := ⟨B.m, fun i => B.y i + d, B.m_nonneg⟩

/-- **Parallel axis theorem** (Huygens–Steiner): about the centre of mass (`Σ mᵢ yᵢ = 0`),
`J_d ω = J ω + M d × (ω × d)`. -/
theorem inertia_shift (hG : B.moment = 0) (d ω : Vec) :
    (B.shift d).inertia ω = B.inertia ω + B.mass • (d ⨯₃ (ω ⨯₃ d)) := by
  have hG' : ∑ i, B.m i • B.y i = 0 := hG
  have e : ∀ i, B.m i • ((B.y i + d) ⨯₃ (ω ⨯₃ (B.y i + d))) =
      B.m i • (B.y i ⨯₃ (ω ⨯₃ B.y i)) + (B.m i • B.y i) ⨯₃ (ω ⨯₃ d) +
        d ⨯₃ (ω ⨯₃ (B.m i • B.y i)) + B.m i • (d ⨯₃ (ω ⨯₃ d)) := fun i => by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_add]
    abel
  simp only [shift, inertia, e, Finset.sum_add_distrib, mass, Finset.sum_smul]
  rw [← map_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum, hG']
  simp

/-- Angular momentum of a rigid velocity field `vᵢ = V + ω × yᵢ` about the centre of mass:
`Σ mᵢ yᵢ × vᵢ = J ω`. -/
theorem angMom_rigid (hG : B.moment = 0) (V ω : Vec) :
    ∑ i, B.m i • (B.y i ⨯₃ (V + ω ⨯₃ B.y i)) = B.inertia ω := by
  have hG' : ∑ i, B.m i • B.y i = 0 := hG
  have e : ∀ i, B.m i • (B.y i ⨯₃ (V + ω ⨯₃ B.y i)) =
      (B.m i • B.y i) ⨯₃ V + B.m i • (B.y i ⨯₃ (ω ⨯₃ B.y i)) := fun i => by
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_add]
  simp only [e, Finset.sum_add_distrib]
  rw [← LinearMap.sum_apply, ← map_sum, hG']
  simp [inertia]

/-- **König's theorem** for a rigid velocity field about the centre of mass:
`Σ ½ mᵢ |V + ω × yᵢ|² = ½ M |V|² + ½ ω · J ω`. -/
theorem kinetic_rigid (hG : B.moment = 0) (V ω : Vec) :
    ∑ i, B.m i / 2 * normSq (V + ω ⨯₃ B.y i) =
      B.mass / 2 * normSq V + (B.inertia ω ⬝ᵥ ω) / 2 := by
  have hG' : ∑ i, B.m i • B.y i = 0 := hG
  -- the cross term `Σ mᵢ V · (ω × yᵢ) = V · (ω × Σ mᵢ yᵢ)` vanishes
  have hc : ∑ i, B.m i * (V ⬝ᵥ ω ⨯₃ B.y i) = 0 := by
    have : ∑ i, B.m i * (V ⬝ᵥ ω ⨯₃ B.y i) = V ⬝ᵥ ω ⨯₃ ∑ i, B.m i • B.y i := by
      simp only [map_sum, map_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    rw [this, hG', map_zero, dotProduct_zero]
  have e : ∀ i, B.m i / 2 * normSq (V + ω ⨯₃ B.y i) =
      B.m i / 2 * normSq V + B.m i * (V ⬝ᵥ ω ⨯₃ B.y i) +
        B.m i * ((ω ⨯₃ B.y i) ⬝ᵥ (ω ⨯₃ B.y i)) / 2 := fun i => by
    simp only [normSq, add_dotProduct, dotProduct_add, dotProduct_comm (ω ⨯₃ B.y i) V]
    ring
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_add_distrib, hc,
    inertia_dot, mass]
  simp only [add_zero, Finset.sum_div, Finset.sum_mul]

end RigidBody

/-- A **torque-free rigid body** in principal axes: angular velocity components `ω₁, ω₂, ω₃`
(body frame) obeying **Euler's equations** `I₁ ω̇₁ = (I₂ - I₃) ω₂ ω₃` and cyclically. -/
structure EulerTop where
  I₁ : ℝ
  I₂ : ℝ
  I₃ : ℝ
  ω₁ : ℝ → ℝ
  ω₂ : ℝ → ℝ
  ω₃ : ℝ → ℝ
  d₁ : ℝ → ℝ
  d₂ : ℝ → ℝ
  d₃ : ℝ → ℝ
  h₁ : ∀ t, HasDerivAt ω₁ (d₁ t) t
  h₂ : ∀ t, HasDerivAt ω₂ (d₂ t) t
  h₃ : ∀ t, HasDerivAt ω₃ (d₃ t) t
  euler₁ : ∀ t, I₁ * d₁ t = (I₂ - I₃) * ω₂ t * ω₃ t
  euler₂ : ∀ t, I₂ * d₂ t = (I₃ - I₁) * ω₃ t * ω₁ t
  euler₃ : ∀ t, I₃ * d₃ t = (I₁ - I₂) * ω₁ t * ω₂ t

namespace EulerTop

variable (T : EulerTop)

/-- Kinetic energy `½ (I₁ ω₁² + I₂ ω₂² + I₃ ω₃²)`. -/
def energy (t : ℝ) : ℝ := (T.I₁ * T.ω₁ t ^ 2 + T.I₂ * T.ω₂ t ^ 2 + T.I₃ * T.ω₃ t ^ 2) / 2

/-- Squared angular momentum `|L|² = I₁² ω₁² + I₂² ω₂² + I₃² ω₃²`. -/
def angMomSq (t : ℝ) : ℝ :=
  T.I₁ ^ 2 * T.ω₁ t ^ 2 + T.I₂ ^ 2 * T.ω₂ t ^ 2 + T.I₃ ^ 2 * T.ω₃ t ^ 2

/-- **Conservation of kinetic energy** for the torque-free body. -/
theorem energy_const (s t : ℝ) : T.energy s = T.energy t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((((T.h₁ t).pow 2).const_mul T.I₁).add (((T.h₂ t).pow 2).const_mul T.I₂)).add
    (((T.h₃ t).pow 2).const_mul T.I₃) |>.div_const 2
  convert h using 1
  · rfl
  have e1 := T.euler₁ t; have e2 := T.euler₂ t; have e3 := T.euler₃ t
  linear_combination (-(T.ω₁ t)) * e1 - T.ω₂ t * e2 - T.ω₃ t * e3

/-- **Conservation of angular momentum** (its length) for the torque-free body. -/
theorem angMomSq_const (s t : ℝ) : T.angMomSq s = T.angMomSq t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((((T.h₁ t).pow 2).const_mul (T.I₁ ^ 2)).add
    (((T.h₂ t).pow 2).const_mul (T.I₂ ^ 2))).add (((T.h₃ t).pow 2).const_mul (T.I₃ ^ 2))
  convert h using 1
  · rfl
  have e1 := T.euler₁ t; have e2 := T.euler₂ t; have e3 := T.euler₃ t
  linear_combination (-2 * T.I₁ * T.ω₁ t) * e1 - 2 * T.I₂ * T.ω₂ t * e2 - 2 * T.I₃ * T.ω₃ t * e3

/-- **Steady rotations**: a rotation about a principal axis (`ω₂ = ω₃ = 0`) has `ω̇ = 0`. -/
theorem steady_principal (hI : T.I₁ ≠ 0 ∧ T.I₂ ≠ 0 ∧ T.I₃ ≠ 0) {t : ℝ} (h2 : T.ω₂ t = 0)
    (h3 : T.ω₃ t = 0) : T.d₁ t = 0 ∧ T.d₂ t = 0 ∧ T.d₃ t = 0 := by
  have e1 := T.euler₁ t; have e2 := T.euler₂ t; have e3 := T.euler₃ t
  simp only [h2, h3, mul_zero, zero_mul] at e1 e2 e3
  exact ⟨(mul_eq_zero.mp e1).resolve_left hI.1, (mul_eq_zero.mp e2).resolve_left hI.2.1,
    (mul_eq_zero.mp e3).resolve_left hI.2.2⟩

end EulerTop

end ClassicalMechanics
