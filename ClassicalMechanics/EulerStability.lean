import ClassicalMechanics.RigidBody
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Stability of steady rotations of a free rigid body (tennis racket theorem)

A torque-free rigid body with principal moments `I₁, I₂, I₃ > 0` (`EulerTop`) rotates steadily
about each principal axis (`EulerTop.steady_principal`). Such a rotation `ω = (Ω, 0, 0)` is
**stable** when `I₁` is the largest or the smallest moment and **unstable** when it is the
intermediate one ([Arnold1989], §29; [LandauLifshitz1976], §37; [Goldstein2002], §5.6).

* **Linearization** (`EulerTop.euler₂_split`, `EulerTop.euler₃_split`, `LinearizedEuler`): writing
  `ω₁ = Ω + δω₁`, Euler's equations for `ω₂, ω₃` are linear up to quadratic terms:
  `I₂ δω̇₂ = (I₃ - I₁) Ω δω₃`, `I₃ δω̇₃ = (I₁ - I₂) Ω δω₂`. Then
  `δω̈₂ = λ δω₂` with `λ = Ω² (I₃ - I₁)(I₁ - I₂) / (I₂ I₃)` (`LinearizedEuler.second_order`).
* **Sign of `λ`** (`rate_neg_iff`, `rate_pos_iff`): `λ < 0` iff `I₁` is the largest or the smallest
  moment, `λ > 0` iff it is the intermediate one.
* **Linear stability** (`LinearizedEuler.weighted_const`): if `λ < 0` the weighted norm
  `|b| δω₂² + |a| δω₃²` is conserved, so perturbations stay bounded.
* **Linear instability** (`growing_solves`, `growing_unbounded`): if `λ > 0`,
  `δω₂ = ε e^{√λ t}`, `δω₃ = (ε √λ / a) e^{√λ t}` solves the linearized system and is unbounded
  for every `ε > 0`.
* **Nonlinear (Lyapunov) stability** (`EulerTop.perp_bound_of_largest`,
  `EulerTop.perp_bound_of_smallest`): from the conservation of `2T` and `|L|²`, the quantity
  `|L|² - 2 I₁ T = I₂ (I₂ - I₁) ω₂² + I₃ (I₃ - I₁) ω₃²` is conserved (`EulerTop.axisInv_const`),
  and when `I₁` is extremal it is definite, giving
  `ω₂(t)² + ω₃(t)² ≤ (max c / min c) (ω₂(0)² + ω₃(0)²)` with `cᵢ = Iᵢ |Iᵢ - I₁|`.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §29.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §37.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §5.6.
-/

noncomputable section

namespace ClassicalMechanics

/-! ### Linearization about a steady rotation -/

namespace EulerTop

variable (T : EulerTop)

/-- Euler's equation for `ω₂` about `ω₁ = Ω`: a linear term plus a quadratic remainder,
`I₂ ω̇₂ = (I₃ - I₁) Ω ω₃ + (I₃ - I₁) (ω₁ - Ω) ω₃`. -/
theorem euler₂_split (Ω t : ℝ) :
    T.I₂ * T.d₂ t = (T.I₃ - T.I₁) * Ω * T.ω₃ t + (T.I₃ - T.I₁) * (T.ω₁ t - Ω) * T.ω₃ t := by
  rw [T.euler₂ t]; ring

/-- Euler's equation for `ω₃` about `ω₁ = Ω`: a linear term plus a quadratic remainder,
`I₃ ω̇₃ = (I₁ - I₂) Ω ω₂ + (I₁ - I₂) (ω₁ - Ω) ω₂`. -/
theorem euler₃_split (Ω t : ℝ) :
    T.I₃ * T.d₃ t = (T.I₁ - T.I₂) * Ω * T.ω₂ t + (T.I₁ - T.I₂) * (T.ω₁ t - Ω) * T.ω₂ t := by
  rw [T.euler₃ t]; ring

/-- Euler's equation for `ω₁` is quadratic in the perturbation: `I₁ ω̇₁ = (I₂ - I₃) ω₂ ω₃`, so
to first order `δω̇₁ = 0`. -/
theorem euler₁_quadratic (t : ℝ) : T.I₁ * T.d₁ t = (T.I₂ - T.I₃) * T.ω₂ t * T.ω₃ t :=
  T.euler₁ t

end EulerTop

/-- The **rate** `λ = Ω² (I₃ - I₁)(I₁ - I₂) / (I₂ I₃)` of the linearized dynamics
`δω̈₂ = λ δω₂` about the steady rotation `(Ω, 0, 0)`. -/
def eulerRate (I₁ I₂ I₃ Ω : ℝ) : ℝ := Ω ^ 2 * (I₃ - I₁) * (I₁ - I₂) / (I₂ * I₃)

/-- The coefficient `a = (I₃ - I₁) Ω / I₂` in `δω̇₂ = a δω₃`. -/
def eulerA (I₁ I₂ I₃ Ω : ℝ) : ℝ := (I₃ - I₁) * Ω / I₂

/-- The coefficient `b = (I₁ - I₂) Ω / I₃` in `δω̇₃ = b δω₂`. -/
def eulerB (I₁ I₂ I₃ Ω : ℝ) : ℝ := (I₁ - I₂) * Ω / I₃

/-- `λ = a b`. -/
theorem eulerRate_eq (I₁ I₂ I₃ Ω : ℝ) :
    eulerRate I₁ I₂ I₃ Ω = eulerA I₁ I₂ I₃ Ω * eulerB I₁ I₂ I₃ Ω := by
  simp only [eulerRate, eulerA, eulerB]
  rw [div_mul_div_comm]
  ring

/-- `λ` has the sign of `(I₃ - I₁)(I₁ - I₂)`. -/
theorem eulerRate_pos_iff_mul {I₁ I₂ I₃ Ω : ℝ} (h₂ : 0 < I₂) (h₃ : 0 < I₃) (hΩ : Ω ≠ 0) :
    0 < eulerRate I₁ I₂ I₃ Ω ↔ 0 < (I₃ - I₁) * (I₁ - I₂) := by
  have hc : 0 < Ω ^ 2 / (I₂ * I₃) := div_pos (by positivity) (mul_pos h₂ h₃)
  have e : eulerRate I₁ I₂ I₃ Ω = Ω ^ 2 / (I₂ * I₃) * ((I₃ - I₁) * (I₁ - I₂)) := by
    simp only [eulerRate]; ring
  rw [e]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

/-- **Stable case**: `λ < 0` iff `I₁` is the largest or the smallest principal moment. -/
theorem rate_neg_iff {I₁ I₂ I₃ Ω : ℝ} (h₂ : 0 < I₂) (h₃ : 0 < I₃) (hΩ : Ω ≠ 0) :
    eulerRate I₁ I₂ I₃ Ω < 0 ↔ (I₂ < I₁ ∧ I₃ < I₁) ∨ (I₁ < I₂ ∧ I₁ < I₃) := by
  have hc : 0 < Ω ^ 2 / (I₂ * I₃) := div_pos (by positivity) (mul_pos h₂ h₃)
  have e : eulerRate I₁ I₂ I₃ Ω = Ω ^ 2 / (I₂ * I₃) * ((I₃ - I₁) * (I₁ - I₂)) := by
    simp only [eulerRate]; ring
  rw [e, mul_neg_iff, mul_neg_iff]
  constructor
  · rintro (⟨-, h | h⟩ | ⟨h, -⟩)
    · exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact absurd hc (not_lt.2 h.le)
  · rintro (h | h)
    · exact Or.inl ⟨hc, Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩⟩
    · exact Or.inl ⟨hc, Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩⟩

/-- **Unstable case**: `λ > 0` iff `I₁` is the intermediate principal moment. -/
theorem rate_pos_iff {I₁ I₂ I₃ Ω : ℝ} (h₂ : 0 < I₂) (h₃ : 0 < I₃) (hΩ : Ω ≠ 0) :
    0 < eulerRate I₁ I₂ I₃ Ω ↔ (I₂ < I₁ ∧ I₁ < I₃) ∨ (I₃ < I₁ ∧ I₁ < I₂) := by
  rw [eulerRate_pos_iff_mul h₂ h₃ hΩ, mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩
  · rintro (h | h)
    · exact Or.inl ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- The **linearized Euler equations** about the steady rotation `(Ω, 0, 0)`:
`I₂ δω̇₂ = (I₃ - I₁) Ω δω₃`, `I₃ δω̇₃ = (I₁ - I₂) Ω δω₂` (and `δω̇₁ = 0`). -/
structure LinearizedEuler where
  I₁ : ℝ
  I₂ : ℝ
  I₃ : ℝ
  Ω : ℝ
  x₂ : ℝ → ℝ
  x₃ : ℝ → ℝ
  I₂_pos : 0 < I₂
  I₃_pos : 0 < I₃
  h₂ : ∀ t, HasDerivAt x₂ ((I₃ - I₁) * Ω / I₂ * x₃ t) t
  h₃ : ∀ t, HasDerivAt x₃ ((I₁ - I₂) * Ω / I₃ * x₂ t) t

namespace LinearizedEuler

variable (P : LinearizedEuler)

/-- The linearized equations in the form `I₂ δω̇₂ = (I₃ - I₁) Ω δω₃`,
`I₃ δω̇₃ = (I₁ - I₂) Ω δω₂`. -/
theorem euler_form (t : ℝ) :
    P.I₂ * deriv P.x₂ t = (P.I₃ - P.I₁) * P.Ω * P.x₃ t ∧
      P.I₃ * deriv P.x₃ t = (P.I₁ - P.I₂) * P.Ω * P.x₂ t := by
  rw [(P.h₂ t).deriv, (P.h₃ t).deriv]
  constructor <;> field_simp [P.I₂_pos.ne', P.I₃_pos.ne']

/-- **Second-order form**: `δω̈₂ = λ δω₂` with `λ = Ω² (I₃ - I₁)(I₁ - I₂) / (I₂ I₃)`. -/
theorem second_order (t : ℝ) :
    HasDerivAt (deriv P.x₂) (eulerRate P.I₁ P.I₂ P.I₃ P.Ω * P.x₂ t) t := by
  have e : deriv P.x₂ = fun s => (P.I₃ - P.I₁) * P.Ω / P.I₂ * P.x₃ s :=
    funext fun s => (P.h₂ s).deriv
  rw [e, eulerRate_eq]
  convert (P.h₃ t).const_mul ((P.I₃ - P.I₁) * P.Ω / P.I₂) using 1
  simp only [eulerA, eulerB]
  ring

/-- **Linear stability**: when `λ < 0`, the weighted norm `|b| δω₂² + |a| δω₃²` is conserved
(`a = (I₃ - I₁) Ω / I₂`, `b = (I₁ - I₂) Ω / I₃`), so perturbations stay bounded. -/
theorem weighted_const (hrate : eulerRate P.I₁ P.I₂ P.I₃ P.Ω < 0) (s t : ℝ) :
    |eulerB P.I₁ P.I₂ P.I₃ P.Ω| * P.x₂ s ^ 2 + |eulerA P.I₁ P.I₂ P.I₃ P.Ω| * P.x₃ s ^ 2 =
      |eulerB P.I₁ P.I₂ P.I₃ P.Ω| * P.x₂ t ^ 2 + |eulerA P.I₁ P.I₂ P.I₃ P.Ω| * P.x₃ t ^ 2 := by
  set a := eulerA P.I₁ P.I₂ P.I₃ P.Ω
  set b := eulerB P.I₁ P.I₂ P.I₃ P.Ω
  -- `b x₂² - a x₃²` is conserved
  have hQ : ∀ s t, b * P.x₂ s ^ 2 - a * P.x₃ s ^ 2 = b * P.x₂ t ^ 2 - a * P.x₃ t ^ 2 := by
    refine eq_of_hasDerivAt_zero (fun t => ?_)
    have h := (((P.h₂ t).pow 2).const_mul b).sub (((P.h₃ t).pow 2).const_mul a)
    convert h using 1
    simp only [a, b, eulerA, eulerB]
    ring
  rw [eulerRate_eq] at hrate
  rcases mul_neg_iff.1 hrate with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha, abs_of_neg hb]
    linarith [hQ s t]
  · rw [abs_of_neg ha, abs_of_pos hb]
    linarith [hQ s t]

end LinearizedEuler

/-- The **growing solution** of the linearized system for `λ > 0`:
`δω₂ = ε e^{√λ t}`, `δω₃ = (ε √λ / a) e^{√λ t}`. -/
def growingX₂ (I₁ I₂ I₃ Ω ε : ℝ) (t : ℝ) : ℝ :=
  ε * Real.exp (Real.sqrt (eulerRate I₁ I₂ I₃ Ω) * t)

/-- The `δω₃` component of the growing solution. -/
def growingX₃ (I₁ I₂ I₃ Ω ε : ℝ) (t : ℝ) : ℝ :=
  ε * Real.sqrt (eulerRate I₁ I₂ I₃ Ω) / eulerA I₁ I₂ I₃ Ω *
    Real.exp (Real.sqrt (eulerRate I₁ I₂ I₃ Ω) * t)

/-- `a ≠ 0` when `λ = a b > 0`. -/
theorem eulerA_ne_zero {I₁ I₂ I₃ Ω : ℝ} (hrate : 0 < eulerRate I₁ I₂ I₃ Ω) :
    eulerA I₁ I₂ I₃ Ω ≠ 0 := by
  intro h
  rw [eulerRate_eq, h, zero_mul] at hrate
  exact lt_irrefl _ hrate

/-- `√λ √λ = a b` when `λ ≥ 0`. -/
theorem sqrt_mul_self_rate {I₁ I₂ I₃ Ω : ℝ} (hrate : 0 < eulerRate I₁ I₂ I₃ Ω) :
    Real.sqrt (eulerRate I₁ I₂ I₃ Ω) * Real.sqrt (eulerRate I₁ I₂ I₃ Ω) =
      eulerA I₁ I₂ I₃ Ω * eulerB I₁ I₂ I₃ Ω := by
  rw [Real.mul_self_sqrt hrate.le, eulerRate_eq]

/-- The algebra behind the exponential solution: with `μ² = a b`, `x₂ = ε E`,
`x₃ = (ε μ / a) E` and `Ė = μ E`, one has `ẋ₂ = a x₃` and `ẋ₃ = b x₂`. -/
theorem growing_aux {a b μ ε E : ℝ} (ha : a ≠ 0) (hs : μ * μ = a * b) :
    a * (ε * μ / a * E) = ε * (E * (μ * 1)) ∧ b * (ε * E) = ε * μ / a * (E * (μ * 1)) := by
  constructor
  · field_simp
  · rw [show ε * μ / a * (E * (μ * 1)) = ε * E * (μ * μ) / a by ring, hs]
    field_simp

/-- **Linear instability**: for `λ > 0` the exponential `growingX₂`, `growingX₃` solves the
linearized Euler equations. -/
def growing {I₁ I₂ I₃ Ω : ℝ} (h₂ : 0 < I₂) (h₃ : 0 < I₃) (hrate : 0 < eulerRate I₁ I₂ I₃ Ω)
    (ε : ℝ) : LinearizedEuler where
  I₁ := I₁
  I₂ := I₂
  I₃ := I₃
  Ω := Ω
  x₂ := growingX₂ I₁ I₂ I₃ Ω ε
  x₃ := growingX₃ I₁ I₂ I₃ Ω ε
  I₂_pos := h₂
  I₃_pos := h₃
  h₂ t := by
    have h := ((hasDerivAt_id t).const_mul (Real.sqrt (eulerRate I₁ I₂ I₃ Ω))).exp.const_mul ε
    convert h using 1
    · rfl
    exact (growing_aux (eulerA_ne_zero hrate) (sqrt_mul_self_rate hrate)).1
  h₃ t := by
    have h := ((hasDerivAt_id t).const_mul (Real.sqrt (eulerRate I₁ I₂ I₃ Ω))).exp.const_mul
      (ε * Real.sqrt (eulerRate I₁ I₂ I₃ Ω) / eulerA I₁ I₂ I₃ Ω)
    convert h using 1
    · rfl
    exact (growing_aux (eulerA_ne_zero hrate) (sqrt_mul_self_rate hrate)).2

/-- The growing solution starts at `δω₂(0) = ε`. -/
theorem growingX₂_zero (I₁ I₂ I₃ Ω ε : ℝ) : growingX₂ I₁ I₂ I₃ Ω ε 0 = ε := by
  simp [growingX₂]

/-- **Instability**: for `λ > 0` and any `ε > 0`, the perturbation `δω₂ = ε e^{√λ t}` is
unbounded, however small `ε` is. -/
theorem growing_unbounded {I₁ I₂ I₃ Ω ε : ℝ} (hrate : 0 < eulerRate I₁ I₂ I₃ Ω) (hε : 0 < ε)
    (M : ℝ) : ∃ t, M < growingX₂ I₁ I₂ I₃ Ω ε t := by
  have hμ : 0 < Real.sqrt (eulerRate I₁ I₂ I₃ Ω) := Real.sqrt_pos.2 hrate
  refine ⟨|M| / ε / Real.sqrt (eulerRate I₁ I₂ I₃ Ω), ?_⟩
  have e : Real.sqrt (eulerRate I₁ I₂ I₃ Ω) * (|M| / ε / Real.sqrt (eulerRate I₁ I₂ I₃ Ω)) =
      |M| / ε := by field_simp
  have h1 := Real.add_one_le_exp (|M| / ε)
  have h2 : ε * (|M| / ε + 1) = |M| + ε := by field_simp
  simp only [growingX₂, e]
  nlinarith [le_abs_self M, mul_le_mul_of_nonneg_left h1 hε.le]

/-! ### Nonlinear stability -/

namespace EulerTop

variable (T : EulerTop)

/-- The invariant `|L|² - 2 I₁ T` adapted to the axis `e₁`. -/
def axisInv (t : ℝ) : ℝ := T.angMomSq t - 2 * T.I₁ * T.energy t

/-- `|L|² - 2 I₁ T = I₂ (I₂ - I₁) ω₂² + I₃ (I₃ - I₁) ω₃²`. -/
theorem axisInv_eq (t : ℝ) :
    T.axisInv t = T.I₂ * (T.I₂ - T.I₁) * T.ω₂ t ^ 2 + T.I₃ * (T.I₃ - T.I₁) * T.ω₃ t ^ 2 := by
  simp only [axisInv, angMomSq, energy]
  ring

/-- `|L|² - 2 I₁ T` is conserved, by conservation of energy and of `|L|²`. -/
theorem axisInv_const (s t : ℝ) : T.axisInv s = T.axisInv t := by
  simp only [axisInv, T.energy_const s t, T.angMomSq_const s t]

/-- If `c₂ x² + c₃ y² = c₂ x₀² + c₃ y₀²` with `c₂, c₃ > 0`, then
`x² + y² ≤ (max c₂ c₃ / min c₂ c₃) (x₀² + y₀²)`. -/
theorem sq_add_sq_le_of_weighted {c₂ c₃ x y x₀ y₀ : ℝ} (h₂ : 0 < c₂) (h₃ : 0 < c₃)
    (h : c₂ * x ^ 2 + c₃ * y ^ 2 = c₂ * x₀ ^ 2 + c₃ * y₀ ^ 2) :
    x ^ 2 + y ^ 2 ≤ max c₂ c₃ / min c₂ c₃ * (x₀ ^ 2 + y₀ ^ 2) := by
  have hm : 0 < min c₂ c₃ := lt_min h₂ h₃
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  have a₂ := min_le_left c₂ c₃; have a₃ := min_le_right c₂ c₃
  have b₂ := le_max_left c₂ c₃; have b₃ := le_max_right c₂ c₃
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg x₀, sq_nonneg y₀,
    mul_le_mul_of_nonneg_right a₂ (sq_nonneg x), mul_le_mul_of_nonneg_right a₃ (sq_nonneg y),
    mul_le_mul_of_nonneg_right b₂ (sq_nonneg x₀), mul_le_mul_of_nonneg_right b₃ (sq_nonneg y₀)]

/-- **Lyapunov stability about the axis of largest moment**: if `I₂ < I₁` and `I₃ < I₁`, then
`ω₂(t)² + ω₃(t)² ≤ C (ω₂(0)² + ω₃(0)²)` with `C = max c / min c`,
`c₂ = I₂ (I₁ - I₂)`, `c₃ = I₃ (I₁ - I₃)`. -/
theorem perp_bound_of_largest (hI₂ : 0 < T.I₂) (hI₃ : 0 < T.I₃) (h₂ : T.I₂ < T.I₁)
    (h₃ : T.I₃ < T.I₁) (t : ℝ) :
    T.ω₂ t ^ 2 + T.ω₃ t ^ 2 ≤
      max (T.I₂ * (T.I₁ - T.I₂)) (T.I₃ * (T.I₁ - T.I₃)) /
          min (T.I₂ * (T.I₁ - T.I₂)) (T.I₃ * (T.I₁ - T.I₃)) *
        (T.ω₂ 0 ^ 2 + T.ω₃ 0 ^ 2) := by
  refine sq_add_sq_le_of_weighted (mul_pos hI₂ (by linarith)) (mul_pos hI₃ (by linarith)) ?_
  have h := T.axisInv_const t 0
  rw [axisInv_eq, axisInv_eq] at h
  linarith

/-- **Lyapunov stability about the axis of smallest moment**: if `I₁ < I₂` and `I₁ < I₃`, then
`ω₂(t)² + ω₃(t)² ≤ C (ω₂(0)² + ω₃(0)²)` with `C = max c / min c`,
`c₂ = I₂ (I₂ - I₁)`, `c₃ = I₃ (I₃ - I₁)`. -/
theorem perp_bound_of_smallest (hI₂ : 0 < T.I₂) (hI₃ : 0 < T.I₃) (h₂ : T.I₁ < T.I₂)
    (h₃ : T.I₁ < T.I₃) (t : ℝ) :
    T.ω₂ t ^ 2 + T.ω₃ t ^ 2 ≤
      max (T.I₂ * (T.I₂ - T.I₁)) (T.I₃ * (T.I₃ - T.I₁)) /
          min (T.I₂ * (T.I₂ - T.I₁)) (T.I₃ * (T.I₃ - T.I₁)) *
        (T.ω₂ 0 ^ 2 + T.ω₃ 0 ^ 2) := by
  refine sq_add_sq_le_of_weighted (mul_pos hI₂ (by linarith)) (mul_pos hI₃ (by linarith)) ?_
  have h := T.axisInv_const t 0
  rw [axisInv_eq, axisInv_eq] at h
  linarith

end EulerTop

end ClassicalMechanics
