import ClassicalMechanics.Vector
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Lagrange's heavy symmetric top

A rigid body with a fixed point `O` moves in a uniform gravitational field `-M g e₃`. In the
**body frame** (principal axes at `O`) let `ω` be the body angular velocity and `γ = Rᵀ e₃` the
upward vertical seen from the body. For a **symmetric** top, the inertia tensor is
`I = diag(I₁, I₁, I₃)`, and the centre of mass lies on the symmetry axis `χ = e₃` at distance `ℓ`.
The torque of the weight about `O` is `ℓ χ × (-M g γ) = M g ℓ (γ × χ)`, and the
**Euler–Poisson equations** read

`I ω̇ + ω × I ω = M g ℓ (γ × χ)`,   `γ̇ = γ × ω`

([Arnold1989], §30; [Goldstein2002], §5.7; [LandauLifshitz1976], §35). The second one is
Poisson's formula for the space-fixed vector `e₃` seen in the body frame.

* **Conservation laws** along solutions (`HeavyTop`):
  the energy `E = ½ ω · I ω + M g ℓ γ · χ` (`HeavyTop.energy_const`), the vertical angular
  momentum `L · γ = (I ω) · γ` (`HeavyTop.vertMom_const`), the geometric integral `|γ|²`
  (`HeavyTop.normSq_γ_const`), and, **Lagrange's case**, the spin momentum `I₃ ω₃`
  (`HeavyTop.spinMom_const`) since `I₁ = I₂` and the torque is orthogonal to `χ`; hence the spin
  `ω₃` itself when `I₃ ≠ 0` (`HeavyTop.spin_const`). The reduced energy
  `E' = E - ½ I₃ ω₃²` is conserved too (`HeavyTop.reducedEnergy_const`).
* **Reduction to one degree of freedom** (`HeavyTop.nutation_sq`): with `u = γ₃ = cos θ`
  (`θ` the nutation angle), `a = I₃ ω₃`, `b = L · γ`, and `|γ| = 1`,

  `u̇² = f(u) = (2E' - 2 M g ℓ u)(1 - u²) / I₁ - (b - a u)² / I₁²`   (`lagrangeCubic`),

  a cubic in `u` whose coefficients are the initial values of the integrals. The proof computes
  `u̇ = (γ × ω)₃` and uses Lagrange's identity
  `(ω₁² + ω₂²)(γ₁² + γ₂²) = (ω₁ γ₁ + ω₂ γ₂)² + (γ₁ ω₂ - γ₂ ω₁)²`
  (`HeavyTop.nutation_sq_mul`, the form without division).
* **Sleeping top** (`HeavyTop.sleeping`, `HeavyTop.sleeping_rigid`): the upright spinning top
  `ω = (0, 0, Ω)`, `γ = e₃` is a solution. If `(I₃ Ω)² > 4 I₁ M g ℓ` (the classical **fast top**
  condition), then `f(u) = (1 - u)² (2 M g ℓ I₁ (1 + u) - a²) / I₁² < 0` for `u < 1`, so *every*
  motion with the same values of the integrals stays upright: `γ₃ ≡ 1`. (This is the
  integral-level statement behind the stability of the sleeping top; we do not prove Lyapunov
  stability under perturbation of the integrals.)

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §30.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §5.7.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §35.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

namespace HeavyTop

/-- The inertia tensor `diag(I₁, I₁, I₃)` of a symmetric top, acting on body vectors. -/
def inertia (I₁ I₃ : ℝ) (v : Vec) : Vec := ![I₁ * v 0, I₁ * v 1, I₃ * v 2]

/-- The symmetry axis `χ = e₃` of the body, carrying the centre of mass. -/
def χ : Vec := ![0, 0, 1]

end HeavyTop

/-- **Lagrange's heavy symmetric top** in the body frame: body angular velocity `ω`, vertical
`γ = Rᵀ e₃`, derivatives `ω'`, `γ'`, obeying the **Euler–Poisson equations**
`I ω̇ + ω × I ω = M g ℓ (γ × χ)` and `γ̇ = γ × ω`, with `I = diag(I₁, I₁, I₃)`, `χ = e₃`. -/
structure HeavyTop where
  I₁ : ℝ
  I₃ : ℝ
  M : ℝ
  g : ℝ
  ℓ : ℝ
  ω : ℝ → Vec
  γ : ℝ → Vec
  ω' : ℝ → Vec
  γ' : ℝ → Vec
  hω : ∀ t, HasDerivAt ω (ω' t) t
  hγ : ∀ t, HasDerivAt γ (γ' t) t
  euler : ∀ t, HeavyTop.inertia I₁ I₃ (ω' t) + ω t ⨯₃ HeavyTop.inertia I₁ I₃ (ω t) =
    (M * g * ℓ) • (γ t ⨯₃ HeavyTop.χ)
  poisson : ∀ t, γ' t = γ t ⨯₃ ω t

namespace HeavyTop

variable (T : HeavyTop)

/-! ### Euler–Poisson equations in components -/

/-- Euler's equations of the heavy symmetric top in components:
`I₁ ω̇₁ = (I₁ - I₃) ω₂ ω₃ + M g ℓ γ₂`, `I₁ ω̇₂ = (I₃ - I₁) ω₃ ω₁ - M g ℓ γ₁`, `I₃ ω̇₃ = 0`. -/
theorem euler_comp (t : ℝ) :
    T.I₁ * T.ω' t 0 = (T.I₁ - T.I₃) * T.ω t 1 * T.ω t 2 + T.M * T.g * T.ℓ * T.γ t 1 ∧
    T.I₁ * T.ω' t 1 = (T.I₃ - T.I₁) * T.ω t 2 * T.ω t 0 - T.M * T.g * T.ℓ * T.γ t 0 ∧
    T.I₃ * T.ω' t 2 = 0 := by
  have h0 := congrFun (T.euler t) 0
  have h1 := congrFun (T.euler t) 1
  have h2 := congrFun (T.euler t) 2
  simp only [inertia, Fin.isValue, cross_apply, Nat.succ_eq_add_one, Nat.reduceAdd, cons_val,
    cons_val_one, cons_val_zero, Pi.add_apply, χ, mul_one, mul_zero, sub_zero, zero_sub, sub_self,
    Pi.smul_apply, smul_eq_mul, mul_neg] at h0 h1 h2
  refine ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2⟩

/-- Poisson's equation `γ̇ = γ × ω` in components. -/
theorem poisson_comp (t : ℝ) :
    T.γ' t 0 = T.γ t 1 * T.ω t 2 - T.γ t 2 * T.ω t 1 ∧
    T.γ' t 1 = T.γ t 2 * T.ω t 0 - T.γ t 0 * T.ω t 2 ∧
    T.γ' t 2 = T.γ t 0 * T.ω t 1 - T.γ t 1 * T.ω t 0 := by
  simp [T.poisson t, cross_apply]

/-- The nutation `u = γ₃ = cos θ` has derivative `u̇ = (γ × ω)₃ = γ₁ ω₂ - γ₂ ω₁`. -/
theorem hasDerivAt_nutation (t : ℝ) :
    HasDerivAt (fun s => T.γ s 2) (T.γ t 0 * T.ω t 1 - T.γ t 1 * T.ω t 0) t := by
  rw [← (T.poisson_comp t).2.2]
  exact hasDerivAt_pi.1 (T.hγ t) 2

/-! ### Conservation laws -/

/-- The total energy `E = ½ ω · I ω + M g ℓ γ · χ`. -/
def energy (t : ℝ) : ℝ :=
  inertia T.I₁ T.I₃ (T.ω t) ⬝ᵥ T.ω t / 2 + T.M * T.g * T.ℓ * (T.γ t ⬝ᵥ χ)

/-- The vertical component of the angular momentum, `L · γ = (I ω) · γ`. -/
def vertMom (t : ℝ) : ℝ := inertia T.I₁ T.I₃ (T.ω t) ⬝ᵥ T.γ t

/-- The spin angular momentum `a = I₃ ω₃` (component of `L` along the symmetry axis). -/
def spinMom (t : ℝ) : ℝ := T.I₃ * T.ω t 2

/-- The reduced energy `E' = E - ½ I₃ ω₃²`. -/
def reducedEnergy (t : ℝ) : ℝ := T.energy t - T.I₃ * T.ω t 2 ^ 2 / 2

/-- The energy in components: `E = ½ (I₁ (ω₁² + ω₂²) + I₃ ω₃²) + M g ℓ γ₃`. -/
theorem energy_eq (t : ℝ) :
    T.energy t = (T.I₁ * (T.ω t 0 ^ 2 + T.ω t 1 ^ 2) + T.I₃ * T.ω t 2 ^ 2) / 2 +
      T.M * T.g * T.ℓ * T.γ t 2 := by
  simp [energy, inertia, χ, dotProduct, Fin.sum_univ_three]
  ring

/-- The vertical angular momentum in components: `L · γ = I₁ (ω₁ γ₁ + ω₂ γ₂) + I₃ ω₃ γ₃`. -/
theorem vertMom_eq (t : ℝ) :
    T.vertMom t = T.I₁ * (T.ω t 0 * T.γ t 0 + T.ω t 1 * T.γ t 1) + T.I₃ * T.ω t 2 * T.γ t 2 := by
  simp [vertMom, inertia, dotProduct, Fin.sum_univ_three]
  ring

/-- `|γ|² = γ₁² + γ₂² + γ₃²`. -/
theorem normSq_γ_eq (t : ℝ) : normSq (T.γ t) = T.γ t 0 ^ 2 + T.γ t 1 ^ 2 + T.γ t 2 ^ 2 := by
  simp [normSq, dotProduct, Fin.sum_univ_three]
  ring

/-- **Conservation of energy** `E = ½ ω · I ω + M g ℓ γ · χ`. -/
theorem energy_const (s t : ℝ) : T.energy s = T.energy t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  obtain ⟨e0, e1, e2⟩ := T.euler_comp t
  obtain ⟨-, -, p2⟩ := T.poisson_comp t
  have hw := hasDerivAt_pi.1 (T.hω t)
  have hg := hasDerivAt_pi.1 (T.hγ t)
  have h := (((((hw 0).pow 2).add ((hw 1).pow 2)).const_mul T.I₁).add
    (((hw 2).pow 2).const_mul T.I₃)).div_const 2 |>.add ((hg 2).const_mul (T.M * T.g * T.ℓ))
  convert h using 1
  · funext s; rw [T.energy_eq]; rfl
  · linear_combination (-(T.ω t 0)) * e0 - T.ω t 1 * e1 - T.ω t 2 * e2 -
      T.M * T.g * T.ℓ * p2

/-- **Conservation of the vertical angular momentum** `L · γ` (the torque `M g ℓ γ × χ` is
horizontal). -/
theorem vertMom_const (s t : ℝ) : T.vertMom s = T.vertMom t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  obtain ⟨e0, e1, e2⟩ := T.euler_comp t
  obtain ⟨p0, p1, p2⟩ := T.poisson_comp t
  have hw := hasDerivAt_pi.1 (T.hω t)
  have hg := hasDerivAt_pi.1 (T.hγ t)
  have h := ((((hw 0).mul (hg 0)).add ((hw 1).mul (hg 1))).const_mul T.I₁).add
    (((hw 2).const_mul T.I₃).mul (hg 2))
  convert h using 1
  · funext s; rw [T.vertMom_eq]; rfl
  · linear_combination (-(T.γ t 0)) * e0 - T.γ t 1 * e1 - T.γ t 2 * e2 -
      T.I₁ * T.ω t 0 * p0 - T.I₁ * T.ω t 1 * p1 - T.I₃ * T.ω t 2 * p2

/-- **Conservation of `|γ|²`** (geometric integral): `γ` is a rotating unit vector. -/
theorem normSq_γ_const (s t : ℝ) : normSq (T.γ s) = normSq (T.γ t) := by
  refine eq_of_hasDerivAt_zero (F := fun t => normSq (T.γ t)) (fun t => ?_) s t
  have h := hasDerivAt_dot (T.hγ t) (T.hγ t)
  convert h using 1
  · rfl
  rw [T.poisson t, dotProduct_comm, ← two_mul]
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **Lagrange's case**: the spin momentum `I₃ ω₃` is conserved, because `I₁ = I₂` and the
torque `M g ℓ γ × χ` is orthogonal to the symmetry axis `χ`. -/
theorem spinMom_const (s t : ℝ) : T.spinMom s = T.spinMom t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := (hasDerivAt_pi.1 (T.hω t) 2).const_mul T.I₃
  rw [(T.euler_comp t).2.2] at h
  exact h

/-- **Lagrange's case**: the spin `ω₃` is conserved (for `I₃ ≠ 0`). -/
theorem spin_const (hI₃ : T.I₃ ≠ 0) (s t : ℝ) : T.ω s 2 = T.ω t 2 :=
  mul_left_cancel₀ hI₃ (T.spinMom_const s t)

/-- The **reduced energy** `E' = E - ½ I₃ ω₃² = ½ I₁ (ω₁² + ω₂²) + M g ℓ γ₃` is conserved. -/
theorem reducedEnergy_const (s t : ℝ) : T.reducedEnergy s = T.reducedEnergy t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  obtain ⟨e0, e1, e2⟩ := T.euler_comp t
  obtain ⟨-, -, p2⟩ := T.poisson_comp t
  have hw := hasDerivAt_pi.1 (T.hω t)
  have hg := hasDerivAt_pi.1 (T.hγ t)
  have h := ((((((hw 0).pow 2).add ((hw 1).pow 2)).const_mul T.I₁).add
    (((hw 2).pow 2).const_mul T.I₃)).div_const 2 |>.add
      ((hg 2).const_mul (T.M * T.g * T.ℓ))).sub (((hw 2).pow 2).const_mul T.I₃ |>.div_const 2)
  convert h using 1
  · funext s; rw [reducedEnergy, T.energy_eq]; rfl
  · linear_combination (-(T.ω t 0)) * e0 - T.ω t 1 * e1 - T.M * T.g * T.ℓ * p2

/-! ### Reduction to the nutation equation -/

/-- **Lagrange's cubic** `f(u) = (2E' - 2 M g ℓ u)(1 - u²) / I₁ - (b - a u)² / I₁²`, where
`k = M g ℓ`, `E'` is the reduced energy, `a = I₃ ω₃` and `b = L · γ`. -/
def lagrangeCubic (I₁ k E' a b u : ℝ) : ℝ :=
  (2 * E' - 2 * k * u) * (1 - u ^ 2) / I₁ - (b - a * u) ^ 2 / I₁ ^ 2

/-- Pointwise algebraic identity behind the reduction: if `|γ|² = 1`, then
`I₁² u̇² = I₁ (2E' - 2 M g ℓ u)(1 - u²) - (b - a u)²` with `u = γ₃`, `u̇ = (γ × ω)₃`. -/
theorem nutation_sq_mul_at (t : ℝ) (hγ : normSq (T.γ t) = 1) :
    T.I₁ ^ 2 * T.γ' t 2 ^ 2 =
      T.I₁ * (2 * T.reducedEnergy t - 2 * (T.M * T.g * T.ℓ) * T.γ t 2) * (1 - T.γ t 2 ^ 2) -
        (T.vertMom t - T.spinMom t * T.γ t 2) ^ 2 := by
  rw [T.normSq_γ_eq] at hγ
  rw [(T.poisson_comp t).2.2, reducedEnergy, T.energy_eq, T.vertMom_eq, spinMom]
  -- Lagrange's identity, with `γ₁² + γ₂² = 1 - γ₃²`
  linear_combination T.I₁ ^ 2 * (T.ω t 0 ^ 2 + T.ω t 1 ^ 2) * hγ

/-- **Reduction to one degree of freedom** (polynomial form): along a solution with
`|γ(0)| = 1`, the nutation `u = γ₃` satisfies
`I₁² u̇² = I₁ (2E' - 2 M g ℓ u)(1 - u²) - (b - a u)²`, with the integrals `E'`, `a = I₃ ω₃`,
`b = L · γ` evaluated at time `0`. -/
theorem nutation_sq_mul (hγ : normSq (T.γ 0) = 1) (t : ℝ) :
    T.I₁ ^ 2 * T.γ' t 2 ^ 2 =
      T.I₁ * (2 * T.reducedEnergy 0 - 2 * (T.M * T.g * T.ℓ) * T.γ t 2) * (1 - T.γ t 2 ^ 2) -
        (T.vertMom 0 - T.spinMom 0 * T.γ t 2) ^ 2 := by
  rw [T.reducedEnergy_const 0 t, T.vertMom_const 0 t, T.spinMom_const 0 t]
  exact T.nutation_sq_mul_at t (by rw [T.normSq_γ_const t 0, hγ])

/-- **Reduction to one degree of freedom** ([Goldstein2002], §5.7; [Arnold1989], §30): along a
solution with `|γ(0)| = 1` and `I₁ ≠ 0`, the nutation `u = γ₃ = cos θ` obeys `u̇² = f(u)`, where
`f` is Lagrange's cubic built from the conserved values `E'`, `a = I₃ ω₃`, `b = L · γ`. -/
theorem nutation_sq (hI₁ : T.I₁ ≠ 0) (hγ : normSq (T.γ 0) = 1) (t : ℝ) :
    T.γ' t 2 ^ 2 = lagrangeCubic T.I₁ (T.M * T.g * T.ℓ) (T.reducedEnergy 0) (T.spinMom 0)
      (T.vertMom 0) (T.γ t 2) := by
  have h := T.nutation_sq_mul hγ t
  rw [lagrangeCubic]
  field_simp
  linear_combination h

/-- On the unit sphere, the nutation `u = γ₃` lies in `[-1, 1]`. -/
theorem nutation_mem (hγ : normSq (T.γ 0) = 1) (t : ℝ) : T.γ t 2 ^ 2 ≤ 1 := by
  have h := T.normSq_γ_const t 0
  rw [hγ, T.normSq_γ_eq] at h
  nlinarith [sq_nonneg (T.γ t 0), sq_nonneg (T.γ t 1)]

/-! ### The sleeping top -/

/-- The **sleeping top**: the upright top `γ = e₃` spinning steadily, `ω = (0, 0, Ω)`. -/
def sleeping (I₁ I₃ M g ℓ Ω : ℝ) : HeavyTop where
  I₁ := I₁
  I₃ := I₃
  M := M
  g := g
  ℓ := ℓ
  ω := fun _ => ![0, 0, Ω]
  γ := fun _ => χ
  ω' := fun _ => 0
  γ' := fun _ => 0
  hω := fun _ => hasDerivAt_const _ _
  hγ := fun _ => hasDerivAt_const _ _
  euler := fun _ => by
    ext i; fin_cases i <;> simp [inertia, χ, cross_apply]
  poisson := fun _ => by
    ext i; fin_cases i <;> simp [χ, cross_apply]

/-- For the integrals of the sleeping top (`E' = M g ℓ`, `b = a`), Lagrange's cubic factors as
`I₁² f(u) = (1 - u)² (2 M g ℓ I₁ (1 + u) - a²)`. -/
theorem lagrangeCubic_sleeping (I₁ k a u : ℝ) (hI₁ : I₁ ≠ 0) :
    I₁ ^ 2 * lagrangeCubic I₁ k k a a u = (1 - u) ^ 2 * (2 * k * I₁ * (1 + u) - a ^ 2) := by
  rw [lagrangeCubic]
  field_simp
  ring

/-- **Fast top** ([Goldstein2002], §5.7; [Arnold1989], §30): if a motion has the integrals of
the sleeping top (`|γ| = 1`, `E' = M g ℓ`, `L · γ = I₃ ω₃ = a`) and `a² > 4 I₁ M g ℓ` (with
`I₁ > 0`, `M g ℓ ≥ 0`), then it stays upright: `γ₃(t) = 1` for all `t`. Indeed then
`f(u) < 0` for every `u < 1`, while `u̇² ≥ 0`. -/
theorem sleeping_rigid (hI₁ : 0 < T.I₁) (hk : 0 ≤ T.M * T.g * T.ℓ)
    (hγ : normSq (T.γ 0) = 1) (hE : T.reducedEnergy 0 = T.M * T.g * T.ℓ)
    (hb : T.vertMom 0 = T.spinMom 0)
    (hfast : 4 * T.I₁ * (T.M * T.g * T.ℓ) < T.spinMom 0 ^ 2) (t : ℝ) : T.γ t 2 = 1 := by
  have h := T.nutation_sq_mul hγ t
  rw [hE, hb] at h
  have hu : T.γ t 2 ≤ 1 := by nlinarith [T.nutation_mem hγ t]
  set u := T.γ t 2
  set k := T.M * T.g * T.ℓ
  set a := T.spinMom 0
  have hf : T.I₁ ^ 2 * T.γ' t 2 ^ 2 = (1 - u) ^ 2 * (2 * k * T.I₁ * (1 + u) - a ^ 2) := by
    rw [h]; ring
  by_contra hne
  have h1 : 0 < (1 - u) ^ 2 := by
    have : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  have h2 : 2 * k * T.I₁ * (1 + u) - a ^ 2 < 0 := by
    nlinarith [mul_nonneg hk hI₁.le]
  have h3 : 0 ≤ T.I₁ ^ 2 * T.γ' t 2 ^ 2 := by positivity
  nlinarith [mul_neg_of_pos_of_neg h1 h2]

/-- The sleeping top satisfies the hypotheses of `sleeping_rigid`: its integrals are
`|γ| = 1`, `E' = M g ℓ` and `L · γ = I₃ ω₃`. -/
theorem sleeping_integrals (I₁ I₃ M g ℓ Ω : ℝ) :
    normSq ((sleeping I₁ I₃ M g ℓ Ω).γ 0) = 1 ∧
    (sleeping I₁ I₃ M g ℓ Ω).reducedEnergy 0 = M * g * ℓ ∧
    (sleeping I₁ I₃ M g ℓ Ω).vertMom 0 = (sleeping I₁ I₃ M g ℓ Ω).spinMom 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sleeping, normSq, χ, dotProduct, Fin.sum_univ_three]
  · rw [reducedEnergy, energy_eq]; simp [sleeping, χ]
  · rw [vertMom_eq]; simp [sleeping, spinMom, χ]

end HeavyTop

end ClassicalMechanics
