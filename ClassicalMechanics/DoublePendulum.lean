import ClassicalMechanics.Stability

/-!
# The planar double pendulum

Two point masses `m₁, m₂` hang on massless rods of lengths `ℓ₁, ℓ₂` in a uniform gravitational
field `g`; the configuration is given by the angles `q = (θ₁, θ₂)` of the rods from the downward
vertical ([Goldstein2002], §1.6 and §6.4; [LandauLifshitz1976], §5 Problem 1 and §23).

* **Kinematics** (`hasDerivAt_pos₁`, `hasDerivAt_pos₂`, `kinetic_eq_deriv`): the positions are
  `x₁ = ℓ₁ (sin θ₁, -cos θ₁)` and `x₂ = x₁ + ℓ₂ (sin θ₂, -cos θ₂)`; along every trajectory the
  kinetic energy `½ m₁ |ẋ₁|² + ½ m₂ |ẋ₂|²` equals
  `T = ½ (m₁ + m₂) ℓ₁² θ̇₁² + ½ m₂ ℓ₂² θ̇₂² + m₂ ℓ₁ ℓ₂ θ̇₁ θ̇₂ cos (θ₁ - θ₂)`, and
  `T = ½ θ̇ · M(θ) θ̇` with the **mass matrix** `M(θ)` (`kinetic_eq_mass`). The potential is
  `U = -(m₁ + m₂) g ℓ₁ cos θ₁ - m₂ g ℓ₂ cos θ₂`.
* **Lagrangian** (`lagrangian`): `L = T - U` as a `LagrangianN 2`, with its gradients.
* **Euler–Lagrange equations** (`eulerLagrange_iff`):
  `(m₁ + m₂) ℓ₁² θ̈₁ + m₂ ℓ₁ ℓ₂ θ̈₂ cos (θ₁ - θ₂) + m₂ ℓ₁ ℓ₂ θ̇₂² sin (θ₁ - θ₂)
    + (m₁ + m₂) g ℓ₁ sin θ₁ = 0` and
  `m₂ ℓ₂² θ̈₂ + m₂ ℓ₁ ℓ₂ θ̈₁ cos (θ₁ - θ₂) - m₂ ℓ₁ ℓ₂ θ̇₁² sin (θ₁ - θ₂) + m₂ g ℓ₂ sin θ₂ = 0`.
* **Energy** (`energy_const`): `T + U` is conserved, as the Noether energy of `L`.
* **Mass matrix** (`det_massMatrix`, `massMatrix_posDef`, `exists_kinetic_coercive`):
  `det M(θ) = m₂ ℓ₁² ℓ₂² (m₁ + m₂ sin² (θ₁ - θ₂)) > 0`, `M(θ)` is positive definite, and even
  uniformly so: `T ≥ c ‖θ̇‖²` with `c > 0` independent of `θ`.
* **Stable equilibrium** (`gradU_zero`, `hasHessian_zero`, `posDef_hessian_zero`,
  `strictMin_zero`, `lyapunovStable`): the hanging position `0` is an equilibrium with Hessian
  `K = diag((m₁ + m₂) g ℓ₁, m₂ g ℓ₂) > 0`, a strict local minimum of `U`, and it is Lyapunov
  stable for the full nonlinear equations (Lagrange–Dirichlet, with the uniform bound on `T`).
* **Normal modes** (`det_sub_eq_zero_iff`, `isMode_slow`, `isMode_fast`): for equal masses and
  lengths, `det (K - ω² M(0)) = 0` iff `ω² = (g/ℓ)(2 ± √2)`, with mode shapes `(1, ±√2)`
  (`ω² = (g/ℓ)(2 - √2)` for `(1, √2)`, `ω² = (g/ℓ)(2 + √2)` for `(1, -√2)`).
* **Unstable equilibria** (`gradU_eq_zero_iff`, `inverted_equilibria`, `potential_le_top`): the
  equilibria are `sin θ₁ = sin θ₂ = 0`; at `(0, π)`, `(π, 0)`, `(π, π)` the Hessian of `U` is not
  positive semidefinite, and `(π, π)` is the global maximum of `U`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §1.6, §6.4.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §5, §23.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§22–23.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

/-- The parameters of a planar double pendulum: masses, rod lengths and gravity, all
positive. -/
structure DoublePendulum where
  /-- The upper mass. -/
  m₁ : ℝ
  /-- The lower mass. -/
  m₂ : ℝ
  /-- The length of the upper rod. -/
  ℓ₁ : ℝ
  /-- The length of the lower rod. -/
  ℓ₂ : ℝ
  /-- The gravitational acceleration. -/
  g : ℝ
  m₁_pos : 0 < m₁
  m₂_pos : 0 < m₂
  ℓ₁_pos : 0 < ℓ₁
  ℓ₂_pos : 0 < ℓ₂
  g_pos : 0 < g

namespace DoublePendulum

variable (P : DoublePendulum)

/-! ### Kinematics -/

/-- The position `x₁ = ℓ₁ (sin θ₁, -cos θ₁)` of the upper mass. -/
def pos₁ (q : Fin 2 → ℝ) : Fin 2 → ℝ := ![P.ℓ₁ * sin (q 0), -(P.ℓ₁ * cos (q 0))]

/-- The position `x₂ = x₁ + ℓ₂ (sin θ₂, -cos θ₂)` of the lower mass. -/
def pos₂ (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  P.pos₁ q + ![P.ℓ₂ * sin (q 1), -(P.ℓ₂ * cos (q 1))]

/-- The velocity `ẋ₁ = ℓ₁ θ̇₁ (cos θ₁, sin θ₁)` of the upper mass. -/
def vel₁ (q v : Fin 2 → ℝ) : Fin 2 → ℝ := ![P.ℓ₁ * cos (q 0) * v 0, P.ℓ₁ * sin (q 0) * v 0]

/-- The velocity `ẋ₂ = ẋ₁ + ℓ₂ θ̇₂ (cos θ₂, sin θ₂)` of the lower mass. -/
def vel₂ (q v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  P.vel₁ q v + ![P.ℓ₂ * cos (q 1) * v 1, P.ℓ₂ * sin (q 1) * v 1]

/-- The kinetic energy
`T = ½ (m₁ + m₂) ℓ₁² θ̇₁² + ½ m₂ ℓ₂² θ̇₂² + m₂ ℓ₁ ℓ₂ θ̇₁ θ̇₂ cos (θ₁ - θ₂)`. -/
def kinetic (q v : Fin 2 → ℝ) : ℝ :=
  (P.m₁ + P.m₂) * P.ℓ₁ ^ 2 / 2 * v 0 ^ 2 + P.m₂ * P.ℓ₂ ^ 2 / 2 * v 1 ^ 2 +
    P.m₂ * P.ℓ₁ * P.ℓ₂ * v 0 * v 1 * cos (q 0 - q 1)

/-- The potential energy `U = -(m₁ + m₂) g ℓ₁ cos θ₁ - m₂ g ℓ₂ cos θ₂`. -/
def potential (q : Fin 2 → ℝ) : ℝ :=
  -((P.m₁ + P.m₂) * P.g * P.ℓ₁ * cos (q 0)) - P.m₂ * P.g * P.ℓ₂ * cos (q 1)

/-- The potential is the gravitational energy `g (m₁ y₁ + m₂ y₂)` of the two masses. -/
theorem potential_eq (q : Fin 2 → ℝ) :
    P.potential q = P.g * (P.m₁ * P.pos₁ q 1 + P.m₂ * P.pos₂ q 1) := by
  simp [potential, pos₁, pos₂]
  ring

/-- The upper mass moves with velocity `ẋ₁` along a trajectory `θ(t)`. -/
theorem hasDerivAt_pos₁ {θ : ℝ → Fin 2 → ℝ} {ω : Fin 2 → ℝ} {t : ℝ}
    (h : HasDerivAt θ ω t) : HasDerivAt (fun s => P.pos₁ (θ s)) (P.vel₁ (θ t) ω) t := by
  have h0 := hasDerivAt_pi.1 h 0
  rw [hasDerivAt_pi, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · convert h0.sin.const_mul P.ℓ₁ using 1 <;> simp [vel₁, pos₁]
    ring
  · convert (h0.cos.const_mul P.ℓ₁).neg using 1 <;> first | (funext s; simp [pos₁]) |
      (simp [vel₁]; ring)

/-- The lower mass moves with velocity `ẋ₂` along a trajectory `θ(t)`. -/
theorem hasDerivAt_pos₂ {θ : ℝ → Fin 2 → ℝ} {ω : Fin 2 → ℝ} {t : ℝ}
    (h : HasDerivAt θ ω t) : HasDerivAt (fun s => P.pos₂ (θ s)) (P.vel₂ (θ t) ω) t := by
  have h1 := hasDerivAt_pi.1 h 1
  have hb : HasDerivAt (fun s => ![P.ℓ₂ * sin (θ s 1), -(P.ℓ₂ * cos (θ s 1))])
      ![P.ℓ₂ * cos (θ t 1) * ω 1, P.ℓ₂ * sin (θ t 1) * ω 1] t := by
    rw [hasDerivAt_pi, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · convert h1.sin.const_mul P.ℓ₂ using 1 <;> simp
      ring
    · convert (h1.cos.const_mul P.ℓ₂).neg using 1 <;> first | (funext s; simp) |
        (simp; ring)
  exact (P.hasDerivAt_pos₁ h).add hb

/-- `T` is the sum of the kinetic energies of the two masses, in terms of their velocities. -/
theorem kinetic_eq_vel (q v : Fin 2 → ℝ) :
    P.kinetic q v = P.m₁ / 2 * (P.vel₁ q v ⬝ᵥ P.vel₁ q v) +
      P.m₂ / 2 * (P.vel₂ q v ⬝ᵥ P.vel₂ q v) := by
  simp only [kinetic, vel₂, vel₁, dotProduct, Fin.sum_univ_two, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, cos_sub]
  linear_combination (-(P.m₁ + P.m₂) / 2 * P.ℓ₁ ^ 2 * v 0 ^ 2) * sin_sq_add_cos_sq (q 0) +
    (-P.m₂ / 2 * P.ℓ₂ ^ 2 * v 1 ^ 2) * sin_sq_add_cos_sq (q 1)

/-- **Kinetic energy of the double pendulum**: along every trajectory `θ(t)` with angular
velocity `θ̇(t) = ω`, `T(θ, θ̇) = ½ m₁ |ẋ₁|² + ½ m₂ |ẋ₂|²` for the positions `x₁, x₂`. -/
theorem kinetic_eq_deriv {θ : ℝ → Fin 2 → ℝ} {ω : Fin 2 → ℝ} {t : ℝ} (h : HasDerivAt θ ω t) :
    P.kinetic (θ t) ω =
      P.m₁ / 2 * (deriv (fun s => P.pos₁ (θ s)) t ⬝ᵥ deriv (fun s => P.pos₁ (θ s)) t) +
      P.m₂ / 2 * (deriv (fun s => P.pos₂ (θ s)) t ⬝ᵥ deriv (fun s => P.pos₂ (θ s)) t) := by
  rw [(P.hasDerivAt_pos₁ h).deriv, (P.hasDerivAt_pos₂ h).deriv, kinetic_eq_vel]

/-- The **mass matrix**
`M(θ) = [[(m₁ + m₂) ℓ₁², m₂ ℓ₁ ℓ₂ cos (θ₁ - θ₂)], [m₂ ℓ₁ ℓ₂ cos (θ₁ - θ₂), m₂ ℓ₂²]]`. -/
def massMatrix (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(P.m₁ + P.m₂) * P.ℓ₁ ^ 2, P.m₂ * P.ℓ₁ * P.ℓ₂ * cos (q 0 - q 1);
    P.m₂ * P.ℓ₁ * P.ℓ₂ * cos (q 0 - q 1), P.m₂ * P.ℓ₂ ^ 2]

/-- The mass matrix is symmetric. -/
theorem massMatrix_transpose (q : Fin 2 → ℝ) : (P.massMatrix q)ᵀ = P.massMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [massMatrix]

/-- `T = ½ θ̇ · M(θ) θ̇`. -/
theorem kinetic_eq_mass (q v : Fin 2 → ℝ) :
    P.kinetic q v = (v ⬝ᵥ P.massMatrix q *ᵥ v) / 2 := by
  simp [kinetic, massMatrix, dotProduct, Fin.sum_univ_two, mulVec]
  ring

/-- The determinant of the mass matrix:
`det M(θ) = m₂ ℓ₁² ℓ₂² (m₁ + m₂ sin² (θ₁ - θ₂))`. -/
theorem det_massMatrix (q : Fin 2 → ℝ) :
    (P.massMatrix q).det = P.m₂ * P.ℓ₁ ^ 2 * P.ℓ₂ ^ 2 * (P.m₁ + P.m₂ * sin (q 0 - q 1) ^ 2) := by
  rw [massMatrix, Matrix.det_fin_two_of]
  linear_combination (-(P.m₂ ^ 2 * P.ℓ₁ ^ 2 * P.ℓ₂ ^ 2)) * sin_sq_add_cos_sq (q 0 - q 1)

/-- The determinant of the mass matrix is positive. -/
theorem det_massMatrix_pos (q : Fin 2 → ℝ) : 0 < (P.massMatrix q).det := by
  rw [det_massMatrix]
  have := P.m₁_pos; have := P.m₂_pos; have := P.ℓ₁_pos; have := P.ℓ₂_pos
  positivity

/-- **Uniform coercivity of `T`**, explicit form:
`T ≥ (m₁/4) ℓ₁² θ̇₁² + (m₁ m₂ / (2 (m₁ + 2 m₂))) ℓ₂² θ̇₂²`, for every configuration. -/
theorem kinetic_ge (q v : Fin 2 → ℝ) :
    P.m₁ / 4 * P.ℓ₁ ^ 2 * v 0 ^ 2 +
      P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * P.ℓ₂ ^ 2 * v 1 ^ 2 ≤ P.kinetic q v := by
  have hm₁ := P.m₁_pos; have hm₂ := P.m₂_pos
  have hk : 0 < P.m₁ + 2 * P.m₂ := by positivity
  set c := cos (q 0 - q 1)
  set a := P.ℓ₁ * v 0
  set b := P.ℓ₂ * v 1
  have hc : c ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact abs_cos_le_one _
  have hT : P.kinetic q v = ((P.m₁ + P.m₂) * a ^ 2 + 2 * P.m₂ * c * a * b + P.m₂ * b ^ 2) / 2 := by
    simp only [kinetic, a, b, c]; ring
  have key : 0 ≤ ((P.m₁ + 2 * P.m₂) * a + 2 * P.m₂ * c * b) ^ 2 +
      4 * P.m₂ ^ 2 * (1 - c ^ 2) * b ^ 2 := by
    have : 0 ≤ 1 - c ^ 2 := by linarith
    positivity
  have hrhs : P.m₁ / 4 * P.ℓ₁ ^ 2 * v 0 ^ 2 +
      P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * P.ℓ₂ ^ 2 * v 1 ^ 2 =
      P.m₁ / 4 * a ^ 2 + P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * b ^ 2 := by
    simp only [a, b]; ring
  rw [hT, hrhs, ← sub_nonneg]
  have : ((P.m₁ + P.m₂) * a ^ 2 + 2 * P.m₂ * c * a * b + P.m₂ * b ^ 2) / 2 -
      (P.m₁ / 4 * a ^ 2 + P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * b ^ 2) =
      (((P.m₁ + 2 * P.m₂) * a + 2 * P.m₂ * c * b) ^ 2 +
        4 * P.m₂ ^ 2 * (1 - c ^ 2) * b ^ 2) / (4 * (P.m₁ + 2 * P.m₂)) := by
    field_simp
    ring
  rw [this]
  positivity

/-- **Uniform coercivity of `T`**: there is `c > 0` with `c ‖θ̇‖² ≤ T(θ, θ̇)` for all `θ`. -/
theorem exists_kinetic_coercive : ∃ c > 0, ∀ q v : Fin 2 → ℝ, c * ‖v‖ ^ 2 ≤ P.kinetic q v := by
  have hm₁ := P.m₁_pos; have hm₂ := P.m₂_pos; have := P.ℓ₁_pos; have := P.ℓ₂_pos
  set κ := min (P.m₁ / 4 * P.ℓ₁ ^ 2) (P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * P.ℓ₂ ^ 2)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  refine ⟨κ, hκ, fun q v => le_trans ?_ (P.kinetic_ge q v)⟩
  have hv : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
    have hn : ‖v‖ ≤ √(v 0 ^ 2 + v 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      fin_cases i
      · exact Real.abs_le_sqrt (by simp; nlinarith [sq_nonneg (v 1)])
      · exact Real.abs_le_sqrt (by simp; nlinarith [sq_nonneg (v 0)])
    calc ‖v‖ ^ 2 ≤ √(v 0 ^ 2 + v 1 ^ 2) ^ 2 := by gcongr
      _ = _ := sq_sqrt (by positivity)
  have h1 : κ ≤ P.m₁ / 4 * P.ℓ₁ ^ 2 := min_le_left _ _
  have h2 : κ ≤ P.m₁ * P.m₂ / (2 * (P.m₁ + 2 * P.m₂)) * P.ℓ₂ ^ 2 := min_le_right _ _
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The kinetic energy is nonnegative. -/
theorem kinetic_nonneg (q v : Fin 2 → ℝ) : 0 ≤ P.kinetic q v := by
  obtain ⟨c, hc, h⟩ := P.exists_kinetic_coercive
  exact le_trans (by positivity) (h q v)

/-- The **mass matrix is positive definite** for all configurations. -/
theorem massMatrix_posDef (q : Fin 2 → ℝ) : (P.massMatrix q).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial, massMatrix_transpose]
  · obtain ⟨c, hc, h⟩ := P.exists_kinetic_coercive
    have h := h q v
    rw [kinetic_eq_mass] at h
    have : 0 < ‖v‖ := norm_pos_iff.2 hv
    simp only [star_trivial]
    nlinarith [pow_pos this 2]

/-! ### The Lagrangian and the Euler–Lagrange equations -/

/-- `∂L/∂θ`: `(-m₂ ℓ₁ ℓ₂ θ̇₁ θ̇₂ sin (θ₁ - θ₂) - (m₁ + m₂) g ℓ₁ sin θ₁,
m₂ ℓ₁ ℓ₂ θ̇₁ θ̇₂ sin (θ₁ - θ₂) - m₂ g ℓ₂ sin θ₂)`. -/
def Lq (q v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-(P.m₂ * P.ℓ₁ * P.ℓ₂ * v 0 * v 1 * sin (q 0 - q 1)) - (P.m₁ + P.m₂) * P.g * P.ℓ₁ * sin (q 0),
    P.m₂ * P.ℓ₁ * P.ℓ₂ * v 0 * v 1 * sin (q 0 - q 1) - P.m₂ * P.g * P.ℓ₂ * sin (q 1)]

/-- `∂L/∂θ̇`: `((m₁ + m₂) ℓ₁² θ̇₁ + m₂ ℓ₁ ℓ₂ θ̇₂ cos (θ₁ - θ₂),
m₂ ℓ₂² θ̇₂ + m₂ ℓ₁ ℓ₂ θ̇₁ cos (θ₁ - θ₂))`. -/
def Lv (q v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(P.m₁ + P.m₂) * P.ℓ₁ ^ 2 * v 0 + P.m₂ * P.ℓ₁ * P.ℓ₂ * v 1 * cos (q 0 - q 1),
    P.m₂ * P.ℓ₂ ^ 2 * v 1 + P.m₂ * P.ℓ₁ * P.ℓ₂ * v 0 * cos (q 0 - q 1)]

/-- The generalized momenta are `∂L/∂θ̇ = M(θ) θ̇`. -/
theorem Lv_eq (q v : Fin 2 → ℝ) : P.Lv q v = P.massMatrix q *ᵥ v := by
  ext i
  fin_cases i <;> simp [Lv, massMatrix, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The Lagrangian `L = T - U` has gradients `Lq`, `Lv`. -/
theorem hasFDerivAt_L (q v : Fin 2 → ℝ) :
    HasFDerivAt (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => P.kinetic p.1 p.2 - P.potential p.1)
      ((dotCLM (P.Lq q v)).comp (ContinuousLinearMap.fst ℝ _ _) +
        (dotCLM (P.Lv q v)).comp (ContinuousLinearMap.snd ℝ _ _)) (q, v) := by
  have hq : ∀ i : Fin 2, HasFDerivAt (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 i)
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)) (q, v) := fun i =>
    (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)) :
      (Fin 2 → ℝ) × (Fin 2 → ℝ) →L[ℝ] ℝ)).hasFDerivAt
  have hv : ∀ i : Fin 2, HasFDerivAt (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 i)
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)) (q, v) := fun i =>
    (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)) :
      (Fin 2 → ℝ) × (Fin 2 → ℝ) →L[ℝ] ℝ)).hasFDerivAt
  have h := (((((hv 0).mul (hv 0)).const_mul ((P.m₁ + P.m₂) * P.ℓ₁ ^ 2 / 2)).add
    (((hv 1).mul (hv 1)).const_mul (P.m₂ * P.ℓ₂ ^ 2 / 2))).add
    ((((hv 0).mul (hv 1)).mul ((hq 0).sub (hq 1)).cos).const_mul (P.m₂ * P.ℓ₁ * P.ℓ₂))).sub
    (((((hq 0).cos.const_mul ((P.m₁ + P.m₂) * P.g * P.ℓ₁)).neg).sub
      ((hq 1).cos.const_mul (P.m₂ * P.g * P.ℓ₂))))
  convert h using 1
  · funext p
    simp only [kinetic, potential, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  · refine ContinuousLinearMap.ext fun w => ?_
    simp [Lq, Lv, dotProduct, Fin.sum_univ_two]
    ring

/-- The **Lagrangian of the double pendulum** `L = T - U` on `ℝ² × ℝ²`. -/
def lagrangian : LagrangianN 2 where
  L q v := P.kinetic q v - P.potential q
  Lq := P.Lq
  Lv := P.Lv
  hasFDerivAt := P.hasFDerivAt_L

/-- The **Euler–Lagrange equations of the double pendulum**:
`(m₁ + m₂) ℓ₁² θ̈₁ + m₂ ℓ₁ ℓ₂ θ̈₂ cos (θ₁ - θ₂) + m₂ ℓ₁ ℓ₂ θ̇₂² sin (θ₁ - θ₂)
  + (m₁ + m₂) g ℓ₁ sin θ₁ = 0`,
`m₂ ℓ₂² θ̈₂ + m₂ ℓ₁ ℓ₂ θ̈₁ cos (θ₁ - θ₂) - m₂ ℓ₁ ℓ₂ θ̇₁² sin (θ₁ - θ₂) + m₂ g ℓ₂ sin θ₂ = 0`. -/
theorem eulerLagrange_iff (γ : MotionN 2) :
    P.lagrangian.EulerLagrange γ ↔ ∀ t,
      (P.m₁ + P.m₂) * P.ℓ₁ ^ 2 * γ.a t 0 +
          P.m₂ * P.ℓ₁ * P.ℓ₂ * γ.a t 1 * cos (γ.q t 0 - γ.q t 1) +
          P.m₂ * P.ℓ₁ * P.ℓ₂ * γ.v t 1 ^ 2 * sin (γ.q t 0 - γ.q t 1) +
          (P.m₁ + P.m₂) * P.g * P.ℓ₁ * sin (γ.q t 0) = 0 ∧
      P.m₂ * P.ℓ₂ ^ 2 * γ.a t 1 + P.m₂ * P.ℓ₁ * P.ℓ₂ * γ.a t 0 * cos (γ.q t 0 - γ.q t 1) -
          P.m₂ * P.ℓ₁ * P.ℓ₂ * γ.v t 0 ^ 2 * sin (γ.q t 0 - γ.q t 1) +
          P.m₂ * P.g * P.ℓ₂ * sin (γ.q t 1) = 0 := by
  -- the time derivative of the momenta `∂L/∂θ̇`
  have hD : ∀ t, HasDerivAt (fun s => P.Lv (γ.q s) (γ.v s))
      ![(P.m₁ + P.m₂) * P.ℓ₁ ^ 2 * γ.a t 0 + P.m₂ * P.ℓ₁ * P.ℓ₂ *
          (γ.a t 1 * cos (γ.q t 0 - γ.q t 1) -
            γ.v t 1 * sin (γ.q t 0 - γ.q t 1) * (γ.v t 0 - γ.v t 1)),
        P.m₂ * P.ℓ₂ ^ 2 * γ.a t 1 + P.m₂ * P.ℓ₁ * P.ℓ₂ *
          (γ.a t 0 * cos (γ.q t 0 - γ.q t 1) -
            γ.v t 0 * sin (γ.q t 0 - γ.q t 1) * (γ.v t 0 - γ.v t 1))] t := by
    intro t
    have hq0 := hasDerivAt_pi.1 (γ.hasDerivAt_q t) 0
    have hq1 := hasDerivAt_pi.1 (γ.hasDerivAt_q t) 1
    have hv0 := hasDerivAt_pi.1 (γ.hasDerivAt_v t) 0
    have hv1 := hasDerivAt_pi.1 (γ.hasDerivAt_v t) 1
    have hc := (hq0.sub hq1).cos
    rw [hasDerivAt_pi, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · convert (hv0.const_mul ((P.m₁ + P.m₂) * P.ℓ₁ ^ 2)).add
        ((hv1.mul hc).const_mul (P.m₂ * P.ℓ₁ * P.ℓ₂)) using 1
      · funext s; simp [Lv]; ring
      · simp only [Matrix.cons_val_zero, Pi.sub_apply]; ring
    · convert (hv1.const_mul (P.m₂ * P.ℓ₂ ^ 2)).add
        ((hv0.mul hc).const_mul (P.m₂ * P.ℓ₁ * P.ℓ₂)) using 1
      · funext s; simp [Lv]; ring
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply]; ring
  constructor
  · intro h t
    have he := (hD t).unique (h t)
    have e0 := congrFun he 0
    have e1 := congrFun he 1
    simp only [lagrangian, Lq, Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    exact ⟨by linear_combination e0, by linear_combination e1⟩
  · intro h t
    obtain ⟨h0, h1⟩ := h t
    refine (hD t).congr_deriv ?_
    ext i
    fin_cases i
    · simp only [lagrangian, Lq, Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination h0
    · simp only [lagrangian, Lq, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination h1

/-- The Noether energy `θ̇ · ∂L/∂θ̇ - L` of the double pendulum is `T + U`. -/
theorem energy_eq (γ : MotionN 2) (t : ℝ) :
    P.lagrangian.energy γ t = P.kinetic (γ.q t) (γ.v t) + P.potential (γ.q t) := by
  simp only [LagrangianN.energy, lagrangian, Lv, kinetic, dotProduct, Fin.sum_univ_two]
  simp
  ring

/-- **Conservation of energy**: `T + U` is constant along every solution of the Euler–Lagrange
equations. -/
theorem energy_const {γ : MotionN 2} (h : P.lagrangian.EulerLagrange γ) (s t : ℝ) :
    P.kinetic (γ.q s) (γ.v s) + P.potential (γ.q s) =
      P.kinetic (γ.q t) (γ.v t) + P.potential (γ.q t) := by
  rw [← energy_eq, ← energy_eq]
  exact P.lagrangian.energy_const γ h s t

/-! ### Equilibria and their linearization -/

/-- The gradient `∇U = ((m₁ + m₂) g ℓ₁ sin θ₁, m₂ g ℓ₂ sin θ₂)` of the potential. -/
def gradU (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(P.m₁ + P.m₂) * P.g * P.ℓ₁ * sin (q 0), P.m₂ * P.g * P.ℓ₂ * sin (q 1)]

/-- The coordinate functions `q ↦ q i` on `ℝ²` are differentiable. -/
theorem hasFDerivAt_coord (i : Fin 2) (q : Fin 2 → ℝ) :
    HasFDerivAt (fun q : Fin 2 → ℝ => q i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) q :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).hasFDerivAt

/-- `∇U` is the gradient of `U`. -/
theorem hasFDerivAt_potential (q : Fin 2 → ℝ) :
    HasFDerivAt P.potential (dotCLM (P.gradU q)) q := by
  have h := (((hasFDerivAt_coord 0 q).cos.const_mul ((P.m₁ + P.m₂) * P.g * P.ℓ₁)).neg).sub
    ((hasFDerivAt_coord 1 q).cos.const_mul (P.m₂ * P.g * P.ℓ₂))
  convert h using 1
  · funext x
    simp only [potential, Pi.sub_apply, Pi.neg_apply]
  · refine ContinuousLinearMap.ext fun w => ?_
    simp [gradU, dotProduct, Fin.sum_univ_two]
    ring

/-- The Hessian `diag((m₁ + m₂) g ℓ₁ cos θ₁, m₂ g ℓ₂ cos θ₂)` of the potential. -/
def hessian (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(P.m₁ + P.m₂) * P.g * P.ℓ₁ * cos (q 0), 0; 0, P.m₂ * P.g * P.ℓ₂ * cos (q 1)]

/-- The gradient `∇U` has derivative `ξ ↦ hessian q ξ`. -/
theorem hasFDerivAt_gradU (q : Fin 2 → ℝ) :
    HasFDerivAt P.gradU (LinearMap.toContinuousLinearMap (Matrix.toLin' (P.hessian q))) q := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · convert (hasFDerivAt_coord 0 q).sin.const_mul ((P.m₁ + P.m₂) * P.g * P.ℓ₁) using 1
    all_goals first
      | (funext x; simp [gradU])
      | (refine ContinuousLinearMap.ext fun w => ?_
         simp [hessian, dotProduct, Fin.sum_univ_two]; ring)
  · convert (hasFDerivAt_coord 1 q).sin.const_mul (P.m₂ * P.g * P.ℓ₂) using 1
    all_goals first
      | (funext x; simp [gradU])
      | (refine ContinuousLinearMap.ext fun w => ?_
         simp [hessian, dotProduct, Fin.sum_univ_two]; ring)

/-- The **frozen-mass natural system** `M(0) q̈ = -∇U(q)`: the double pendulum's potential
with the mass matrix of the hanging configuration. It has the same equilibria, Hessians and
linearization at `0` as the double pendulum. -/
def system : NaturalSystem 2 where
  M := P.massMatrix 0
  M_symm := P.massMatrix_transpose 0
  M_posDef := P.massMatrix_posDef 0
  U := P.potential
  gradU := P.gradU
  hasFDerivAt_U := P.hasFDerivAt_potential

/-- `hessian q` is the Hessian of `U` at `q`, in the sense of `NaturalSystem.HasHessian`. -/
theorem hasHessian (q : Fin 2 → ℝ) : P.system.HasHessian (P.hessian q) q :=
  P.hasFDerivAt_gradU q

/-- The **equilibria** are the critical points of `U`: `sin θ₁ = sin θ₂ = 0`. -/
theorem gradU_eq_zero_iff (q : Fin 2 → ℝ) :
    P.gradU q = 0 ↔ sin (q 0) = 0 ∧ sin (q 1) = 0 := by
  have h₁ : (P.m₁ + P.m₂) * P.g * P.ℓ₁ ≠ 0 := by
    have := P.m₁_pos; have := P.m₂_pos; have := P.g_pos; have := P.ℓ₁_pos; positivity
  have h₂ : P.m₂ * P.g * P.ℓ₂ ≠ 0 := by
    have := P.m₂_pos; have := P.g_pos; have := P.ℓ₂_pos; positivity
  rw [funext_iff, Fin.forall_fin_two]
  simp [gradU, h₁, h₂]

/-- The hanging position `0` is an **equilibrium**: `∇U(0) = 0`. -/
theorem gradU_zero : P.gradU 0 = 0 := by
  rw [gradU_eq_zero_iff]
  simp

/-- The **stiffness matrix** `K = diag((m₁ + m₂) g ℓ₁, m₂ g ℓ₂)` at the hanging position. -/
def K : Matrix (Fin 2) (Fin 2) ℝ := !![(P.m₁ + P.m₂) * P.g * P.ℓ₁, 0; 0, P.m₂ * P.g * P.ℓ₂]

/-- The stiffness matrix is symmetric. -/
theorem K_transpose : P.Kᵀ = P.K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K]

/-- **The Hessian of `U` at `0` is `K`.** -/
theorem hasHessian_zero : P.system.HasHessian P.K 0 := by
  have h : P.hessian 0 = P.K := by
    simp [hessian, K]
  exact h ▸ P.hasHessian 0

/-- A diagonal `2 × 2` matrix with positive entries is positive definite. -/
theorem posDef_diag {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (!![a, 0; 0, b]).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, cons_val_one, zero_mul, add_zero, zero_add]
    rcases hx' with h | h
    · have := pow_pos (sq_pos_of_ne_zero h) 1
      nlinarith [sq_nonneg (x 1), sq_pos_of_ne_zero h]
    · nlinarith [sq_nonneg (x 0), sq_pos_of_ne_zero h]

/-- The stiffness matrix `K` is **positive definite**. -/
theorem posDef_K : P.K.PosDef := by
  have := P.m₁_pos; have := P.m₂_pos; have := P.g_pos; have := P.ℓ₁_pos; have := P.ℓ₂_pos
  exact posDef_diag (by positivity) (by positivity)

/-- The hanging position is a **strict local minimum** of `U` (second-derivative test). -/
theorem strictMin_zero : ∃ r > 0, ∀ q : Fin 2 → ℝ, 0 < ‖q‖ → ‖q‖ ≤ r →
    P.potential 0 < P.potential q := by
  obtain ⟨r, hr, h⟩ := P.system.strictMin_of_posDef P.hasHessian_zero P.gradU_zero P.posDef_K
  exact ⟨r, hr, fun q hq hqr => by
    simpa [system] using h q (by simpa using hq) (by simpa using hqr)⟩

/-- The total energy is continuous on phase space. -/
theorem continuous_energy :
    Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => P.kinetic p.1 p.2 + P.potential p.1 := by
  unfold kinetic potential
  fun_prop

/-- **Stability of the hanging double pendulum** (Lagrange–Dirichlet): for every small `ε > 0`
there is `δ > 0` such that every solution of the Euler–Lagrange equations with `‖θ(0)‖ < δ`
and `‖θ̇(0)‖ < δ` satisfies `‖θ(t)‖ < ε` and `‖θ̇(t)‖ < ε` for all times. The proof uses the
conserved energy `T + U` as a Lyapunov function, with the uniform bound `T ≥ c ‖θ̇‖²`. -/
theorem lyapunovStable : ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r → ∃ δ > 0, ∀ γ : MotionN 2,
    P.lagrangian.EulerLagrange γ → ‖γ.q 0‖ < δ → ‖γ.v 0‖ < δ →
      ∀ t, ‖γ.q t‖ < ε ∧ ‖γ.v t‖ < ε := by
  obtain ⟨r, hr, hmin⟩ := P.strictMin_zero
  refine ⟨r, hr, fun ε hε hεr => ?_⟩
  have hcU : Continuous P.potential := P.system.continuous_U
  -- the energy barrier `m` on the sphere `‖q‖ = ε`
  obtain ⟨m, hm, hmS⟩ : ∃ m > 0, ∀ q ∈ Metric.sphere (0 : Fin 2 → ℝ) ε,
      P.potential 0 + m ≤ P.potential q := by
    rcases (Metric.sphere (0 : Fin 2 → ℝ) ε).eq_empty_or_nonempty with hs | hs
    · exact ⟨1, one_pos, by simp [hs]⟩
    · obtain ⟨q0, hq0, hq0min⟩ := (isCompact_sphere 0 ε).exists_isMinOn hs hcU.continuousOn
      have hd : ‖q0‖ = ε := mem_sphere_zero_iff_norm.mp hq0
      refine ⟨P.potential q0 - P.potential 0,
        sub_pos.2 (hmin q0 (hd ▸ hε) (hd ▸ hεr)), fun q hq => ?_⟩
      have := isMinOn_iff.mp hq0min q hq
      linarith
  obtain ⟨c, hc, hcT⟩ := P.exists_kinetic_coercive
  set η := min m (c * ε ^ 2) with hη_def
  have hη : 0 < η := lt_min hm (by positivity)
  obtain ⟨δ₀, hδ₀, hδ⟩ :=
    Metric.continuousAt_iff.1 (P.continuous_energy.continuousAt (x := (0, 0))) η hη
  refine ⟨min δ₀ ε, lt_min hδ₀ hε, fun γ hγ h0 hv0 => ?_⟩
  have hE0 : P.kinetic (γ.q 0) (γ.v 0) + P.potential (γ.q 0) < P.potential 0 + η := by
    have hd := hδ (x := (γ.q 0, γ.v 0)) (by
      rw [Prod.dist_eq, max_lt_iff, dist_zero_right, dist_zero_right]
      exact ⟨h0.trans_le (min_le_left _ _), hv0.trans_le (min_le_left _ _)⟩)
    rw [Real.dist_eq] at hd
    have hk0 : P.kinetic 0 0 = 0 := by simp [kinetic]
    simp only [hk0, zero_add] at hd
    linarith [(abs_lt.1 hd).2]
  have hE : ∀ t, P.kinetic (γ.q t) (γ.v t) + P.potential (γ.q t) < P.potential 0 + η :=
    fun t => P.energy_const hγ t 0 ▸ hE0
  -- the motion never reaches the sphere
  have hpos : ∀ t, ‖γ.q t‖ < ε := by
    intro t
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have hcq : Continuous γ.q :=
      continuous_iff_continuousAt.2 fun t => (γ.hasDerivAt_q t).continuousAt
    have hf : ContinuousOn (fun s => ‖γ.q s‖) (Set.uIcc 0 t) := hcq.norm.continuousOn
    have hmem : ε ∈ Set.uIcc ‖γ.q 0‖ ‖γ.q t‖ :=
      Set.mem_uIcc.2 (Or.inl ⟨(h0.trans_le (min_le_right _ _)).le, hcon⟩)
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hf hmem
    have h1 := hmS _ (mem_sphere_zero_iff_norm.mpr hs)
    have h2 := hE s
    have h3 := P.kinetic_nonneg (γ.q s) (γ.v s)
    have : η ≤ m := min_le_left _ _
    linarith
  refine fun t => ⟨hpos t, ?_⟩
  -- the velocity stays small
  have hU : P.potential 0 ≤ P.potential (γ.q t) := by
    rcases eq_or_lt_of_le (norm_nonneg (γ.q t)) with h | h
    · rw [eq_comm, norm_eq_zero] at h
      rw [h]
    · exact (hmin _ h ((hpos t).le.trans hεr)).le
  have h2 := hE t
  have h3 := hcT (γ.q t) (γ.v t)
  have : η ≤ c * ε ^ 2 := min_le_right _ _
  have h4 : c * ‖γ.v t‖ ^ 2 < c * ε ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_mul_lt_mul_left h4 hc.le)

/-- The **linearized double pendulum** `M(0) ξ̈ + K ξ = 0` about the hanging position. -/
def linearized : SmallOscillations 2 := P.system.linearization P.K P.K_transpose

/-- The linearized force about the hanging position is `-K ξ + o(ξ)`. -/
theorem linearized_force :
    (fun ξ => -P.gradU (0 + ξ) - -(P.K *ᵥ ξ)) =o[nhds 0] fun ξ => ξ :=
  P.system.linearized_force P.hasHessian_zero P.gradU_zero

/-- Every eigenfrequency of the linearized double pendulum is real: `ω² > 0`. -/
theorem omega_sq_pos {ω : ℝ} {φ : Fin 2 → ℝ} (h : P.linearized.IsMode ω φ) (hφ : φ ≠ 0) :
    0 < ω ^ 2 :=
  P.linearized.omega_sq_pos P.posDef_K h hφ

/-! ### Normal modes for equal masses and lengths -/

/-- For equal masses and lengths,
`det (K - λ M(0)) = m² ℓ⁴ (λ - (g/ℓ)(2 - √2)) (λ - (g/ℓ)(2 + √2))`. -/
theorem det_sub_smul (hm : P.m₁ = P.m₂) (hl : P.ℓ₁ = P.ℓ₂) (lam : ℝ) :
    (P.K - lam • P.massMatrix 0).det = P.m₂ ^ 2 * P.ℓ₂ ^ 4 *
      ((lam - P.g / P.ℓ₂ * (2 - √2)) * (lam - P.g / P.ℓ₂ * (2 + √2))) := by
  have hℓ := P.ℓ₂_pos.ne'
  rw [Matrix.det_fin_two]
  simp only [K, massMatrix, hm, hl, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Pi.zero_apply, sub_self, cos_zero]
  field_simp
  linear_combination (P.g ^ 2 * P.m₂ ^ 2 * P.ℓ₂ ^ 2) * sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- **Normal-mode frequencies of the double pendulum** with equal masses and lengths:
`det (K - ω² M(0)) = 0` iff `ω² = (g/ℓ)(2 - √2)` or `ω² = (g/ℓ)(2 + √2)`. -/
theorem det_sub_eq_zero_iff (hm : P.m₁ = P.m₂) (hl : P.ℓ₁ = P.ℓ₂) (ω : ℝ) :
    (P.K - ω ^ 2 • P.massMatrix 0).det = 0 ↔
      ω ^ 2 = P.g / P.ℓ₂ * (2 - √2) ∨ ω ^ 2 = P.g / P.ℓ₂ * (2 + √2) := by
  have h0 : P.m₂ ^ 2 * P.ℓ₂ ^ 4 ≠ 0 := by
    have := P.m₂_pos; have := P.ℓ₂_pos; positivity
  rw [P.det_sub_smul hm hl]
  simp [h0, sub_eq_zero]

/-- `2 - √2 ≥ 0`. -/
theorem two_sub_sqrt_two_nonneg : (0 : ℝ) ≤ 2 - √2 := by
  have : √2 ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  linarith

/-- The **slow normal mode** (in phase): for equal masses and lengths, `φ = (1, √2)` is a
normal mode with `ω² = (g/ℓ)(2 - √2)`. -/
theorem isMode_slow (hm : P.m₁ = P.m₂) (hl : P.ℓ₁ = P.ℓ₂) :
    P.linearized.IsMode √(P.g / P.ℓ₂ * (2 - √2)) ![1, √2] := by
  have hℓ := P.ℓ₂_pos.ne'
  have hω : √(P.g / P.ℓ₂ * (2 - √2)) ^ 2 = P.g / P.ℓ₂ * (2 - √2) :=
    sq_sqrt (mul_nonneg (div_nonneg P.g_pos.le P.ℓ₂_pos.le) two_sub_sqrt_two_nonneg)
  have h2 := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold SmallOscillations.IsMode
  rw [hω]
  ext i
  fin_cases i
  · simp [linearized, NaturalSystem.linearization, system, K, massMatrix, mulVec,
      dotProduct, Fin.sum_univ_two, hm, hl]
    field_simp
    linear_combination (P.m₂ * P.g) * h2
  · simp [linearized, NaturalSystem.linearization, system, K, massMatrix, mulVec,
      dotProduct, Fin.sum_univ_two, hm, hl]
    field_simp
    linear_combination (P.m₂ * P.g) * h2

/-- The **fast normal mode** (in antiphase): for equal masses and lengths, `φ = (1, -√2)` is a
normal mode with `ω² = (g/ℓ)(2 + √2)`. -/
theorem isMode_fast (hm : P.m₁ = P.m₂) (hl : P.ℓ₁ = P.ℓ₂) :
    P.linearized.IsMode √(P.g / P.ℓ₂ * (2 + √2)) ![1, -√2] := by
  have hℓ := P.ℓ₂_pos.ne'
  have hω : √(P.g / P.ℓ₂ * (2 + √2)) ^ 2 = P.g / P.ℓ₂ * (2 + √2) :=
    sq_sqrt (mul_nonneg (div_nonneg P.g_pos.le P.ℓ₂_pos.le) (by positivity))
  have h2 := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold SmallOscillations.IsMode
  rw [hω]
  ext i
  fin_cases i
  · simp [linearized, NaturalSystem.linearization, system, K, massMatrix, mulVec,
      dotProduct, Fin.sum_univ_two, hm, hl]
    field_simp
    linear_combination (P.m₂ * P.g) * h2
  · simp [linearized, NaturalSystem.linearization, system, K, massMatrix, mulVec,
      dotProduct, Fin.sum_univ_two, hm, hl]
    field_simp
    linear_combination (P.m₂ * P.g) * h2

/-! ### The unstable equilibria -/

/-- If `cos θ₁ < 0` or `cos θ₂ < 0`, the Hessian of `U` at `θ` is not positive semidefinite. -/
theorem not_posSemidef_hessian {q : Fin 2 → ℝ} (h : cos (q 0) < 0 ∨ cos (q 1) < 0) :
    ¬ (P.hessian q).PosSemidef := by
  intro hP
  have h₁ : 0 < (P.m₁ + P.m₂) * P.g * P.ℓ₁ := by
    have := P.m₁_pos; have := P.m₂_pos; have := P.g_pos; have := P.ℓ₁_pos; positivity
  have h₂ : 0 < P.m₂ * P.g * P.ℓ₂ := by
    have := P.m₂_pos; have := P.g_pos; have := P.ℓ₂_pos; positivity
  have e0 := hP.dotProduct_mulVec_nonneg ![1, 0]
  have e1 := hP.dotProduct_mulVec_nonneg ![0, 1]
  simp [hessian, mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  rcases h with h | h
  · nlinarith
  · nlinarith

/-- The three **inverted equilibria** `(0, π)`, `(π, 0)`, `(π, π)` are critical points of `U`
whose Hessians are not positive semidefinite, so the second-derivative test fails there. -/
theorem inverted_equilibria :
    (P.gradU ![0, π] = 0 ∧ ¬ (P.hessian ![0, π]).PosSemidef) ∧
    (P.gradU ![π, 0] = 0 ∧ ¬ (P.hessian ![π, 0]).PosSemidef) ∧
    (P.gradU ![π, π] = 0 ∧ ¬ (P.hessian ![π, π]).PosSemidef) := by
  refine ⟨⟨?_, P.not_posSemidef_hessian ?_⟩, ⟨?_, P.not_posSemidef_hessian ?_⟩,
    ⟨?_, P.not_posSemidef_hessian ?_⟩⟩ <;> simp [gradU_eq_zero_iff]

/-- The fully inverted position `(π, π)` is the **global maximum** of `U`. -/
theorem potential_le_top (q : Fin 2 → ℝ) : P.potential q ≤ P.potential ![π, π] := by
  have h₁ : 0 < (P.m₁ + P.m₂) * P.g * P.ℓ₁ := by
    have := P.m₁_pos; have := P.m₂_pos; have := P.g_pos; have := P.ℓ₁_pos; positivity
  have h₂ : 0 < P.m₂ * P.g * P.ℓ₂ := by
    have := P.m₂_pos; have := P.g_pos; have := P.ℓ₂_pos; positivity
  simp only [potential, Matrix.cons_val_zero, Matrix.cons_val_one, cos_pi]
  nlinarith [neg_one_le_cos (q 0), neg_one_le_cos (q 1)]

end DoublePendulum

end ClassicalMechanics
