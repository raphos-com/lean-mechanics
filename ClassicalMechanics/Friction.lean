import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Coulomb friction

**Coulomb's law of dry friction**: a body pressed against a surface by the normal force `N` can
be held at rest by any friction force of magnitude `|F_f| ≤ μ_s N` (static friction); once it
slides, the friction force has magnitude `μ_k N` and opposes the velocity (kinetic friction).

* **Block on an incline** of angle `α ∈ [0, π/2)`: the normal force is `N = m g cos α` and the
  driving force `m g sin α`. The block can rest iff `tan α ≤ μ_s` (`incline_rest_iff`), i.e. iff
  `α ≤ α_r = arctan μ_s`, the **angle of repose** (`incline_rest_iff_le_repose`). A sliding block
  has acceleration `a = g (sin α - μ_k cos α)` (`sliding_accel`), positive iff `tan α > μ_k`
  (`sliding_accel_pos_iff`). Pushing it up at constant speed along the incline needs
  `P = m g (sin α + μ_k cos α)` (`push_force`); pulling at an angle `β` above the incline needs
  `P(β) = m g (sin α + μ cos α) / (cos β + μ sin β)` (`pull_force`). Since
  `cos β + μ sin β ≤ √(1 + μ²)` with equality at `β = arctan μ` (`cos_add_mul_sin_le`,
  `cos_add_mul_sin_arctan`), the optimal pulling angle is `tan β = μ` (`pull_force_min`).
* **Capstan (Euler–Eytelwein) equation**: along a rope on the verge of slipping around a fixed
  cylinder, `dT/dφ = μ T` on `[0, θ]`. Every solution is `T(φ) = T(0) e^{μφ}`, since
  `e^{-μφ} T(φ)` is constant (`capstan`); the holding ratio is `T(θ)/T(0) = e^{μθ}`
  (`capstan_ratio`), and with `n` full turns `e^{2πμn} = (e^{2πμ})ⁿ` (`capstan_turns`).
* **Oscillator with dry friction** `m ẍ + k x = -f sign ẋ` (`f = μ_k N`): while `ẋ ≤ 0` the motion
  is harmonic about the shifted centre `f/k`. Released from rest at `x₀ > f/k`,
  `x(t) = f/k + (x₀ - f/k) cos ωt` solves `m ẍ + k x = f` on `[0, π/ω]` with `ẋ ≤ 0` there
  (`coulomb_halfCycle_solves`, `coulomb_halfCycle_vel_nonpos`), and ends at rest at
  `x(π/ω) = -(x₀ - 2f/k)` (`coulomb_halfCycle_end`): the amplitude drops by `2f/k` per half-cycle
  and by `4f/k` per full cycle (`coulomb_fullCycle`), a *linear* decay. The mass stays at rest
  exactly when `|x| ≤ f/k`, where static friction can balance the spring (`coulomb_rest_iff`).
* **Rolling without slipping** down an incline, for a body with `I = β m R²`:
  `a = g sin α / (1 + β)` (`rolling_accel`), which is `5/7`, `2/3`, `1/2` of `g sin α` for a solid
  sphere, a solid cylinder and a hoop (`rolling_sphere`, `rolling_cylinder`, `rolling_hoop`); the
  friction force needed is `β m g sin α / (1 + β)`, so rolling requires
  `μ_s ≥ β tan α / (1 + β)` (`rolling_requires`).

## References

* [KleppnerKolenkow2014] D. Kleppner, R. Kolenkow, *An Introduction to Mechanics*, 2nd ed.,
  §§2.4, 7.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §1.4.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §25.
-/

open Set Real
open scoped Real

noncomputable section

namespace ClassicalMechanics

namespace Friction

/-! ### Block on an incline -/

/-- The normal force `N = m g cos α` on a block of mass `m` on an incline of angle `α`. -/
def normalForce (m g α : ℝ) : ℝ := m * g * cos α

/-- The component `m g sin α` of gravity along an incline of angle `α`. -/
def drivingForce (m g α : ℝ) : ℝ := m * g * sin α

/-- On an incline of angle `α ∈ [0, π/2)`, `cos α > 0`. -/
theorem cos_pos_of_incline {α : ℝ} (hα : α ∈ Ico 0 (π / 2)) : 0 < cos α :=
  cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], hα.2⟩

/-- **Block at rest on an incline**: the friction force needed for equilibrium,
`F_f = m g sin α`, satisfies Coulomb's bound `|F_f| ≤ μ_s N` iff `tan α ≤ μ_s`. -/
theorem incline_rest_iff {m g α μs : ℝ} (hm : 0 < m) (hg : 0 < g) (hα : α ∈ Ico 0 (π / 2)) :
    |drivingForce m g α| ≤ μs * normalForce m g α ↔ tan α ≤ μs := by
  have hc := cos_pos_of_incline hα
  have hs : 0 ≤ sin α := sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2, pi_pos])
  have hmg : 0 < m * g := mul_pos hm hg
  unfold drivingForce normalForce
  rw [abs_of_nonneg (mul_nonneg hmg.le hs), tan_eq_sin_div_cos, div_le_iff₀ hc]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Angle of repose**: on an incline of angle `α ∈ [0, π/2)` the block can rest iff
`α ≤ α_r = arctan μ_s`. -/
theorem incline_rest_iff_le_repose {m g α μs : ℝ} (hm : 0 < m) (hg : 0 < g)
    (hα : α ∈ Ico 0 (π / 2)) :
    |drivingForce m g α| ≤ μs * normalForce m g α ↔ α ≤ arctan μs := by
  rw [incline_rest_iff hm hg hα, ← arctan_strictMono.le_iff_le,
    arctan_tan (by linarith [hα.1, pi_pos]) hα.2]

/-- The angle of repose `arctan μ_s` has tangent `μ_s`. -/
theorem tan_repose (μs : ℝ) : tan (arctan μs) = μs := tan_arctan μs

/-- **Sliding down an incline**: Newton's law `m a = m g sin α - μ_k N` gives
`a = g (sin α - μ_k cos α)`. -/
theorem sliding_accel {m g α μk a : ℝ} (hm : 0 < m)
    (h : m * a = drivingForce m g α - μk * normalForce m g α) :
    a = g * (sin α - μk * cos α) := by
  unfold drivingForce normalForce at h
  have : m * (a - g * (sin α - μk * cos α)) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hm.ne'
  · linarith

/-- The sliding acceleration `g (sin α - μ_k cos α)` is positive iff `tan α > μ_k`. -/
theorem sliding_accel_pos_iff {g α μk : ℝ} (hg : 0 < g) (hα : α ∈ Ico 0 (π / 2)) :
    0 < g * (sin α - μk * cos α) ↔ μk < tan α := by
  have hc := cos_pos_of_incline hα
  rw [tan_eq_sin_div_cos, lt_div_iff₀ hc, mul_pos_iff_of_pos_left hg, sub_pos]

/-- **Pushing a block up an incline at constant speed**: with kinetic friction opposing the
motion, the force along the incline must be `P = m g (sin α + μ_k cos α)`. -/
theorem push_force {m g α μk P : ℝ}
    (h : P - drivingForce m g α - μk * normalForce m g α = 0) :
    P = m * g * (sin α + μk * cos α) := by
  unfold drivingForce normalForce at h
  linear_combination h

/-- **Pulling at an angle**: a force `P` at angle `β` above the incline reduces the normal force
to `N = m g cos α - P sin β`; balance along the incline, `P cos β = m g sin α + μ N`, gives
`P = m g (sin α + μ cos α) / (cos β + μ sin β)`. -/
theorem pull_force {m g α μ β P : ℝ} (hβ : 0 < cos β + μ * sin β)
    (h : P * cos β = drivingForce m g α + μ * (normalForce m g α - P * sin β)) :
    P = m * g * (sin α + μ * cos α) / (cos β + μ * sin β) := by
  unfold drivingForce normalForce at h
  rw [eq_div_iff hβ.ne']
  linear_combination h

/-- `cos β + μ sin β ≤ √(1 + μ²)` (Cauchy–Schwarz). -/
theorem cos_add_mul_sin_le (μ β : ℝ) : cos β + μ * sin β ≤ √(1 + μ ^ 2) := by
  refine le_trans (le_abs_self _) ?_
  rw [← sqrt_sq_eq_abs]
  refine sqrt_le_sqrt ?_
  nlinarith [sq_nonneg (μ * cos β - sin β), sin_sq_add_cos_sq β]

/-- The bound `cos β + μ sin β ≤ √(1 + μ²)` is attained at `β = arctan μ`. -/
theorem cos_add_mul_sin_arctan (μ : ℝ) :
    cos (arctan μ) + μ * sin (arctan μ) = √(1 + μ ^ 2) := by
  have hpos : 0 < √(1 + μ ^ 2) := sqrt_pos.mpr (by positivity)
  rw [cos_arctan, sin_arctan]
  field_simp
  rw [sq_sqrt (by positivity)]

/-- **Optimal pulling angle**: the pulling force
`P(β) = m g (sin α + μ cos α) / (cos β + μ sin β)` is minimal at `tan β = μ`, where it equals
`m g (sin α + μ cos α) / √(1 + μ²)`. -/
theorem pull_force_min {m g α μ β : ℝ} (hW : 0 ≤ m * g * (sin α + μ * cos α))
    (hβ : 0 < cos β + μ * sin β) :
    m * g * (sin α + μ * cos α) / (cos (arctan μ) + μ * sin (arctan μ)) ≤
      m * g * (sin α + μ * cos α) / (cos β + μ * sin β) := by
  rw [cos_add_mul_sin_arctan]
  exact div_le_div_of_nonneg_left hW hβ (cos_add_mul_sin_le μ β)

/-! ### The capstan equation -/

/-- **Capstan (Euler–Eytelwein) equation**: if the tension along a rope wrapped over `[0, θ]`
obeys `dT/dφ = μ T`, then `T(φ) = T(0) e^{μφ}` (the quantity `e^{-μφ} T(φ)` is constant). -/
theorem capstan {T T' : ℝ → ℝ} {μ θ : ℝ} (hT : ∀ φ ∈ Icc 0 θ, HasDerivAt T (T' φ) φ)
    (heq : ∀ φ ∈ Icc 0 θ, T' φ = μ * T φ) {φ : ℝ} (hφ : φ ∈ Icc 0 θ) :
    T φ = T 0 * exp (μ * φ) := by
  set ψ : ℝ → ℝ := fun s => exp (-(μ * s)) * T s with hψ
  have hd : ∀ s ∈ Icc 0 θ, HasDerivAt ψ 0 s := by
    intro s hs
    have h := (((hasDerivAt_id s).const_mul μ).neg.exp).mul (hT s hs)
    refine (h.congr_deriv ?_ :)
    rw [heq s hs]
    simp only [id, mul_one]
    ring
  have hc : ContinuousOn ψ (Icc 0 θ) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) φ hφ
  simp only [hψ, mul_zero, neg_zero, exp_zero, one_mul] at hconst
  rw [← hconst, mul_comm, ← mul_assoc, ← exp_add]
  simp

/-- The exponential profile `T₁ e^{μφ}` does solve the capstan equation `dT/dφ = μ T`. -/
theorem capstan_solves (T₁ μ φ : ℝ) :
    HasDerivAt (fun s => T₁ * exp (μ * s)) (μ * (T₁ * exp (μ * φ))) φ := by
  have h := (((hasDerivAt_id φ).const_mul μ).exp).const_mul T₁
  refine (h.congr_deriv ?_ :)
  simp only [id, mul_one]
  ring

/-- **Holding ratio**: a rope on the verge of slipping over the wrap angle `θ ≥ 0` has
`T(θ) / T(0) = e^{μθ}`. -/
theorem capstan_ratio {T T' : ℝ → ℝ} {μ θ : ℝ} (hθ : 0 ≤ θ)
    (hT : ∀ φ ∈ Icc 0 θ, HasDerivAt T (T' φ) φ) (heq : ∀ φ ∈ Icc 0 θ, T' φ = μ * T φ)
    (h0 : T 0 ≠ 0) : T θ / T 0 = exp (μ * θ) := by
  rw [capstan hT heq ⟨hθ, le_rfl⟩, mul_div_cancel_left₀ _ h0]

/-- **Several turns**: with `n` full turns (`θ = 2π n`) the holding ratio is
`e^{2πμn} = (e^{2πμ})ⁿ`: it grows exponentially with the number of turns. -/
theorem capstan_turns {T T' : ℝ → ℝ} {μ : ℝ} (n : ℕ)
    (hT : ∀ φ ∈ Icc 0 (2 * π * n), HasDerivAt T (T' φ) φ)
    (heq : ∀ φ ∈ Icc 0 (2 * π * n), T' φ = μ * T φ) (h0 : T 0 ≠ 0) :
    T (2 * π * n) / T 0 = exp (2 * π * μ * n) ∧ exp (2 * π * μ * n) = exp (2 * π * μ) ^ n := by
  refine ⟨?_, ?_⟩
  · rw [capstan_ratio (by positivity) hT heq h0]
    ring_nf
  · rw [← exp_nat_mul]
    ring_nf

/-- The holding ratio `e^{μθ}` is strictly increasing in the wrap angle when `μ > 0`. -/
theorem capstan_ratio_strictMono {μ : ℝ} (hμ : 0 < μ) : StrictMono fun θ : ℝ => exp (μ * θ) :=
  fun _ _ h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hμ)

/-! ### Oscillator with Coulomb friction -/

/-- The half-cycle motion about the shifted centre `c` with angular frequency `ω`, released from
rest at `x₀`: `x(t) = c + (x₀ - c) cos ωt`. -/
def halfCycle (c x₀ ω t : ℝ) : ℝ := c + (x₀ - c) * cos (ω * t)

/-- The velocity `-(x₀ - c) ω sin ωt` of the half-cycle motion. -/
def halfCycleVel (c x₀ ω t : ℝ) : ℝ := -(x₀ - c) * ω * sin (ω * t)

/-- The half-cycle position has derivative `halfCycleVel`. -/
theorem hasDerivAt_halfCycle (c x₀ ω t : ℝ) :
    HasDerivAt (halfCycle c x₀ ω) (halfCycleVel c x₀ ω t) t := by
  have h := (((hasDerivAt_id t).const_mul ω).cos.const_mul (x₀ - c)).const_add c
  refine (h.congr_deriv ?_ :)
  simp only [halfCycleVel, id, mul_one]
  ring

/-- The half-cycle velocity has derivative `-(x₀ - c) ω² cos ωt`. -/
theorem hasDerivAt_halfCycleVel (c x₀ ω t : ℝ) :
    HasDerivAt (halfCycleVel c x₀ ω) (-(x₀ - c) * ω ^ 2 * cos (ω * t)) t := by
  have h := ((hasDerivAt_id t).const_mul ω).sin.const_mul (-(x₀ - c) * ω)
  refine (h.congr_deriv ?_ :)
  simp only [id, mul_one]
  ring

/-- **Half-cycle with dry friction**: with `ω = √(k/m)` and friction force `f = μ N`,
`x(t) = f/k + (x₀ - f/k) cos ωt` solves `m ẍ + k x = f` and starts at rest at `x₀`. -/
theorem coulomb_halfCycle_solves {m k f x₀ : ℝ} (hm : 0 < m) (hk : 0 < k) (t : ℝ) :
    m * (-(x₀ - f / k) * √(k / m) ^ 2 * cos (√(k / m) * t)) +
        k * halfCycle (f / k) x₀ (√(k / m)) t = f ∧
      halfCycle (f / k) x₀ (√(k / m)) 0 = x₀ ∧ halfCycleVel (f / k) x₀ (√(k / m)) 0 = 0 := by
  refine ⟨?_, by simp [halfCycle], by simp [halfCycleVel]⟩
  rw [sq_sqrt (div_pos hk hm).le]
  unfold halfCycle
  field_simp
  ring

/-- **The velocity keeps its sign** during the half-cycle: if `x₀ > f/k` then `ẋ ≤ 0` on
`[0, π/ω]`, so kinetic friction indeed pushes in the `+` direction with magnitude `f`. -/
theorem coulomb_halfCycle_vel_nonpos {c x₀ ω t : ℝ} (hx : c < x₀) (hω : 0 < ω)
    (ht : t ∈ Icc 0 (π / ω)) : halfCycleVel c x₀ ω t ≤ 0 := by
  have h1 : 0 ≤ ω * t := mul_nonneg hω.le ht.1
  have h2 : ω * t ≤ π := by
    have := mul_le_mul_of_nonneg_left ht.2 hω.le
    rwa [mul_div_cancel₀ _ hω.ne'] at this
  have hs := sin_nonneg_of_nonneg_of_le_pi h1 h2
  unfold halfCycleVel
  have : 0 ≤ (x₀ - c) * ω * sin (ω * t) :=
    mul_nonneg (mul_nonneg (by linarith) hω.le) hs
  linarith

/-- **End of the half-cycle**: at `t = π/ω` the mass is again at rest, at
`x(π/ω) = 2c - x₀`; for the centre `c = f/k` this is `-(x₀ - 2f/k)`. -/
theorem coulomb_halfCycle_end {c x₀ ω : ℝ} (hω : 0 < ω) :
    halfCycle c x₀ ω (π / ω) = 2 * c - x₀ ∧ halfCycleVel c x₀ ω (π / ω) = 0 := by
  have h : ω * (π / ω) = π := mul_div_cancel₀ _ hω.ne'
  simp only [halfCycle, halfCycleVel, h, cos_pi, sin_pi]
  constructor <;> ring

/-- **Amplitude loss per half-cycle**: released at `x₀`, the mass stops at `-(x₀ - 2f/k)`, so the
turning points satisfy `x₀ + x(π/ω) = 2f/k`. -/
theorem coulomb_halfCycle_loss {k f x₀ ω : ℝ} (hω : 0 < ω) :
    halfCycle (f / k) x₀ ω (π / ω) = -(x₀ - 2 * f / k) ∧
      x₀ + halfCycle (f / k) x₀ ω (π / ω) = 2 * f / k := by
  rw [(coulomb_halfCycle_end hω).1]
  constructor <;> ring

/-- **Amplitude loss per full cycle**: the return half-cycle is harmonic about `-f/k`; starting
from the turning point `-(x₀ - 2f/k)` it ends at `x₀ - 4f/k`. The amplitude thus decays linearly,
by `4f/k` per cycle. -/
theorem coulomb_fullCycle {k f x₀ ω : ℝ} (hω : 0 < ω) :
    halfCycle (-(f / k)) (halfCycle (f / k) x₀ ω (π / ω)) ω (π / ω) = x₀ - 4 * f / k := by
  rw [(coulomb_halfCycle_end hω).1, (coulomb_halfCycle_end hω).1]
  ring

/-- **Where the motion stops**: a mass at rest at `x` stays at rest iff some friction force `F`
with `|F| ≤ f` balances the spring, `-k x + F = 0`; this holds iff `|x| ≤ f/k`. -/
theorem coulomb_rest_iff {k f x : ℝ} (hk : 0 < k) :
    (∃ F : ℝ, |F| ≤ f ∧ -k * x + F = 0) ↔ |x| ≤ f / k := by
  rw [le_div_iff₀ hk]
  constructor
  · rintro ⟨F, hF, h⟩
    have : F = k * x := by linarith
    rw [this, abs_mul, abs_of_pos hk] at hF
    linarith
  · intro h
    refine ⟨k * x, ?_, by ring⟩
    rw [abs_mul, abs_of_pos hk]
    linarith

/-! ### Rolling without slipping -/

/-- **Rolling down an incline**: a body of mass `m`, radius `R` and moment of inertia
`I = β m R²` obeys `m a = m g sin α - F`, `I ω̇ = F R`, and rolls without slipping, `a = R ω̇`.
Then `a = g sin α / (1 + β)` and the friction force is `F = β m g sin α / (1 + β)`. -/
theorem rolling_accel {m g R α β a ωd F : ℝ} (hm : 0 < m) (hR : 0 < R) (hβ : 0 ≤ β)
    (htr : m * a = m * g * sin α - F) (hrot : β * m * R ^ 2 * ωd = F * R) (hroll : a = R * ωd) :
    a = g * sin α / (1 + β) ∧ F = β * m * g * sin α / (1 + β) := by
  have hF : F = β * m * a := by
    have : R * (F - β * m * a) = 0 := by
      rw [hroll]; linear_combination -hrot
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hR.ne'
    · linarith
  have h1 : 0 < 1 + β := by linarith
  have ha : a = g * sin α / (1 + β) := by
    rw [eq_div_iff h1.ne']
    have : m * (a * (1 + β) - g * sin α) = 0 := by
      rw [hF] at htr; linear_combination htr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hm.ne'
    · linarith
  refine ⟨ha, ?_⟩
  rw [hF, ha]
  ring

/-- A **solid sphere** (`β = 2/5`) rolls down with `a = (5/7) g sin α`. -/
theorem rolling_sphere (g α : ℝ) : g * sin α / (1 + 2 / 5) = 5 / 7 * (g * sin α) := by ring

/-- A **solid cylinder** (`β = 1/2`) rolls down with `a = (2/3) g sin α`. -/
theorem rolling_cylinder (g α : ℝ) : g * sin α / (1 + 1 / 2) = 2 / 3 * (g * sin α) := by ring

/-- A **hoop** (`β = 1`) rolls down with `a = (1/2) g sin α`. -/
theorem rolling_hoop (g α : ℝ) : g * sin α / (1 + 1) = 1 / 2 * (g * sin α) := by ring

/-- **Condition for rolling**: the friction force `β m g sin α / (1 + β)` needed for rolling is
within Coulomb's bound `μ_s m g cos α` iff `μ_s ≥ β tan α / (1 + β)`. -/
theorem rolling_requires {m g α β μs : ℝ} (hm : 0 < m) (hg : 0 < g) (hβ : 0 ≤ β)
    (hα : α ∈ Ico 0 (π / 2)) :
    β * m * g * sin α / (1 + β) ≤ μs * normalForce m g α ↔ β * tan α / (1 + β) ≤ μs := by
  have hc := cos_pos_of_incline hα
  have h1 : 0 < 1 + β := by linarith
  have hmg : 0 < m * g := mul_pos hm hg
  unfold normalForce
  rw [tan_eq_sin_div_cos, div_le_iff₀ h1, div_le_iff₀ h1, mul_div_assoc', div_le_iff₀ hc]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end Friction

end ClassicalMechanics
