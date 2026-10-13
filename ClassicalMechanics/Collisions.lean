import ClassicalMechanics.Vector

/-!
# Collisions

Two particles of masses `m₁, m₂ > 0` collide; their velocities are `u₁, u₂` before and `v₁, v₂`
after the collision, and the total momentum is conserved: `m₁ v₁ + m₂ v₂ = m₁ u₁ + m₂ u₂`.

**Head-on (one-dimensional) collisions.** The **coefficient of restitution** `e` is defined by
Newton's law of restitution `v₂ - v₁ = -e (u₂ - u₁)`.

* `collision_iff`: momentum conservation and the law of restitution determine the final velocities
  uniquely, `v₁ = finalVel₁`, `v₂ = finalVel₂`.
* `kinetic_loss`: the kinetic energy lost is `ΔT = ½ μ (1 - e²) (u₁ - u₂)²`, with the reduced mass
  `μ = m₁ m₂ / (m₁ + m₂)`. Hence `ΔT ≥ 0` for `0 ≤ e ≤ 1` (`kinetic_loss_nonneg`), and for
  `u₁ ≠ u₂`, `e ≥ 0` the energy is conserved iff `e = 1` (`energy_conserved_iff`).
* `elastic_equal_masses`: in an elastic collision of equal masses the velocities are exchanged.

**Three-dimensional elastic collisions.**

* `koenig_identity`: `(m₁ + m₂)(m₁ |a|² + m₂ |b|²) = |m₁ a + m₂ b|² + m₁ m₂ |a - b|²`, which is
  König's decomposition `T = ½ M |v_G|² + ½ μ |v₁ - v₂|²` of the kinetic energy.
* `elastic_relative_speed`: conservation of momentum and kinetic energy imply
  `|v₁ - v₂| = |u₁ - u₂|`; in the centre-of-mass frame the relative velocity is only rotated.
* `elastic_equal_masses_orthogonal`: if a particle hits an equal mass at rest elastically, the
  outgoing velocities are orthogonal, `v₁ · v₂ = 0`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §3.10.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §16–17.
* [KleppnerKolenkow2014] D. Kleppner, R. Kolenkow, *An Introduction to Mechanics*, 2nd ed., §4.7.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

namespace Collision

variable {m₁ m₂ u₁ u₂ v₁ v₂ e : ℝ}

/-- Reduced mass `μ = m₁ m₂ / (m₁ + m₂)` of the two colliding particles. -/
def reducedMass (m₁ m₂ : ℝ) : ℝ := m₁ * m₂ / (m₁ + m₂)

/-- Final velocity of particle `1` in a head-on collision with restitution coefficient `e`. -/
def finalVel₁ (m₁ m₂ u₁ u₂ e : ℝ) : ℝ := (m₁ * u₁ + m₂ * u₂ + m₂ * e * (u₂ - u₁)) / (m₁ + m₂)

/-- Final velocity of particle `2` in a head-on collision with restitution coefficient `e`. -/
def finalVel₂ (m₁ m₂ u₁ u₂ e : ℝ) : ℝ := (m₁ * u₁ + m₂ * u₂ + m₁ * e * (u₁ - u₂)) / (m₁ + m₂)

/-- Kinetic energy `½ m₁ w₁² + ½ m₂ w₂²` of the pair (one-dimensional). -/
def kinetic (m₁ m₂ w₁ w₂ : ℝ) : ℝ := m₁ / 2 * w₁ ^ 2 + m₂ / 2 * w₂ ^ 2

/-- **The outcome of a head-on collision**: momentum conservation together with the law of
restitution `v₂ - v₁ = -e (u₂ - u₁)` hold iff `v₁, v₂` are given by `finalVel₁, finalVel₂`. -/
theorem collision_iff (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (m₁ * v₁ + m₂ * v₂ = m₁ * u₁ + m₂ * u₂ ∧ v₂ - v₁ = -e * (u₂ - u₁)) ↔
      (v₁ = finalVel₁ m₁ m₂ u₁ u₂ e ∧ v₂ = finalVel₂ m₁ m₂ u₁ u₂ e) := by
  have hM : m₁ + m₂ ≠ 0 := by positivity
  simp only [finalVel₁, finalVel₂, eq_div_iff hM]
  constructor
  · rintro ⟨hp, hr⟩
    constructor
    · linear_combination hp - m₂ * hr
    · linear_combination hp + m₁ * hr
  · rintro ⟨h1, h2⟩
    constructor
    · apply mul_left_cancel₀ hM
      linear_combination m₁ * h1 + m₂ * h2
    · apply mul_left_cancel₀ hM
      linear_combination h2 - h1

/-- **Kinetic energy lost in a head-on collision**: `ΔT = ½ μ (1 - e²) (u₁ - u₂)²`. -/
theorem kinetic_loss (h₁ : 0 < m₁) (h₂ : 0 < m₂) (hp : m₁ * v₁ + m₂ * v₂ = m₁ * u₁ + m₂ * u₂)
    (hr : v₂ - v₁ = -e * (u₂ - u₁)) :
    kinetic m₁ m₂ u₁ u₂ - kinetic m₁ m₂ v₁ v₂ =
      reducedMass m₁ m₂ / 2 * (1 - e ^ 2) * (u₁ - u₂) ^ 2 := by
  obtain ⟨rfl, rfl⟩ := (collision_iff h₁ h₂).1 ⟨hp, hr⟩
  have hM : m₁ + m₂ ≠ 0 := by positivity
  simp only [kinetic, reducedMass, finalVel₁, finalVel₂]
  field_simp
  ring

/-- The reduced mass of two positive masses is positive. -/
theorem reducedMass_pos (h₁ : 0 < m₁) (h₂ : 0 < m₂) : 0 < reducedMass m₁ m₂ := by
  unfold reducedMass
  positivity

/-- For `0 ≤ e ≤ 1` (in fact `|e| ≤ 1`) kinetic energy is never gained in a collision. -/
theorem kinetic_loss_nonneg (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hp : m₁ * v₁ + m₂ * v₂ = m₁ * u₁ + m₂ * u₂) (hr : v₂ - v₁ = -e * (u₂ - u₁))
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1) :
    0 ≤ kinetic m₁ m₂ u₁ u₂ - kinetic m₁ m₂ v₁ v₂ := by
  rw [kinetic_loss h₁ h₂ hp hr]
  have hμ := reducedMass_pos h₁ h₂
  have : 0 ≤ 1 - e ^ 2 := by nlinarith
  positivity

/-- **Elastic collisions**: for `u₁ ≠ u₂` and `e ≥ 0`, kinetic energy is conserved iff `e = 1`. -/
theorem energy_conserved_iff (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hp : m₁ * v₁ + m₂ * v₂ = m₁ * u₁ + m₂ * u₂) (hr : v₂ - v₁ = -e * (u₂ - u₁))
    (hu : u₁ ≠ u₂) (he : 0 ≤ e) :
    kinetic m₁ m₂ v₁ v₂ = kinetic m₁ m₂ u₁ u₂ ↔ e = 1 := by
  have hloss := kinetic_loss h₁ h₂ hp hr
  have hμ := (reducedMass_pos h₁ h₂).ne'
  have hu' : (u₁ - u₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hu)
  constructor
  · intro hE
    rw [hE, sub_self] at hloss
    have h : 1 - e ^ 2 = 0 := by
      rcases mul_eq_zero.1 hloss.symm with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h (div_ne_zero hμ two_ne_zero)
        · exact h
      · exact absurd h hu'
    nlinarith
  · rintro rfl
    rw [one_pow, sub_self, mul_zero, zero_mul] at hloss
    linarith

/-- **Equal masses exchange velocities** in a perfectly elastic (`e = 1`) head-on collision. -/
theorem elastic_equal_masses {m : ℝ} (hm : 0 < m) (hp : m * v₁ + m * v₂ = m * u₁ + m * u₂)
    (hr : v₂ - v₁ = -1 * (u₂ - u₁)) : v₁ = u₂ ∧ v₂ = u₁ := by
  obtain ⟨h1, h2⟩ := (collision_iff hm hm).1 ⟨hp, hr⟩
  have hm2 : m + m ≠ 0 := by positivity
  rw [finalVel₁, eq_div_iff hm2] at h1
  rw [finalVel₂, eq_div_iff hm2] at h2
  constructor
  · apply mul_left_cancel₀ hm2
    linear_combination h1
  · apply mul_left_cancel₀ hm2
    linear_combination h2

/-- **König's identity** for two masses:
`(m₁ + m₂)(m₁ |a|² + m₂ |b|²) = |m₁ a + m₂ b|² + m₁ m₂ |a - b|²`. -/
theorem koenig_identity (m₁ m₂ : ℝ) (a b : Vec) :
    (m₁ + m₂) * (m₁ * normSq a + m₂ * normSq b) =
      normSq (m₁ • a + m₂ • b) + m₁ * m₂ * normSq (a - b) := by
  simp only [normSq, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **Elastic collisions in three dimensions**: if momentum and kinetic energy are conserved,
the relative speed is unchanged, `|v₁ - v₂|² = |u₁ - u₂|²`; the relative velocity is only
rotated (in the centre-of-mass frame, each velocity keeps its magnitude). -/
theorem elastic_relative_speed {u₁ u₂ v₁ v₂ : Vec} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hp : m₁ • v₁ + m₂ • v₂ = m₁ • u₁ + m₂ • u₂)
    (hE : m₁ / 2 * normSq v₁ + m₂ / 2 * normSq v₂ = m₁ / 2 * normSq u₁ + m₂ / 2 * normSq u₂) :
    normSq (v₁ - v₂) = normSq (u₁ - u₂) := by
  have kv := koenig_identity m₁ m₂ v₁ v₂
  have ku := koenig_identity m₁ m₂ u₁ u₂
  rw [hp] at kv
  have h : m₁ * m₂ * normSq (v₁ - v₂) = m₁ * m₂ * normSq (u₁ - u₂) := by
    linear_combination 2 * (m₁ + m₂) * hE - kv + ku
  exact mul_left_cancel₀ (by positivity) h

/-- **Elastic collision of equal masses, one at rest**: the outgoing velocities are orthogonal,
`v₁ · v₂ = 0`. -/
theorem elastic_equal_masses_orthogonal {m : ℝ} {u₁ v₁ v₂ : Vec} (hm : 0 < m)
    (hp : m • v₁ + m • v₂ = m • u₁ + m • (0 : Vec))
    (hE : m / 2 * normSq v₁ + m / 2 * normSq v₂ = m / 2 * normSq u₁ + m / 2 * normSq 0) :
    v₁ ⬝ᵥ v₂ = 0 := by
  have hu : u₁ = v₁ + v₂ := by
    rw [smul_zero, add_zero, ← smul_add] at hp
    exact (smul_right_injective Vec hm.ne' hp).symm
  subst hu
  have h : m * (v₁ ⬝ᵥ v₂) = 0 := by
    simp only [normSq, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.zero_apply] at hE ⊢
    linear_combination -hE
  exact (mul_eq_zero.1 h).resolve_left hm.ne'

end Collision

end ClassicalMechanics
