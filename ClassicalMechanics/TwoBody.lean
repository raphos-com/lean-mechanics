import ClassicalMechanics.Particles

/-!
# The two-body problem: reduction to one body

Two isolated particles `0`, `1` with masses `m₀, m₁ > 0`, interacting through the force `F` exerted
on `0` by `1`, separate into ([Goldstein2002], §3.1; [Landau1976], §13):

* the motion of the centre of mass, which is uniform (`ParticleSystem.momentum_conserved`), and
* the motion of the **relative position** `r = x₀ - x₁`, which is that of a single particle of
  **reduced mass** `μ = m₀ m₁ / (m₀ + m₁)` acted on by `F` (`reduced_newton`): `μ r̈ = F`.

The kinetic energy splits accordingly (`kinetic_split`, König):
`T = ½ M |v_G|² + ½ μ |ṙ|²`, with `M = m₀ + m₁` and `v_G = P / M`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §3.1.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §13.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

namespace ParticleSystem

variable (S : ParticleSystem (Fin 2))

/-- Reduced mass `μ = m₀ m₁ / (m₀ + m₁)`. -/
def reducedMass : ℝ := S.m 0 * S.m 1 / (S.m 0 + S.m 1)

/-- **Reduction to one body**: for an isolated pair of particles of positive masses, the relative
position `r = x₀ - x₁` obeys `μ r̈ = F₀₁`. -/
theorem reduced_newton (h0 : 0 < S.m 0) (h1 : 0 < S.m 1) (hext : ∀ t i, S.Fe t i = 0) (t : ℝ) :
    HasDerivAt (fun s => S.x s 0 - S.x s 1) (S.v t 0 - S.v t 1) t ∧
      HasDerivAt (fun s => S.v s 0 - S.v s 1) (S.a t 0 - S.a t 1) t ∧
      S.reducedMass • (S.a t 0 - S.a t 1) = S.F t 0 1 := by
  refine ⟨(S.hasDerivAt_x t 0).sub (S.hasDerivAt_x t 1),
    (S.hasDerivAt_v t 0).sub (S.hasDerivAt_v t 1), ?_⟩
  have n0 := S.newton t 0
  have n1 := S.newton t 1
  simp only [Fin.sum_univ_two, S.self_force, hext, add_zero, zero_add] at n0 n1
  rw [S.reaction t 0 1] at n1
  -- `aᵢ = Fᵢ / mᵢ`
  have a0 : S.a t 0 = (S.m 0)⁻¹ • S.F t 0 1 := by
    rw [← n0, smul_smul, inv_mul_cancel₀ h0.ne', one_smul]
  have a1 : S.a t 1 = -(S.m 1)⁻¹ • S.F t 0 1 := by
    rw [neg_smul, ← smul_neg, ← n1, smul_smul, inv_mul_cancel₀ h1.ne', one_smul]
  rw [a0, a1, ← sub_smul, smul_smul, reducedMass]
  convert one_smul ℝ (S.F t 0 1) using 2
  field_simp
  ring

/-- **König's decomposition for two bodies**: `T = ½ M |v_G|² + ½ μ |ṙ|²`, with `v_G = P / M`. -/
theorem kinetic_split (h0 : 0 < S.m 0) (h1 : 0 < S.m 1) (t : ℝ) :
    S.kinetic t = S.mass / 2 * normSq (S.mass⁻¹ • S.momentum t) +
      S.reducedMass / 2 * normSq (S.v t 0 - S.v t 1) := by
  have hM : S.mass = S.m 0 + S.m 1 := Fin.sum_univ_two _
  have hM0 : S.m 0 + S.m 1 ≠ 0 := by positivity
  simp only [kinetic, momentum, normSq, reducedMass, hM, Fin.sum_univ_two, smul_add,
    dotProduct_add, add_dotProduct, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_smul]
  rw [dotProduct_comm (S.v t 1) (S.v t 0)]
  field_simp
  ring

end ParticleSystem

end ClassicalMechanics
