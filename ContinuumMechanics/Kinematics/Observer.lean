import ContinuumMechanics.Kinematics.Strain

/-!
# Change of observer and objectivity

Under a change of observer `x* = c + Q x` (`Q` orthogonal) the deformation gradient transforms as
`F* = Q F` ([Gurtin1981], §§18–19; [MarsdenHughes1983], §1.6). Kinematic quantities are
**objective** (frame-indifferent) if they transform as `T* = Q T Qᵀ` (tensors) or are
**invariant** (`T* = T`, referential quantities).

## Main results

* `Lin.rightCG_orth_mul`, `Lin.greenLagrange_orth_mul`, `Lin.rightStretch_orth_mul`:
  `C`, `E`, `U` are invariant.
* `Lin.leftCG_orth_mul`, `Lin.leftStretch_orth_mul`: `B`, `V` are objective.
* `Lin.polarRotation_orth_mul`: `R* = Q R`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§18–19.
* [MarsdenHughes1983] J. E. Marsden, T. J. R. Hughes, *Mathematical Foundations of Elasticity*,
  §1.6.
-/

open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- A function of the deformation gradient is **invariant** under changes of observer if
`f (Q F) = f F` for all orthogonal `Q`. -/
def IsObserverInvariant {α : Type*} (f : Lin E → α) : Prop := ∀ Q ∈ Orth E, ∀ F, f (Q * F) = f F

/-- A tensor-valued function of the deformation gradient is **objective** if
`f (Q F) = Q f(F) Qᵀ` for all orthogonal `Q`. [Gurtin1981], §19. -/
def IsObjective (f : Lin E → Lin E) : Prop := ∀ Q ∈ Orth E, ∀ F, f (Q * F) = Q * f F * Qᵀ

variable {Q : Lin E} (F : Lin E)

/-- `C* = C`. [Gurtin1981], §19. -/
theorem rightCG_orth_mul (hQ : Q ∈ Orth E) : rightCG (Q * F) = rightCG F := by
  rw [rightCG, rightCG, transpose_mul, mul_assoc, ← mul_assoc Qᵀ,
    transpose_mul_self_of_mem_orth hQ, one_mul]

/-- `B* = Q B Qᵀ`. [Gurtin1981], §19. -/
theorem leftCG_orth_mul : leftCG (Q * F) = Q * leftCG F * Qᵀ := by
  rw [leftCG, leftCG, transpose_mul]; simp only [mul_assoc]

/-- `E* = E`. -/
theorem greenLagrange_orth_mul (hQ : Q ∈ Orth E) : greenLagrange (Q * F) = greenLagrange F := by
  rw [greenLagrange, greenLagrange, rightCG_orth_mul F hQ]

/-- `U* = U`. -/
theorem rightStretch_orth_mul (hQ : Q ∈ Orth E) : rightStretch (Q * F) = rightStretch F := by
  rw [rightStretch, rightStretch, ← rightCG, ← rightCG, rightCG_orth_mul F hQ]

/-- `V* = Q V Qᵀ`. [Gurtin1981], §19. -/
theorem leftStretch_orth_mul (hQ : Q ∈ Orth E) :
    leftStretch (Q * F) = Q * leftStretch F * Qᵀ := by
  apply sqrt_unique (star_right_conjugate_nonneg (leftStretch_nonneg F) Q)
  calc Q * leftStretch F * Qᵀ * (Q * leftStretch F * Qᵀ)
      = Q * leftStretch F * (Qᵀ * Q) * leftStretch F * Qᵀ := by simp only [mul_assoc]
    _ = Q * leftCG F * Qᵀ := by
      rw [transpose_mul_self_of_mem_orth hQ, mul_one, leftCG_eq_sq_leftStretch]
      simp only [mul_assoc]
    _ = (Q * F) * (Q * F)ᵀ := by rw [← leftCG, leftCG_orth_mul]

/-- `R* = Q R`. [Gurtin1981], §19. -/
theorem polarRotation_orth_mul (hQ : Q ∈ Orth E) :
    polarRotation (Q * F) = Q * polarRotation F := by
  rw [polarRotation, polarRotation, rightStretch_orth_mul F hQ, mul_assoc]

theorem isObserverInvariant_rightCG : IsObserverInvariant (rightCG : Lin E → Lin E) := by
  intro Q hQ F; exact rightCG_orth_mul F hQ

theorem isObjective_leftCG : IsObjective (leftCG : Lin E → Lin E) := by
  intro Q _ F; exact leftCG_orth_mul F

end Lin

end ContinuumMechanics
