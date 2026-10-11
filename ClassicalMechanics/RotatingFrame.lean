import ClassicalMechanics.Rotation

/-!
# Motion relative to a rotating frame: Coriolis and centrifugal forces

Let `R(t)` be the rotation carrying the axes of a moving frame (with origin fixed) onto the inertial
axes, and let `w` be the **body angular velocity**, the axial vector of `W = Rᵀ Ṙ`
(`RigidMotion.body_skew`). A point with coordinates `y(t)` in the moving frame is at
`x(t) = R(t) y(t)` in the inertial frame. With `v = ẏ` and `a = v̇` the relative velocity and
acceleration ([Goldstein2002], §4.10; [Arnold1989], §27; [Landau1976], §39):

* `velocity` : `ẋ = R (v + w × y)`;
* `acceleration` : `ẍ = R (a + 2 w × v + w × (w × y) + ẇ × y)`;
* `newton_rotating` : Newton's law `m ẍ = R f` in the inertial frame (with `f` the force in moving
  coordinates) is equivalent to

  `m a = f - 2m w × v - m w × (w × y) - m ẇ × y`,

  i.e. in the moving frame the particle feels, besides `f`, the **Coriolis force** `-2m w × v`,
  the **centrifugal force** `-m w × (w × y)` and the **Euler force** `-m ẇ × y`.
* `centrifugal_eq` : `-w × (w × y) = |w|² y - (w · y) w`, the component of `|w|² y` orthogonal to
  the axis.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §4.10.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §27.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §39.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- Product rule for a time-dependent matrix acting on a time-dependent vector. -/
theorem hasDerivAt_mulVec_mulVec {R : ℝ → Mat} {R' : Mat} {u : ℝ → Vec} {u' : Vec} {t : ℝ}
    (hR : ∀ i j, HasDerivAt (fun s => R s i j) (R' i j) t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => R s *ᵥ u s) (R' *ᵥ u t + R t *ᵥ u') t := by
  have hu' := hasDerivAt_pi.1 hu
  refine hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hR i j).mul (hu' j)
  convert h using 1
  · funext s; simp [mulVec, dotProduct]
  · simp [mulVec, dotProduct, Finset.sum_add_distrib]

namespace RigidMotion

variable (B : RigidMotion)

/-- The body angular velocity vector `w`, axial vector of `W = Rᵀ Ṙ`. -/
def wb (t : ℝ) : Vec := axial (B.W t)

/-- `Ṙ v = R (w × v)`. -/
theorem R'_mulVec_body (t : ℝ) (v : Vec) : B.R' t *ᵥ v = B.R t *ᵥ (B.wb t ⨯₃ v) := by
  rw [wb, ← skew_mulVec_eq_cross (B.body_skew t), W, mulVec_mulVec, ← Matrix.mul_assoc,
    B.orth' t, Matrix.one_mul]

/-- `R` is injective. -/
theorem R_mulVec_injective (t : ℝ) : Function.Injective (B.R t *ᵥ ·) := fun u v h => by
  have := congrArg ((B.R t)ᵀ *ᵥ ·) h
  simpa only [mulVec_mulVec, B.orth t, one_mulVec] using this

variable {y v a : ℝ → Vec} {w' : Vec} {t : ℝ}

/-- **Velocity in a rotating frame**: `d/dt (R y) = R (ẏ + w × y)`. -/
theorem velocity (hy : HasDerivAt y (v t) t) :
    HasDerivAt (fun s => B.R s *ᵥ y s) (B.R t *ᵥ (v t + B.wb t ⨯₃ y t)) t := by
  have h := hasDerivAt_mulVec_mulVec (B.hasDerivAt_R t) hy
  rw [B.R'_mulVec_body] at h
  rwa [mulVec_add, add_comm]

/-- **Acceleration in a rotating frame**:
`d/dt (R (v + w × y)) = R (a + 2 w × v + w × (w × y) + ẇ × y)`. -/
theorem acceleration (hy : HasDerivAt y (v t) t) (hv : HasDerivAt v (a t) t)
    (hw : HasDerivAt B.wb w' t) :
    HasDerivAt (fun s => B.R s *ᵥ (v s + B.wb s ⨯₃ y s))
      (B.R t *ᵥ (a t + (2 : ℝ) • (B.wb t ⨯₃ v t) + B.wb t ⨯₃ (B.wb t ⨯₃ y t) + w' ⨯₃ y t)) t := by
  have hu := hv.add (hasDerivAt_cross hw hy)
  have h := hasDerivAt_mulVec_mulVec (B.hasDerivAt_R t) hu
  rw [B.R'_mulVec_body, ← mulVec_add] at h
  convert h using 2
  simp only [Pi.add_apply, map_add, two_smul]
  abel

/-- **Newton's law in a rotating frame**: `m ẍ = R f` holds iff
`m a = f - 2m w × v - m w × (w × y) - m ẇ × y` (Coriolis, centrifugal and Euler forces). -/
theorem newton_rotating (m : ℝ) (f : Vec) (y v a w' : Vec) (t : ℝ) :
    m • (B.R t *ᵥ (a + (2 : ℝ) • (B.wb t ⨯₃ v) + B.wb t ⨯₃ (B.wb t ⨯₃ y) + w' ⨯₃ y)) =
        B.R t *ᵥ f ↔
      m • a = f - (2 * m) • (B.wb t ⨯₃ v) - m • (B.wb t ⨯₃ (B.wb t ⨯₃ y)) - m • (w' ⨯₃ y) := by
  rw [← mulVec_smul, (B.R_mulVec_injective t).eq_iff, smul_add, smul_add, smul_add, smul_smul,
    mul_comm m 2]
  constructor <;> intro h
  · rw [← h]; abel
  · rw [h]; abel

end RigidMotion

/-- The centrifugal acceleration `-w × (w × y) = |w|² y - (w · y) w` points away from the axis. -/
theorem centrifugal_eq (w y : Vec) : -(w ⨯₃ (w ⨯₃ y)) = normSq w • y - (w ⬝ᵥ y) • w := by
  rw [cross_cross_eq_smul_sub_smul', normSq, neg_sub]

end ClassicalMechanics
