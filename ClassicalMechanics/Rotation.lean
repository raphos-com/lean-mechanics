import ClassicalMechanics.Vector

/-!
# Kinematics of rigid bodies

A rigid motion places the material point `X` at `x(t) = c(t) + R(t) X`, where `R(t)` is a
rotation: `Rᵀ R = R Rᵀ = I` ([Arnold1989], §26; [Goldstein2002], §4.8). Derivatives of matrices
are taken entrywise.

* `spatial_skew`, `body_skew`: the **spatial angular velocity** `Ω = Ṙ Rᵀ` and the **body angular
  velocity** `W = Rᵀ Ṙ` are skew, and `Ω = R W Rᵀ` (`spatial_eq_body`).
* `skew_mulVec_eq_cross`: a skew matrix acts as a cross product, `Ω v = ω × v`, with the **axial
  vector** `ω = (Ω₃₂, Ω₁₃, Ω₂₁)`.
* **Poisson's formula** (`poisson`): a vector carried by the body, `e(t) = R(t) E`, rotates as
  `ė = ω × e`.
* **Rigid velocity field** (`rigid_velocity`): `ẋ = ċ + ω × (x - c)`, the field used in
  `RigidBody.angMom_rigid` and `RigidBody.kinetic_rigid`.
* Rotations preserve dot products and distances (`dot_rotation`).

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §26.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §4.8.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- 3×3 real matrices. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

/-- The **axial vector** `(Ω₃₂, Ω₁₃, Ω₂₁)` of a matrix. -/
def axial (Ω : Mat) : Vec := ![Ω 2 1, Ω 0 2, Ω 1 0]

/-- A skew matrix acts as the cross product with its axial vector: `Ω v = ω × v`. -/
theorem skew_mulVec_eq_cross {Ω : Mat} (h : Ωᵀ = -Ω) (v : Vec) : Ω *ᵥ v = axial Ω ⨯₃ v := by
  have e : ∀ i j, Ω j i = -Ω i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa using this
  have d : ∀ i, Ω i i = 0 := fun i => by have := e i i; linarith
  ext i
  fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_three, axial, cross_apply, d, e 0 1, e 0 2, e 1 2] <;>
    ring

/-- Rotations preserve dot products. -/
theorem dot_rotation {R : Mat} (hR : Rᵀ * R = 1) (u v : Vec) : (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hR, one_mulVec,
    dotProduct_comm]

/-- A **rigid motion** `x(t) = c(t) + R(t) X` with `R(t)` a rotation. -/
structure RigidMotion where
  R : ℝ → Mat
  R' : ℝ → Mat
  c : ℝ → Vec
  c' : ℝ → Vec
  orth : ∀ t, (R t)ᵀ * R t = 1
  orth' : ∀ t, R t * (R t)ᵀ = 1
  hasDerivAt_R : ∀ t i j, HasDerivAt (fun s => R s i j) (R' t i j) t
  hasDerivAt_c : ∀ t, HasDerivAt c (c' t) t

namespace RigidMotion

variable (B : RigidMotion)

/-- Spatial angular velocity `Ω = Ṙ Rᵀ`. -/
def Ω (t : ℝ) : Mat := B.R' t * (B.R t)ᵀ

/-- Body angular velocity `W = Rᵀ Ṙ`. -/
def W (t : ℝ) : Mat := (B.R t)ᵀ * B.R' t

/-- The angular velocity vector `ω`, axial vector of `Ω`. -/
def ω (t : ℝ) : Vec := axial (B.Ω t)

/-- A quantity constant in time has zero derivative. -/
theorem deriv_const_eq_zero {f : ℝ → ℝ} {d c t : ℝ} (hc : ∀ s, f s = c) (h : HasDerivAt f d t) :
    d = 0 := by
  have : f = fun _ => c := funext hc
  rw [this] at h
  exact h.unique (hasDerivAt_const t c)

/-- `Ω = Ṙ Rᵀ` is skew. -/
theorem spatial_skew (t : ℝ) : (B.Ω t)ᵀ = -B.Ω t := by
  ext i j
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (B.hasDerivAt_R t i k).mul (B.hasDerivAt_R t j k)
  have h0 := deriv_const_eq_zero (fun s => by
    have := congrFun (congrFun (B.orth' s) i) j
    simp only [mul_apply, transpose_apply] at this
    exact this) h
  simp only [Finset.sum_add_distrib] at h0
  change ∑ k, B.R' t j k * B.R t i k = -(∑ k, B.R' t i k * B.R t j k)
  have e : ∑ k, B.R t i k * B.R' t j k = ∑ k, B.R' t j k * B.R t i k :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  linarith

/-- `W = Rᵀ Ṙ` is skew. -/
theorem body_skew (t : ℝ) : (B.W t)ᵀ = -B.W t := by
  ext i j
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (B.hasDerivAt_R t k i).mul (B.hasDerivAt_R t k j)
  have h0 := deriv_const_eq_zero (fun s => by
    have := congrFun (congrFun (B.orth s) i) j
    simp only [mul_apply, transpose_apply] at this
    exact this) h
  simp only [Finset.sum_add_distrib] at h0
  change ∑ k, B.R t k j * B.R' t k i = -(∑ k, B.R t k i * B.R' t k j)
  have e : ∑ k, B.R' t k i * B.R t k j = ∑ k, B.R t k j * B.R' t k i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  linarith

/-- `Ω = R W Rᵀ`. -/
theorem spatial_eq_body (t : ℝ) : B.Ω t = B.R t * B.W t * (B.R t)ᵀ := by
  rw [W, ← Matrix.mul_assoc, B.orth' t, Matrix.one_mul, Ω]

theorem hasDerivAt_mulVec (t : ℝ) (E : Vec) :
    HasDerivAt (fun s => B.R s *ᵥ E) (B.R' t *ᵥ E) t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (B.hasDerivAt_R t i j).mul_const (E j)
  convert h using 1
  · funext s; simp [mulVec, dotProduct]
  · simp [mulVec, dotProduct]

/-- `Ṙ E = ω × R E`. -/
theorem R'_mulVec (t : ℝ) (E : Vec) : B.R' t *ᵥ E = B.ω t ⨯₃ (B.R t *ᵥ E) := by
  rw [ω, ← skew_mulVec_eq_cross (B.spatial_skew t), Ω, mulVec_mulVec, Matrix.mul_assoc,
    B.orth t, Matrix.mul_one]

/-- **Poisson's formula**: a vector carried by the body, `e(t) = R(t) E`, rotates as
`ė = ω × e`. -/
theorem poisson (t : ℝ) (E : Vec) :
    HasDerivAt (fun s => B.R s *ᵥ E) (B.ω t ⨯₃ (B.R t *ᵥ E)) t := by
  rw [← B.R'_mulVec]
  exact B.hasDerivAt_mulVec t E

/-- **Rigid velocity field**: the material point `X` moves with velocity
`ẋ = ċ + ω × (x - c)`. -/
theorem rigid_velocity (t : ℝ) (X : Vec) :
    HasDerivAt (fun s => B.c s + B.R s *ᵥ X)
      (B.c' t + B.ω t ⨯₃ ((B.c t + B.R t *ᵥ X) - B.c t)) t := by
  rw [add_sub_cancel_left]
  exact (B.hasDerivAt_c t).add (B.poisson t X)

/-- Rigid motions preserve distances between material points. -/
theorem dist_preserved (t : ℝ) (X Y : Vec) :
    normSq ((B.c t + B.R t *ᵥ X) - (B.c t + B.R t *ᵥ Y)) = normSq (X - Y) := by
  rw [add_sub_add_left_eq_sub, ← mulVec_sub, normSq, dot_rotation (B.orth t), normSq]

end RigidMotion

end ClassicalMechanics
