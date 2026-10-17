import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Plane stress transformation and Mohr's circle

A **plane stress state** is a symmetric `2 × 2` stress matrix
`σ = [[σx, τxy], [τxy, σy]]`. Rotating the coordinate axes by an angle `θ` (rotation matrix
`R(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]`, whose columns are the rotated basis vectors) gives
the components `σ' = Rᵀ σ R` in the rotated frame:

* `σx'(θ) = (σx + σy)/2 + (σx - σy)/2 · cos 2θ + τxy · sin 2θ`,
* `σy'(θ) = (σx + σy)/2 - (σx - σy)/2 · cos 2θ - τxy · sin 2θ`,
* `τx'y'(θ) = -(σx - σy)/2 · sin 2θ + τxy · cos 2θ`.

As `θ` varies, the point `(σx'(θ), τx'y'(θ))` traces **Mohr's circle**, with centre
`C = (σx + σy)/2` and radius `R = √(((σx - σy)/2)² + τxy²)`. The **principal stresses**
`σ₁,₂ = C ± R` are the eigenvalues of `σ`, the extreme values of the normal stress `σx'`,
attained at the principal angle `θ_p` (`tan 2θ_p = 2τxy/(σx - σy)`), where the shear stress
vanishes; the maximum in-plane shear stress is `R`, attained at `θ_p ± π/4`.

This is a concrete two-dimensional companion of `ContinuumMechanics.Stress.Criteria`.

## Main results

* `PlaneStress.rotate_eq`: the transformation formulas are the entries of `Rᵀ σ R`.
* `PlaneStress.sigmaX'_add_sigmaY'`, `PlaneStress.det_rot`: the invariants
  `σx' + σy'` and `σx' σy' - τx'y'²`.
* `PlaneStress.mohr_circle`: `(σx'(θ) - C)² + τx'y'(θ)² = R²`.
* `PlaneStress.det_sub_eq_zero_iff`: `det (σ - λ I) = 0 ↔ λ = C + R ∨ λ = C - R`.
* `PlaneStress.sigmaX'_le`, `PlaneStress.le_sigmaX'`, `PlaneStress.principal_attained`:
  `C - R ≤ σx'(θ) ≤ C + R`, with `σx'(θ_p) = C + R` and `τx'y'(θ_p) = 0`.
* `PlaneStress.abs_tau'_le`, `PlaneStress.maxShear_attained`: `|τx'y'(θ)| ≤ R`, with
  equality at `θ_p ± π/4`.
* `PlaneStress.vonMises_principal`: `σ₁² - σ₁σ₂ + σ₂² = σx² - σxσy + σy² + 3τxy²`.

## References

* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §§7.2–7.4.
* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
-/

open Real Matrix

namespace ContinuumMechanics

/-- A plane (two-dimensional, symmetric) stress state `σ = [[σx, τxy], [τxy, σy]]`. -/
structure PlaneStress where
  /-- The normal stress in the `x` direction. -/
  σx : ℝ
  /-- The normal stress in the `y` direction. -/
  σy : ℝ
  /-- The shear stress. -/
  τxy : ℝ

namespace PlaneStress

variable (s : PlaneStress) (θ : ℝ)

/-- The stress matrix `[[σx, τxy], [τxy, σy]]`. -/
def toMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![s.σx, s.τxy; s.τxy, s.σy]

/-- The rotation matrix `R(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]`. -/
noncomputable def rot : Matrix (Fin 2) (Fin 2) ℝ := !![cos θ, -sin θ; sin θ, cos θ]

/-- The centre `C = (σx + σy)/2` of Mohr's circle (the mean normal stress). -/
noncomputable def center : ℝ := (s.σx + s.σy) / 2

/-- The radius `R = √(((σx - σy)/2)² + τxy²)` of Mohr's circle (the maximum in-plane shear). -/
noncomputable def radius : ℝ := √(((s.σx - s.σy) / 2) ^ 2 + s.τxy ^ 2)

/-- The rotated normal stress
`σx'(θ) = (σx + σy)/2 + (σx - σy)/2 · cos 2θ + τxy · sin 2θ`. -/
noncomputable def sigmaX' : ℝ :=
  (s.σx + s.σy) / 2 + (s.σx - s.σy) / 2 * cos (2 * θ) + s.τxy * sin (2 * θ)

/-- The rotated normal stress
`σy'(θ) = (σx + σy)/2 - (σx - σy)/2 · cos 2θ - τxy · sin 2θ`. -/
noncomputable def sigmaY' : ℝ :=
  (s.σx + s.σy) / 2 - (s.σx - s.σy) / 2 * cos (2 * θ) - s.τxy * sin (2 * θ)

/-- The rotated shear stress `τx'y'(θ) = -(σx - σy)/2 · sin 2θ + τxy · cos 2θ`. -/
noncomputable def tau' : ℝ := -((s.σx - s.σy) / 2) * sin (2 * θ) + s.τxy * cos (2 * θ)

/-- The rotated stress state `(σx'(θ), σy'(θ), τx'y'(θ))`. -/
noncomputable def rotate : PlaneStress := ⟨s.sigmaX' θ, s.sigmaY' θ, s.tau' θ⟩

/-- The rotation matrix is orthogonal: `Rᵀ R = 1`. -/
theorem rot_transpose_mul_rot : (rot θ)ᵀ * rot θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [sin_sq_add_cos_sq θ]

/-- **Transformation of plane stress**: the rotated components are the entries of `Rᵀ σ R`. -/
theorem rotate_eq : (s.rotate θ).toMatrix = (rot θ)ᵀ * s.toMatrix * rot θ := by
  have h1 := cos_two_mul θ
  have h2 := sin_two_mul θ
  have h3 := sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotate, toMatrix, rot, sigmaX', sigmaY', tau', Matrix.mul_apply, Fin.sum_univ_two,
      h1, h2]
  · linear_combination (-s.σy) * h3
  · linear_combination s.τxy * h3
  · linear_combination s.τxy * h3
  · linear_combination (-s.σx) * h3

/-- **First invariant**: `σx'(θ) + σy'(θ) = σx + σy`. -/
theorem sigmaX'_add_sigmaY' : s.sigmaX' θ + s.sigmaY' θ = s.σx + s.σy := by
  simp only [sigmaX', sigmaY']
  ring

/-- **Second invariant**: `σx'(θ) σy'(θ) - τx'y'(θ)² = σx σy - τxy²`. -/
theorem det_rot : s.sigmaX' θ * s.sigmaY' θ - s.tau' θ ^ 2 = s.σx * s.σy - s.τxy ^ 2 := by
  simp only [sigmaX', sigmaY', tau']
  linear_combination (-(((s.σx - s.σy) / 2) ^ 2 + s.τxy ^ 2)) * sin_sq_add_cos_sq (2 * θ)

/-- The determinant of the stress matrix is `σx σy - τxy²`. -/
theorem det_toMatrix : s.toMatrix.det = s.σx * s.σy - s.τxy ^ 2 := by
  simp [toMatrix, Matrix.det_fin_two]
  ring

/-- The trace of the stress matrix is `σx + σy`. -/
theorem trace_toMatrix : Matrix.trace s.toMatrix = s.σx + s.σy := by
  simp [toMatrix, Matrix.trace, Fin.sum_univ_two]

/-- The radius of Mohr's circle is nonnegative. -/
theorem radius_nonneg : 0 ≤ s.radius := Real.sqrt_nonneg _

/-- The square of the radius: `R² = ((σx - σy)/2)² + τxy²`. -/
theorem radius_sq : s.radius ^ 2 = ((s.σx - s.σy) / 2) ^ 2 + s.τxy ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **Mohr's circle**: `(σx'(θ) - C)² + τx'y'(θ)² = R²`. -/
theorem mohr_circle : (s.sigmaX' θ - s.center) ^ 2 + s.tau' θ ^ 2 = s.radius ^ 2 := by
  rw [radius_sq]
  simp only [sigmaX', tau', center]
  linear_combination (((s.σx - s.σy) / 2) ^ 2 + s.τxy ^ 2) * sin_sq_add_cos_sq (2 * θ)

/-- The rotated normal stress `σy'` also lies on Mohr's circle. -/
theorem mohr_circle_sigmaY' : (s.sigmaY' θ - s.center) ^ 2 + s.tau' θ ^ 2 = s.radius ^ 2 := by
  rw [← s.mohr_circle θ]
  simp only [sigmaX', sigmaY', center]
  ring

/-- The **principal stresses** are the eigenvalues of the stress matrix:
`det (σ - λ I) = 0 ↔ λ = C + R ∨ λ = C - R`. -/
theorem det_sub_eq_zero_iff (l : ℝ) :
    (s.toMatrix - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      l = s.center + s.radius ∨ l = s.center - s.radius := by
  have hdet : (s.toMatrix - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (l - s.center) ^ 2 - s.radius ^ 2 := by
    rw [radius_sq]
    simp [toMatrix, center, Matrix.det_fin_two]
    ring
  rw [hdet, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> rintro (h | h)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The normal stress is bounded by Mohr's circle: `|σx'(θ) - C| ≤ R`. -/
theorem abs_sigmaX'_sub_center_le : |s.sigmaX' θ - s.center| ≤ s.radius :=
  Real.abs_le_sqrt (by nlinarith [s.mohr_circle θ, s.radius_sq, sq_nonneg (s.tau' θ)])

/-- The normal stress never exceeds the major principal stress: `σx'(θ) ≤ C + R`. -/
theorem sigmaX'_le : s.sigmaX' θ ≤ s.center + s.radius := by
  linarith [(abs_le.mp (s.abs_sigmaX'_sub_center_le θ)).2]

/-- The normal stress is never below the minor principal stress: `C - R ≤ σx'(θ)`. -/
theorem le_sigmaX' : s.center - s.radius ≤ s.sigmaX' θ := by
  linarith [(abs_le.mp (s.abs_sigmaX'_sub_center_le θ)).1]

/-- The **maximum in-plane shear** bound: `|τx'y'(θ)| ≤ R`. -/
theorem abs_tau'_le : |s.tau' θ| ≤ s.radius :=
  Real.abs_le_sqrt (by
    nlinarith [s.mohr_circle θ, s.radius_sq, sq_nonneg (s.sigmaX' θ - s.center)])

/-- The **principal angle** `θ_p = ½ arg ((σx - σy)/2 + i τxy)`, so that
`cos 2θ_p = ((σx - σy)/2)/R` and `sin 2θ_p = τxy/R`. -/
noncomputable def principalAngle : ℝ := Complex.arg ⟨(s.σx - s.σy) / 2, s.τxy⟩ / 2

/-- `R cos 2θ_p = (σx - σy)/2`. -/
theorem radius_mul_cos_principalAngle :
    s.radius * cos (2 * s.principalAngle) = (s.σx - s.σy) / 2 := by
  have h := Complex.norm_mul_cos_arg (⟨(s.σx - s.σy) / 2, s.τxy⟩ : ℂ)
  rw [Complex.norm_def, Complex.normSq_mk] at h
  simpa [principalAngle, radius, mul_div_cancel₀, sq] using h

/-- `R sin 2θ_p = τxy`. -/
theorem radius_mul_sin_principalAngle : s.radius * sin (2 * s.principalAngle) = s.τxy := by
  have h := Complex.norm_mul_sin_arg (⟨(s.σx - s.σy) / 2, s.τxy⟩ : ℂ)
  rw [Complex.norm_def, Complex.normSq_mk] at h
  simpa [principalAngle, radius, mul_div_cancel₀, sq] using h

/-- The principal angle satisfies `tan 2θ_p = 2τxy/(σx - σy)` (with Lean's conventions for
division by zero, this holds unconditionally). -/
theorem tan_two_principalAngle : tan (2 * s.principalAngle) = 2 * s.τxy / (s.σx - s.σy) := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  rw [tan_eq_sin_div_cos]
  rcases eq_or_ne s.radius 0 with h0 | h0
  · rw [h0, zero_mul] at hc hs
    have : s.σx - s.σy = 0 := by linarith
    rw [this, div_zero, div_eq_zero_iff]
    left
    have : (⟨(s.σx - s.σy) / 2, s.τxy⟩ : ℂ) = 0 := by
      apply Complex.ext <;> simp [this, ← hs]
    simp [principalAngle, this]
  · rw [show 2 * s.τxy / (s.σx - s.σy) = s.τxy / ((s.σx - s.σy) / 2) by field_simp, ← hc, ← hs,
      mul_div_mul_left _ _ h0]

/-- **Attainment of the major principal stress**: at the principal angle the normal stress is
`C + R` and the shear stress vanishes. -/
theorem principal_attained :
    s.sigmaX' s.principalAngle = s.center + s.radius ∧ s.tau' s.principalAngle = 0 := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  have h := sin_sq_add_cos_sq (2 * s.principalAngle)
  constructor
  · simp only [sigmaX', center, ← hc, ← hs]
    linear_combination s.radius * h
  · simp only [tau', ← hc, ← hs]
    ring

/-- **Attainment of the minor principal stress**: at `θ_p + π/2` the normal stress is `C - R`
and the shear stress vanishes. -/
theorem principal_attained_min :
    s.sigmaX' (s.principalAngle + π / 2) = s.center - s.radius ∧
      s.tau' (s.principalAngle + π / 2) = 0 := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  have h := sin_sq_add_cos_sq (2 * s.principalAngle)
  have e : 2 * (s.principalAngle + π / 2) = 2 * s.principalAngle + π := by ring
  constructor
  · simp only [sigmaX', center, e, cos_add_pi, sin_add_pi, ← hc, ← hs]
    linear_combination (-s.radius) * h
  · simp only [tau', e, cos_add_pi, sin_add_pi, ← hc, ← hs]
    ring

/-- The principal stresses `C ± R` are exactly the extreme values of the normal stress. -/
theorem isGreatest_sigmaX' : IsGreatest (Set.range s.sigmaX') (s.center + s.radius) :=
  ⟨⟨_, s.principal_attained.1⟩, by rintro _ ⟨θ, rfl⟩; exact s.sigmaX'_le θ⟩

/-- The minor principal stress `C - R` is the least value of the normal stress. -/
theorem isLeast_sigmaX' : IsLeast (Set.range s.sigmaX') (s.center - s.radius) :=
  ⟨⟨_, s.principal_attained_min.1⟩, by rintro _ ⟨θ, rfl⟩; exact s.le_sigmaX' θ⟩

/-- **Maximum in-plane shear** is attained at `θ_p + π/4`: `τx'y'(θ_p + π/4) = -R`. -/
theorem tau'_principalAngle_add : s.tau' (s.principalAngle + π / 4) = -s.radius := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  have h := sin_sq_add_cos_sq (2 * s.principalAngle)
  have e : 2 * (s.principalAngle + π / 4) = 2 * s.principalAngle + π / 2 := by ring
  simp only [tau', e, cos_add_pi_div_two, sin_add_pi_div_two, ← hc, ← hs]
  linear_combination (-s.radius) * h

/-- **Maximum in-plane shear** is attained at `θ_p - π/4`: `τx'y'(θ_p - π/4) = R`. -/
theorem tau'_principalAngle_sub : s.tau' (s.principalAngle - π / 4) = s.radius := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  have h := sin_sq_add_cos_sq (2 * s.principalAngle)
  have e : 2 * (s.principalAngle - π / 4) = 2 * s.principalAngle - π / 2 := by ring
  simp only [tau', e, cos_sub_pi_div_two, sin_sub_pi_div_two, ← hc, ← hs]
  linear_combination s.radius * h

/-- **Maximum in-plane shear** is attained at `θ_p ± π/4`: `|τx'y'(θ_p ± π/4)| = R`. -/
theorem maxShear_attained :
    |s.tau' (s.principalAngle + π / 4)| = s.radius ∧
      |s.tau' (s.principalAngle - π / 4)| = s.radius := by
  rw [tau'_principalAngle_add, tau'_principalAngle_sub, abs_neg, abs_of_nonneg s.radius_nonneg]
  exact ⟨rfl, rfl⟩

/-- The maximum in-plane shear is `R`, the greatest value of `|τx'y'|`. -/
theorem isGreatest_abs_tau' : IsGreatest (Set.range fun θ ↦ |s.tau' θ|) s.radius :=
  ⟨⟨_, s.maxShear_attained.2⟩, by rintro _ ⟨θ, rfl⟩; exact s.abs_tau'_le θ⟩

/-- **2D von Mises identity**: with `σ₁,₂ = C ± R`,
`σ₁² - σ₁σ₂ + σ₂² = σx² - σxσy + σy² + 3τxy²`. -/
theorem vonMises_principal :
    (s.center + s.radius) ^ 2 - (s.center + s.radius) * (s.center - s.radius) +
        (s.center - s.radius) ^ 2 = s.σx ^ 2 - s.σx * s.σy + s.σy ^ 2 + 3 * s.τxy ^ 2 := by
  have h := s.radius_sq
  simp only [center]
  linear_combination 3 * h

/-- **2D von Mises stress**: `√(σ₁² - σ₁σ₂ + σ₂²) = √(σx² - σxσy + σy² + 3τxy²)`. -/
theorem sqrt_vonMises_principal :
    √((s.center + s.radius) ^ 2 - (s.center + s.radius) * (s.center - s.radius) +
        (s.center - s.radius) ^ 2) = √(s.σx ^ 2 - s.σx * s.σy + s.σy ^ 2 + 3 * s.τxy ^ 2) := by
  rw [vonMises_principal]

end PlaneStress

end ContinuumMechanics
