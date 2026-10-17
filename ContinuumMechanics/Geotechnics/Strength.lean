import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import ContinuumMechanics.Stress.Mohr

/-!
# Soil strength: Mohr–Coulomb, Rankine earth pressures, slope stability, bearing capacity

**Sign convention.** As is customary in soil mechanics, normal stresses are taken
**positive in compression** throughout this file. The plane-stress transformation formulas of
`ContinuumMechanics.Stress.Mohr` are linear in the stress components, so they hold verbatim in
this convention; only the sign of the shear stress changes, and the criterion below only
involves `|τ|`.

**Mohr–Coulomb.** A soil with cohesion `c` and friction angle `φ` (`0 < φ < π/2`) fails on a
plane carrying normal stress `σ` and shear stress `τ` when `|τ| ≥ c + σ tan φ`. For a plane
stress state with Mohr's circle of centre `C` and radius `R` (principal stresses
`σ₁ = C + R ≥ σ₃ = C - R`), such a plane exists iff the circle reaches the failure line,
`R ≥ c cos φ + C sin φ`. At failure, `σ₁ = σ₃ tan²(π/4 + φ/2) + 2c tan(π/4 + φ/2)`, and the
failure plane makes the angle `θ_f = π/4 + φ/2` with the major principal plane.

**Rankine earth pressures.** `K_a = (1 - sin φ)/(1 + sin φ) = tan²(π/4 - φ/2)`,
`K_p = (1 + sin φ)/(1 - sin φ) = tan²(π/4 + φ/2) = 1/K_a`; active and passive pressures
`σ_a = K_a γ z - 2c√K_a`, `σ_p = K_p γ z + 2c√K_p`; the active thrust on a wall of height `H`
is `P_a = ½ K_a γ H² - 2c√K_a H`; the tension crack depth is `z_c = 2c/(γ√K_a)`.

**Infinite slope.** For a slice of an infinite slope inclined at `β`, at depth `z`, the stresses
on the slip plane are `σ = γ z cos²β`, `τ = γ z sin β cos β`, and the factor of safety is
`FS = (c + σ tan φ)/τ`.

**Bearing capacity.** The Prandtl–Reissner factors `N_q = e^{π tan φ} tan²(π/4 + φ/2)`,
`N_c = (N_q - 1) cot φ`, with Prandtl's undrained limit `N_c → π + 2`.

## Main results

* `PlaneStress.exists_failure_plane_iff`: some plane fails iff `c cos φ + C sin φ ≤ R`.
* `PlaneStress.failure_tangent`: at failure the circle is tangent to the failure line, which
  is reached on the plane `failureAngle` (`PlaneStress.failureAngle_failure`).
* `mohrCoulomb_principal_iff`: `R = c cos φ + C sin φ ↔
  σ₁ = σ₃ tan²(π/4 + φ/2) + 2c tan(π/4 + φ/2)`.
* `activeCoeff_eq_tan_sq`, `passiveCoeff_eq_tan_sq`, `activeCoeff_mul_passiveCoeff`,
  `activeCoeff_le_one`, `one_le_passiveCoeff`, `activeCoeff_le_atRestCoeff`,
  `atRestCoeff_le_passiveCoeff`.
* `activeThrust_eq`, `activeThrust_cohesionless`: `P_a = ½ K_a γ H²` for `c = 0`.
* `activePressure_tensionCrackDepth`, `active_state_failure`.
* `slopeFS_cohesionless`, `one_lt_slopeFS_iff`, `strictAntiOn_slopeFS`, `seepageFS_eq`.
* `one_le_bearingNq`, `strictMonoOn_bearingNq`, `tendsto_bearingNc`.

## References

* [Craig2004] R. F. Craig, *Craig's Soil Mechanics*, 7th ed., Ch. 4, 11, 9, 8.
* [Terzaghi1943] K. Terzaghi, *Theoretical Soil Mechanics*, Ch. II, VIII.
* [DasSobhan2014] B. M. Das, K. Sobhan, *Principles of Geotechnical Engineering*, Ch. 12–15.
-/

open Real Filter Topology

namespace ContinuumMechanics.Geotechnics

/-! ### Trigonometric identities -/

/-- The half-angle formula `tan t = (1 - cos 2t)/sin 2t` (unconditional with Lean's
conventions for division by zero). -/
theorem tan_eq_one_sub_cos_div_sin (t : ℝ) : tan t = (1 - cos (2 * t)) / sin (2 * t) := by
  rw [tan_eq_sin_div_cos, cos_two_mul, sin_two_mul]
  rcases eq_or_ne (cos t) 0 with hc | hc
  · simp [hc]
  rcases eq_or_ne (sin t) 0 with hs | hs
  · simp [hs]
  rw [div_eq_div_iff hc (by positivity)]
  linear_combination 2 * cos t * sin_sq_add_cos_sq t

/-- `tan (π/4 + φ/2) = (1 + sin φ)/cos φ`. -/
theorem tan_pi_div_four_add_half (φ : ℝ) : tan (π / 4 + φ / 2) = (1 + sin φ) / cos φ := by
  rw [tan_eq_one_sub_cos_div_sin, show 2 * (π / 4 + φ / 2) = φ + π / 2 by ring,
    cos_add_pi_div_two, sin_add_pi_div_two, sub_neg_eq_add]

/-- `tan (π/4 - φ/2) = (1 - sin φ)/cos φ`. -/
theorem tan_pi_div_four_sub_half (φ : ℝ) : tan (π / 4 - φ / 2) = (1 - sin φ) / cos φ := by
  rw [tan_eq_one_sub_cos_div_sin, show 2 * (π / 4 - φ / 2) = π / 2 - φ by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub]

/-- `((1 ± sin φ)/cos φ)² = (1 ± sin φ)/(1 ∓ sin φ)`, in the form `(a/cos φ)² = a/b` where
`cos² φ = a b`. -/
private theorem div_cos_sq {a b φ : ℝ} (h : cos φ ^ 2 = a * b) : (a / cos φ) ^ 2 = a / b := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  rw [div_pow, h, sq, mul_div_mul_left _ _ ha]

/-- For `|φ| < π/2`, `0 < cos φ`. -/
private theorem cos_pos' {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) : 0 < cos φ :=
  cos_pos_of_mem_Ioo ⟨h0, h1⟩

/-- For `|φ| < π/2`, `sin φ < 1`. -/
private theorem sin_lt_one' {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) : sin φ < 1 := by
  nlinarith [sin_sq_add_cos_sq φ, cos_pos' h0 h1, sin_le_one φ]

/-- For `|φ| < π/2`, `-1 < sin φ`. -/
private theorem neg_one_lt_sin' {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    -1 < sin φ := by
  nlinarith [sin_sq_add_cos_sq φ, cos_pos' h0 h1, neg_one_le_sin φ]

/-! ### Mohr–Coulomb failure criterion -/

/-- The **Mohr–Coulomb shear strength** `c + σ tan φ` of a plane carrying the (compressive)
normal stress `σ`. -/
noncomputable def shearStrength (c φ σ : ℝ) : ℝ := c + σ * tan φ

end ContinuumMechanics.Geotechnics

/-! The Mohr–Coulomb results for a plane stress state extend the namespace of
`ContinuumMechanics.PlaneStress`, so that they are available by dot notation. -/

namespace ContinuumMechanics.PlaneStress

open ContinuumMechanics.Geotechnics

variable (s : PlaneStress)

/-- The normal stress in terms of the angle from the principal direction:
`σx'(θ) = C + R cos 2(θ - θ_p)`. -/
theorem sigmaX'_eq (θ : ℝ) :
    s.sigmaX' θ = s.center + s.radius * cos (2 * (θ - s.principalAngle)) := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  rw [show 2 * (θ - s.principalAngle) = 2 * θ - 2 * s.principalAngle by ring, cos_sub]
  simp only [sigmaX', center]
  linear_combination (-cos (2 * θ)) * hc + (-sin (2 * θ)) * hs

/-- The shear stress in terms of the angle from the principal direction:
`τx'y'(θ) = -R sin 2(θ - θ_p)`. -/
theorem tau'_eq (θ : ℝ) : s.tau' θ = -(s.radius * sin (2 * (θ - s.principalAngle))) := by
  have hc := s.radius_mul_cos_principalAngle
  have hs := s.radius_mul_sin_principalAngle
  rw [show 2 * (θ - s.principalAngle) = 2 * θ - 2 * s.principalAngle by ring, sin_sub]
  simp only [tau']
  linear_combination sin (2 * θ) * hc + (-cos (2 * θ)) * hs

/-- The **distance bound** from the centre of Mohr's circle to a line of slope `tan φ`:
`|τ| cos φ - (σ - C) sin φ ≤ R` on every plane (Cauchy–Schwarz). -/
theorem abs_tau'_mul_cos_sub_le (θ φ : ℝ) :
    |s.tau' θ| * cos φ - (s.sigmaX' θ - s.center) * sin φ ≤ s.radius := by
  have hcirc := s.mohr_circle θ
  rw [← sq_abs (s.tau' θ)] at hcirc
  set a := |s.tau' θ|
  set u := s.sigmaX' θ - s.center
  have hR := s.radius_nonneg
  have hsc := sin_sq_add_cos_sq φ
  have hx : (a * cos φ - u * sin φ) ^ 2 ≤ s.radius ^ 2 := by
    nlinarith [sq_nonneg (a * sin φ + u * cos φ)]
  exact (abs_le_of_sq_le_sq' hx hR).2

/-- The **failure plane**: the plane at angle `θ_f = π/4 + φ/2` from the major principal plane,
`θ = θ_p - (π/4 + φ/2)`. -/
noncomputable def failureAngle (φ : ℝ) : ℝ := s.principalAngle - (π / 4 + φ / 2)

/-- The failure plane makes the angle `π/4 + φ/2` with the major principal plane. -/
theorem principalAngle_sub_failureAngle (φ : ℝ) :
    s.principalAngle - s.failureAngle φ = π / 4 + φ / 2 := by
  simp only [failureAngle]
  ring

/-- On the failure plane, `σ = C - R sin φ` and `τ = R cos φ`: the point of Mohr's circle at
which the tangent has slope `tan φ`. -/
theorem failureAngle_stress (φ : ℝ) :
    s.sigmaX' (s.failureAngle φ) = s.center - s.radius * sin φ ∧
      s.tau' (s.failureAngle φ) = s.radius * cos φ := by
  have e : 2 * (s.failureAngle φ - s.principalAngle) = -(φ + π / 2) := by
    simp only [failureAngle]
    ring
  rw [sigmaX'_eq, tau'_eq, e, cos_neg, sin_neg, cos_add_pi_div_two, sin_add_pi_div_two]
  constructor <;> ring

/-- If the circle reaches the failure line, `c cos φ + C sin φ ≤ R`, the strength is exceeded
on the failure plane: `c + σ tan φ ≤ |τ|` at `θ_p - (π/4 + φ/2)`. -/
theorem shearStrength_failureAngle_le {c φ : ℝ} (hφ0 : 0 < φ) (hφ : φ < π / 2)
    (h : c * cos φ + s.center * sin φ ≤ s.radius) :
    shearStrength c φ (s.sigmaX' (s.failureAngle φ)) ≤ |s.tau' (s.failureAngle φ)| := by
  have hcos : 0 < cos φ := cos_pos' (by linarith) hφ
  obtain ⟨hσ, hτ⟩ := s.failureAngle_stress φ
  rw [hσ, hτ, abs_of_nonneg (mul_nonneg s.radius_nonneg hcos.le), shearStrength,
    tan_eq_sin_div_cos,
    show c + (s.center - s.radius * sin φ) * (sin φ / cos φ) =
      (c * cos φ + s.center * sin φ - s.radius * sin φ ^ 2) / cos φ by field_simp; ring,
    div_le_iff₀ hcos]
  have h' : s.radius * (sin φ ^ 2 + cos φ ^ 2) = s.radius := by rw [sin_sq_add_cos_sq, mul_one]
  nlinarith [h']

/-- `(c + σ tan φ) cos φ = c cos φ + σ sin φ` for `cos φ ≠ 0`. -/
private theorem shearStrength_mul_cos {c φ σ : ℝ} (hcos : cos φ ≠ 0) :
    shearStrength c φ σ * cos φ = c * cos φ + σ * sin φ := by
  rw [shearStrength, add_mul, mul_assoc, tan_mul_cos hcos]

/-- **Mohr–Coulomb criterion for a plane stress state**: for `0 < φ < π/2`, some plane satisfies
`|τ| ≥ c + σ tan φ` iff Mohr's circle reaches the failure line, `c cos φ + C sin φ ≤ R`. -/
theorem exists_failure_plane_iff {c φ : ℝ} (hφ0 : 0 < φ) (hφ : φ < π / 2) :
    (∃ θ, shearStrength c φ (s.sigmaX' θ) ≤ |s.tau' θ|) ↔
      c * cos φ + s.center * sin φ ≤ s.radius := by
  have hcos : 0 < cos φ := cos_pos' (by linarith) hφ
  constructor
  · rintro ⟨θ, hθ⟩
    have key := s.abs_tau'_mul_cos_sub_le θ φ
    have h1 := shearStrength_mul_cos (c := c) (σ := s.sigmaX' θ) hcos.ne'
    have h2 := mul_le_mul_of_nonneg_right hθ hcos.le
    nlinarith
  · exact fun h ↦ ⟨_, s.shearStrength_failureAngle_le hφ0 hφ h⟩

/-- **Tangency at failure**: if `R = c cos φ + C sin φ`, no plane exceeds the strength:
`|τ| ≤ c + σ tan φ` on every plane. -/
theorem failure_tangent {c φ : ℝ} (hφ : φ < π / 2) (hφ0 : 0 < φ)
    (hR : s.radius = c * cos φ + s.center * sin φ) (θ : ℝ) :
    |s.tau' θ| ≤ shearStrength c φ (s.sigmaX' θ) := by
  have hcos : 0 < cos φ := cos_pos' (by linarith) hφ
  have key := s.abs_tau'_mul_cos_sub_le θ φ
  refine le_of_mul_le_mul_right ?_ hcos
  rw [shearStrength_mul_cos hcos.ne']
  linarith

/-- At failure, the Mohr–Coulomb strength is attained exactly on the failure plane
`θ_f = π/4 + φ/2` from the major principal plane: `|τ| = c + σ tan φ` there. -/
theorem failureAngle_failure {c φ : ℝ} (hφ0 : 0 < φ) (hφ : φ < π / 2)
    (hR : s.radius = c * cos φ + s.center * sin φ) :
    |s.tau' (s.failureAngle φ)| = shearStrength c φ (s.sigmaX' (s.failureAngle φ)) :=
  le_antisymm (s.failure_tangent hφ hφ0 hR _) (s.shearStrength_failureAngle_le hφ0 hφ hR.ge)

end ContinuumMechanics.PlaneStress

namespace ContinuumMechanics.Geotechnics

/-- **Mohr–Coulomb in principal stresses**: with `σ₁ ≥ σ₃` and `|φ| < π/2`, the circle
`C = (σ₁ + σ₃)/2`, `R = (σ₁ - σ₃)/2` touches the failure line iff
`σ₁ = σ₃ tan²(π/4 + φ/2) + 2c tan(π/4 + φ/2)`. -/
theorem mohrCoulomb_principal_iff {σ₁ σ₃ c φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    (σ₁ - σ₃) / 2 = c * cos φ + (σ₁ + σ₃) / 2 * sin φ ↔
      σ₁ = σ₃ * tan (π / 4 + φ / 2) ^ 2 + 2 * c * tan (π / 4 + φ / 2) := by
  have hcos := cos_pos' h0 h1
  have hs1 := sin_lt_one' h0 h1
  have hs2 := neg_one_lt_sin' h0 h1
  have hsc := sin_sq_add_cos_sq φ
  rw [tan_pi_div_four_add_half,
    show σ₃ * ((1 + sin φ) / cos φ) ^ 2 + 2 * c * ((1 + sin φ) / cos φ) =
      (σ₃ * (1 + sin φ) + 2 * c * cos φ) * (1 + sin φ) / cos φ ^ 2 by field_simp,
    eq_div_iff (by positivity), show cos φ ^ 2 = (1 - sin φ) * (1 + sin φ) by linarith,
    ← mul_assoc, mul_left_inj' (by linarith)]
  constructor <;> intro h <;> linarith

/-! ### Rankine earth pressure coefficients -/

/-- Rankine's **active earth pressure coefficient** `K_a = (1 - sin φ)/(1 + sin φ)`. -/
noncomputable def activeCoeff (φ : ℝ) : ℝ := (1 - sin φ) / (1 + sin φ)

/-- Rankine's **passive earth pressure coefficient** `K_p = (1 + sin φ)/(1 - sin φ)`. -/
noncomputable def passiveCoeff (φ : ℝ) : ℝ := (1 + sin φ) / (1 - sin φ)

/-- Jaky's **coefficient of earth pressure at rest** `K₀ = 1 - sin φ`. -/
noncomputable def atRestCoeff (φ : ℝ) : ℝ := 1 - sin φ

/-- `K_a = tan²(π/4 - φ/2)`. -/
theorem activeCoeff_eq_tan_sq (φ : ℝ) : activeCoeff φ = tan (π / 4 - φ / 2) ^ 2 := by
  rw [tan_pi_div_four_sub_half,
    div_cos_sq (a := 1 - sin φ) (b := 1 + sin φ) (by linear_combination sin_sq_add_cos_sq φ),
    activeCoeff]

/-- `K_p = tan²(π/4 + φ/2)`. -/
theorem passiveCoeff_eq_tan_sq (φ : ℝ) : passiveCoeff φ = tan (π / 4 + φ / 2) ^ 2 := by
  rw [tan_pi_div_four_add_half,
    div_cos_sq (a := 1 + sin φ) (b := 1 - sin φ) (by linear_combination sin_sq_add_cos_sq φ),
    passiveCoeff]

/-- `K_p = 1/K_a`. -/
theorem passiveCoeff_eq_inv (φ : ℝ) : passiveCoeff φ = 1 / activeCoeff φ := by
  rw [passiveCoeff, activeCoeff, one_div_div]

/-- For `|φ| < π/2`, `K_a K_p = 1`. -/
theorem activeCoeff_mul_passiveCoeff {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    activeCoeff φ * passiveCoeff φ = 1 := by
  have := sin_lt_one' h0 h1
  have := neg_one_lt_sin' h0 h1
  rw [activeCoeff, passiveCoeff, div_mul_div_comm, mul_comm (1 - sin φ),
    div_self (by nlinarith)]

/-- For `|φ| < π/2`, `0 < K_a`. -/
theorem activeCoeff_pos {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) : 0 < activeCoeff φ := by
  have := sin_lt_one' h0 h1
  have := neg_one_lt_sin' h0 h1
  exact div_pos (by linarith) (by linarith)

/-- For `|φ| < π/2`, `0 < K_p`. -/
theorem passiveCoeff_pos {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    0 < passiveCoeff φ := by
  have := sin_lt_one' h0 h1
  have := neg_one_lt_sin' h0 h1
  exact div_pos (by linarith) (by linarith)

/-- For `0 ≤ φ < π/2`, `K_a ≤ 1`. -/
theorem activeCoeff_le_one {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) : activeCoeff φ ≤ 1 := by
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  rw [activeCoeff, div_le_one (by linarith)]
  linarith

/-- For `0 ≤ φ < π/2`, `1 ≤ K_p`. -/
theorem one_le_passiveCoeff {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) : 1 ≤ passiveCoeff φ := by
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  rw [passiveCoeff, le_div_iff₀ (by linarith [sin_lt_one' (by linarith [pi_pos]) h1])]
  linarith

/-- For `0 ≤ φ < π/2`, Jaky's at-rest coefficient exceeds the active one: `K_a ≤ K₀`. -/
theorem activeCoeff_le_atRestCoeff {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) :
    activeCoeff φ ≤ atRestCoeff φ := by
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  have hs1 := sin_lt_one' (by linarith [pi_pos]) h1
  rw [activeCoeff, atRestCoeff, div_le_iff₀ (by linarith)]
  nlinarith

/-- For `0 ≤ φ < π/2`, Jaky's at-rest coefficient is below the passive one: `K₀ ≤ K_p`. -/
theorem atRestCoeff_le_passiveCoeff {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) :
    atRestCoeff φ ≤ passiveCoeff φ := by
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  linarith [one_le_passiveCoeff h0 h1, show atRestCoeff φ ≤ 1 by rw [atRestCoeff]; linarith]

/-- For `|φ| < π/2`, `√K_a = tan(π/4 - φ/2)`. -/
theorem sqrt_activeCoeff {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    √(activeCoeff φ) = tan (π / 4 - φ / 2) := by
  rw [activeCoeff_eq_tan_sq, sqrt_sq]
  rw [tan_pi_div_four_sub_half]
  exact div_nonneg (by linarith [sin_lt_one' h0 h1]) (cos_pos' h0 h1).le

/-- For `|φ| < π/2`, `√K_p = tan(π/4 + φ/2)`. -/
theorem sqrt_passiveCoeff {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    √(passiveCoeff φ) = tan (π / 4 + φ / 2) := by
  rw [passiveCoeff_eq_tan_sq, sqrt_sq]
  rw [tan_pi_div_four_add_half]
  exact div_nonneg (by linarith [neg_one_lt_sin' h0 h1]) (cos_pos' h0 h1).le

/-- The Mohr–Coulomb principal-stress relation in terms of `K_p`: for `|φ| < π/2`,
`R = c cos φ + C sin φ ↔ σ₁ = K_p σ₃ + 2c√K_p`. -/
theorem mohrCoulomb_principal_iff_passiveCoeff {σ₁ σ₃ c φ : ℝ} (h0 : -(π / 2) < φ)
    (h1 : φ < π / 2) :
    (σ₁ - σ₃) / 2 = c * cos φ + (σ₁ + σ₃) / 2 * sin φ ↔
      σ₁ = σ₃ * passiveCoeff φ + 2 * c * √(passiveCoeff φ) := by
  rw [mohrCoulomb_principal_iff h0 h1, passiveCoeff_eq_tan_sq, ← passiveCoeff_eq_tan_sq,
    sqrt_passiveCoeff h0 h1]

/-! ### Rankine active and passive pressures -/

/-- Rankine's **active earth pressure** at depth `z` in a soil of unit weight `γ`:
`σ_a(z) = K_a γ z - 2c√K_a`. -/
noncomputable def activePressure (c φ γ z : ℝ) : ℝ :=
  activeCoeff φ * γ * z - 2 * c * √(activeCoeff φ)

/-- Rankine's **passive earth pressure** at depth `z`: `σ_p(z) = K_p γ z + 2c√K_p`. -/
noncomputable def passivePressure (c φ γ z : ℝ) : ℝ :=
  passiveCoeff φ * γ * z + 2 * c * √(passiveCoeff φ)

/-- The **total active thrust** `P_a = ∫₀^H σ_a(z) dz` on a smooth vertical wall of height
`H`. -/
noncomputable def activeThrust (c φ γ H : ℝ) : ℝ := ∫ z in (0)..H, activePressure c φ γ z

/-- The **tension crack depth** `z_c = 2c/(γ√K_a)`, where the active pressure vanishes. -/
noncomputable def tensionCrackDepth (c φ γ : ℝ) : ℝ := 2 * c / (γ * √(activeCoeff φ))

/-- `P_a = ½ K_a γ H² - 2c√K_a H`. -/
theorem activeThrust_eq (c φ γ H : ℝ) :
    activeThrust c φ γ H = activeCoeff φ * γ * H ^ 2 / 2 - 2 * c * √(activeCoeff φ) * H := by
  simp only [activeThrust, activePressure]
  rw [intervalIntegral.integral_sub (f := fun z ↦ activeCoeff φ * γ * z)
    (g := fun _ ↦ 2 * c * √(activeCoeff φ))
    (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- **Active thrust of a cohesionless backfill**: `P_a = ½ K_a γ H²`. -/
theorem activeThrust_cohesionless (φ γ H : ℝ) :
    activeThrust 0 φ γ H = activeCoeff φ * γ * H ^ 2 / 2 := by
  rw [activeThrust_eq]
  ring

/-- The active pressure vanishes at the tension crack depth (for `γ > 0`, `|φ| < π/2`). -/
theorem activePressure_tensionCrackDepth {c φ γ : ℝ} (hγ : 0 < γ) (h0 : -(π / 2) < φ)
    (h1 : φ < π / 2) : activePressure c φ γ (tensionCrackDepth c φ γ) = 0 := by
  have hK := activeCoeff_pos h0 h1
  have hs : 0 < √(activeCoeff φ) := sqrt_pos.2 hK
  have hss : √(activeCoeff φ) ^ 2 = activeCoeff φ := sq_sqrt hK.le
  rw [activePressure, tensionCrackDepth]
  field_simp
  rw [hss]
  ring

/-- The **Rankine active state is a Mohr–Coulomb failure state**: with major principal stress
`σ₁ = γ z` (vertical) and minor principal stress `σ₃ = σ_a(z)` (horizontal), the failure
relation `σ₁ = K_p σ₃ + 2c√K_p` holds. -/
theorem active_state_failure {c φ γ z : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    γ * z = activePressure c φ γ z * passiveCoeff φ + 2 * c * √(passiveCoeff φ) := by
  have hKa := activeCoeff_pos h0 h1
  have hKp := passiveCoeff_pos h0 h1
  have hm := activeCoeff_mul_passiveCoeff h0 h1
  have hsp : √(activeCoeff φ) * √(passiveCoeff φ) = 1 := by
    rw [← sqrt_mul hKa.le, hm, sqrt_one]
  have hp : √(passiveCoeff φ) ^ 2 = passiveCoeff φ := sq_sqrt hKp.le
  rw [activePressure]
  linear_combination (-(γ * z)) * hm - 2 * c * √(activeCoeff φ) * hp +
    2 * c * √(passiveCoeff φ) * hsp

/-- The **Rankine passive state is a Mohr–Coulomb failure state**: with minor principal stress
`σ₃ = γ z` and major principal stress `σ₁ = σ_p(z)`, `σ₁ = K_p σ₃ + 2c√K_p`. -/
theorem passive_state_failure (c φ γ z : ℝ) :
    passivePressure c φ γ z = γ * z * passiveCoeff φ + 2 * c * √(passiveCoeff φ) := by
  rw [passivePressure]
  ring

/-! ### Infinite slope stability -/

/-- The weight `W = γ z b` of a vertical slice of horizontal width `b` and depth `z`. -/
def sliceWeight (γ z b : ℝ) : ℝ := γ * z * b

/-- The length `L = b / cos β` of the base of the slice along the slip plane. -/
noncomputable def slipLength (b β : ℝ) : ℝ := b / cos β

/-- The **normal force** `N = W cos β` on the base of the slice (equilibrium normal to the
slope; the side forces of an infinite slope cancel). -/
noncomputable def sliceNormalForce (γ z b β : ℝ) : ℝ := sliceWeight γ z b * cos β

/-- The **shear force** `T = W sin β` on the base of the slice (equilibrium along the
slope). -/
noncomputable def sliceShearForce (γ z b β : ℝ) : ℝ := sliceWeight γ z b * sin β

/-- The normal stress on the slip plane at depth `z`: `σ = γ z cos²β`. -/
noncomputable def slopeNormalStress (γ z β : ℝ) : ℝ := γ * z * cos β ^ 2

/-- The shear stress on the slip plane at depth `z`: `τ = γ z sin β cos β`. -/
noncomputable def slopeShearStress (γ z β : ℝ) : ℝ := γ * z * sin β * cos β

/-- The slip-plane normal stress is the normal force per unit base length: `σ = N / L`. -/
theorem sliceNormalForce_div {γ z b β : ℝ} (hb : b ≠ 0) (hβ : cos β ≠ 0) :
    sliceNormalForce γ z b β / slipLength b β = slopeNormalStress γ z β := by
  simp only [sliceNormalForce, sliceWeight, slipLength, slopeNormalStress]
  field_simp

/-- The slip-plane shear stress is the shear force per unit base length: `τ = T / L`. -/
theorem sliceShearForce_div {γ z b β : ℝ} (hb : b ≠ 0) (hβ : cos β ≠ 0) :
    sliceShearForce γ z b β / slipLength b β = slopeShearStress γ z β := by
  simp only [sliceShearForce, sliceWeight, slipLength, slopeShearStress]
  field_simp

/-- The **factor of safety** of an infinite slope: available strength over mobilized shear,
`FS = (c + σ tan φ)/τ`. -/
noncomputable def slopeFS (c φ γ z β : ℝ) : ℝ :=
  shearStrength c φ (slopeNormalStress γ z β) / slopeShearStress γ z β

/-- `FS = (c + γ z cos²β tan φ)/(γ z sin β cos β)`. -/
theorem slopeFS_eq (c φ γ z β : ℝ) :
    slopeFS c φ γ z β = (c + γ * z * cos β ^ 2 * tan φ) / (γ * z * sin β * cos β) := rfl

/-- **Dry cohesionless infinite slope**: `FS = tan φ / tan β`, independent of depth. -/
theorem slopeFS_cohesionless {φ γ z β : ℝ} (hγz : γ * z ≠ 0) (hβ0 : 0 < β) (hβ : β < π / 2) :
    slopeFS 0 φ γ z β = tan φ / tan β := by
  have hc : cos β ≠ 0 := (cos_pos' (by linarith) hβ).ne'
  have hs : sin β ≠ 0 := (sin_pos_of_pos_of_lt_pi hβ0 (by linarith [pi_pos])).ne'
  obtain ⟨hγ, hz⟩ := mul_ne_zero_iff.mp hγz
  rw [slopeFS_eq, zero_add, tan_eq_sin_div_cos β]
  field_simp

/-- **Stability of a dry cohesionless slope**: `FS > 1` iff `β < φ`. -/
theorem one_lt_slopeFS_iff {φ γ z β : ℝ} (hγz : γ * z ≠ 0) (hβ0 : 0 < β) (hβ : β < π / 2)
    (hφ0 : 0 < φ) (hφ : φ < π / 2) : 1 < slopeFS 0 φ γ z β ↔ β < φ := by
  rw [slopeFS_cohesionless hγz hβ0 hβ, one_lt_div (tan_pos_of_pos_of_lt_pi_div_two hβ0 hβ)]
  exact strictMonoOn_tan.lt_iff_lt ⟨by linarith, hβ⟩ ⟨by linarith, hφ⟩

/-- **Monotonicity**: the factor of safety `tan φ / tan β` of a dry cohesionless slope strictly
decreases with the slope angle on `(0, π/2)`. -/
theorem strictAntiOn_slopeFS {φ γ z : ℝ} (hγz : γ * z ≠ 0) (hφ0 : 0 < φ) (hφ : φ < π / 2) :
    StrictAntiOn (fun β ↦ slopeFS 0 φ γ z β) (Set.Ioo 0 (π / 2)) := by
  intro a ⟨ha0, ha⟩ b ⟨hb0, hb⟩ hab
  simp only
  rw [slopeFS_cohesionless hγz ha0 ha, slopeFS_cohesionless hγz hb0 hb]
  exact div_lt_div_of_pos_left (tan_pos_of_pos_of_lt_pi_div_two hφ0 hφ)
    (tan_pos_of_pos_of_lt_pi_div_two ha0 ha)
    (strictMonoOn_tan ⟨by linarith, ha⟩ ⟨by linarith, hb⟩ hab)

/-- The **pore water pressure** on the slip plane for seepage parallel to the slope with the
water table at the surface: `u = γ_w z cos²β`. -/
noncomputable def seepagePorePressure (γw z β : ℝ) : ℝ := γw * z * cos β ^ 2

/-- The factor of safety of a slope with seepage parallel to the surface: the strength uses
the effective normal stress `σ' = σ - u` (with saturated unit weight `γ_sat`), the driving
shear stress is `γ_sat z sin β cos β`. -/
noncomputable def seepageFS (c φ γsat γw z β : ℝ) : ℝ :=
  shearStrength c φ (slopeNormalStress γsat z β - seepagePorePressure γw z β) /
    slopeShearStress γsat z β

/-- The effective normal stress is computed with the buoyant unit weight `γ' = γ_sat - γ_w`. -/
theorem slopeNormalStress_sub_seepagePorePressure (γsat γw z β : ℝ) :
    slopeNormalStress γsat z β - seepagePorePressure γw z β =
      slopeNormalStress (γsat - γw) z β := by
  simp only [slopeNormalStress, seepagePorePressure]
  ring

/-- **Cohesionless slope with parallel seepage**: `FS = (γ'/γ_sat) tan φ / tan β`,
with `γ' = γ_sat - γ_w`. -/
theorem seepageFS_eq {φ γsat γw z β : ℝ} (hγ : γsat ≠ 0) (hz : z ≠ 0) (hβ0 : 0 < β)
    (hβ : β < π / 2) :
    seepageFS 0 φ γsat γw z β = (γsat - γw) / γsat * (tan φ / tan β) := by
  have hc : cos β ≠ 0 := (cos_pos' (by linarith) hβ).ne'
  have hs : sin β ≠ 0 := (sin_pos_of_pos_of_lt_pi hβ0 (by linarith [pi_pos])).ne'
  rw [seepageFS, slopeNormalStress_sub_seepagePorePressure, tan_eq_sin_div_cos β]
  simp only [shearStrength, slopeNormalStress, slopeShearStress, zero_add]
  field_simp

/-! ### Bearing capacity factors -/

/-- The Prandtl–Reissner **bearing capacity factor** `N_q = e^{π tan φ} K_p`,
i.e. `e^{π tan φ} tan²(π/4 + φ/2)` (`bearingNq_eq`). -/
noncomputable def bearingNq (φ : ℝ) : ℝ := exp (π * tan φ) * passiveCoeff φ

/-- Prandtl's **bearing capacity factor** `N_c = (N_q - 1) cot φ` (`bearingNc_eq_cot`). -/
noncomputable def bearingNc (φ : ℝ) : ℝ := (bearingNq φ - 1) / tan φ

/-- Vesić's **bearing capacity factor** `N_γ = 2 (N_q + 1) tan φ`. -/
noncomputable def bearingNγ (φ : ℝ) : ℝ := 2 * (bearingNq φ + 1) * tan φ

/-- Terzaghi's **ultimate bearing capacity** of a strip footing of width `B` with surcharge
`q`: `q_ult = c N_c + q N_q + ½ γ B N_γ`, for given factors `N_c, N_q, N_γ`. -/
noncomputable def ultimateBearing (c q γ B Nc Nq Nγ : ℝ) : ℝ := c * Nc + q * Nq + γ * B * Nγ / 2

/-- `N_q = e^{π tan φ} tan²(π/4 + φ/2)`. -/
theorem bearingNq_eq (φ : ℝ) : bearingNq φ = exp (π * tan φ) * tan (π / 4 + φ / 2) ^ 2 := by
  rw [bearingNq, passiveCoeff_eq_tan_sq]

/-- `N_c = (N_q - 1) cot φ`. -/
theorem bearingNc_eq_cot (φ : ℝ) : bearingNc φ = (bearingNq φ - 1) * cot φ := by
  rw [bearingNc, cot_eq_cos_div_sin, tan_eq_sin_div_cos, div_div_eq_mul_div, mul_div_assoc]

/-- `N_q(0) = 1`. -/
theorem bearingNq_zero : bearingNq 0 = 1 := by
  simp [bearingNq, passiveCoeff]

/-- For `0 ≤ φ < π/2`, `1 ≤ N_q`. -/
theorem one_le_bearingNq {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < π / 2) : 1 ≤ bearingNq φ :=
  one_le_mul_of_one_le_of_one_le
    (one_le_exp (mul_nonneg pi_pos.le (tan_nonneg_of_nonneg_of_le_pi_div_two h0 h1.le)))
    (one_le_passiveCoeff h0 h1)

/-- `K_p` is strictly increasing on `(-π/2, π/2)`. -/
theorem strictMonoOn_passiveCoeff : StrictMonoOn passiveCoeff (Set.Ioo (-(π / 2)) (π / 2)) := by
  intro a ⟨ha0, ha⟩ b ⟨hb0, hb⟩ hab
  have hs : sin a < sin b := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hb.le hab
  have ha1 := sin_lt_one' ha0 ha
  have hb1 := sin_lt_one' hb0 hb
  have ha2 := neg_one_lt_sin' ha0 ha
  rw [passiveCoeff, passiveCoeff, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `N_q` is strictly increasing in `φ` on `[0, π/2)`. -/
theorem strictMonoOn_bearingNq : StrictMonoOn bearingNq (Set.Ico 0 (π / 2)) := by
  intro a ⟨ha0, ha⟩ b ⟨hb0, hb⟩ hab
  have hpi := pi_pos
  have htan : tan a < tan b := strictMonoOn_tan ⟨by linarith, ha⟩ ⟨by linarith, hb⟩ hab
  exact mul_lt_mul' (exp_le_exp.2 (by nlinarith))
    (strictMonoOn_passiveCoeff ⟨by linarith, ha⟩ ⟨by linarith, hb⟩ hab)
    (passiveCoeff_pos (by linarith) ha).le (exp_pos _)

/-- The derivative of `N_q` at `φ = 0` is `π + 2`. -/
theorem hasDerivAt_bearingNq_zero : HasDerivAt bearingNq (π + 2) 0 := by
  have htan : HasDerivAt tan 1 0 := by
    simpa using hasDerivAt_tan (x := 0) (by simp)
  have hexp : HasDerivAt (fun φ ↦ exp (π * tan φ)) (exp (π * tan 0) * (π * 1)) 0 :=
    (htan.const_mul π).exp
  have hKp : HasDerivAt passiveCoeff
      ((cos 0 * (1 - sin 0) - (1 + sin 0) * (-cos 0)) / (1 - sin 0) ^ 2) 0 := by
    have h1 := (hasDerivAt_sin 0).const_add 1
    have h2 := (hasDerivAt_sin 0).const_sub 1
    exact h1.div h2 (by simp)
  have := hexp.mul hKp
  rw [show bearingNq = (fun φ ↦ exp (π * tan φ)) * passiveCoeff from rfl]
  convert this using 1
  norm_num [passiveCoeff]

/-- **Prandtl's undrained bearing capacity factor**: `N_c → π + 2` as `φ → 0⁺`. -/
theorem tendsto_bearingNc : Tendsto bearingNc (𝓝[>] 0) (𝓝 (π + 2)) := by
  have htan : HasDerivAt tan 1 0 := by
    simpa using hasDerivAt_tan (x := 0) (by simp)
  have h := hasDerivAt_bearingNq_zero.tendsto_slope_zero_right.div
    htan.tendsto_slope_zero_right one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Pi.div_apply, zero_add, smul_eq_mul, bearingNq_zero, tan_zero, sub_zero, bearingNc]
  rw [mul_div_mul_left _ _ (inv_ne_zero ht.ne')]

end ContinuumMechanics.Geotechnics
