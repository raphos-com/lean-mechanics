import ClassicalMechanics.Oscillator

/-!
# The Foucault pendulum

A pendulum of length `ℓ` at latitude `φ` on the Earth, which rotates with angular speed `Ω`.
We use local axes `e₁` (east), `e₂` (north), `e₃` (up); in these axes the Earth's angular
velocity is `w = Ω (0, cos φ, sin φ)`. For small amplitudes the bob moves in the horizontal
plane, at `(x, y)`; neglecting the centrifugal force (absorbed in the effective gravity) and the
vertical motion, the restoring force is `-ω₀² (x, y)` with `ω₀² = g/ℓ`, and the Coriolis
acceleration `-2 w × v` of `RotatingFrame` contributes its horizontal part only
(`coriolis_horizontal`: for horizontal `v = (ẋ, ẏ, 0)` this part is `(2 Ω_z ẏ, -2 Ω_z ẋ)`, with
`Ω_z = Ω sin φ`). The equations of motion are therefore

`ẍ - 2 Ω_z ẏ + ω₀² x = 0`,  `ÿ + 2 Ω_z ẋ + ω₀² y = 0`

([Goldstein2002], §4.10; [Landau1976], §39, problem 3; [Arnold1989], §27). Below `k = ω₀²`.

* `complex_iff` : in complex form `z = x + i y` they read `z̈ + 2 i Ω_z ż + ω₀² z = 0`
  (`Foucault.complex_eq`).
* **Precession** (`solves_of_pendulum`, `pendulum_of_solves`): `z(t) = e^{-i Ω_z t} ζ(t)` solves
  the Foucault equation iff `ζ` solves the non-rotating pendulum `ζ̈ + ω² ζ = 0` with
  `ω² = ω₀² + Ω_z²`. A planar oscillation `ζ(t) ∈ ℝ u` is thus carried by the rotation
  `e^{-i Ω_z t}`: its plane precesses with angular velocity `-Ω_z = -Ω sin φ`, clockwise (seen
  from above) in the northern hemisphere (`planar_precesses`).
* **Explicit solutions** (`explicit_solves`, `explicit_re`, `explicit_im`, `explicit_real`):
  `z(t) = e^{-i Ω_z t} (A cos ωt + B sin ωt)`; e.g. `x = a cos(Ω_z t) cos ωt`,
  `y = -a sin(Ω_z t) cos ωt`.
* **Precession period** (`precessionPeriod`, `rotation_periodic`): `T = 2π / (Ω |sin φ|)`; at the
  poles it is the sidereal day `2π/Ω` (`precessionPeriod_pole`); at the equator `Ω_z = 0`, there
  is no precession and the equations decouple into two harmonic oscillators
  (`equator_decouple`).
* **Conservation laws**: the angular-momentum-like quantity `x ẏ - y ẋ + Ω_z (x² + y²)`
  (`Foucault.angMom_const`) and the energy `½ (ẋ² + ẏ²) + ½ ω₀² (x² + y²)`
  (`Foucault.energy_const`; the Coriolis force does no work).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §4.10.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §39.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §27.
-/

open Complex Matrix

open scoped Real

noncomputable section

namespace ClassicalMechanics

namespace Foucault

/-! ### The Coriolis force on a horizontal velocity -/

/-- The Earth's angular velocity `Ω (0, cos φ, sin φ)` in local (east, north, up) axes at
latitude `φ`. -/
def earthOmega (Ω φ : ℝ) : Vec := ![0, Ω * Real.cos φ, Ω * Real.sin φ]

/-- **Horizontal Coriolis acceleration**: for a horizontal velocity `v = (ẋ, ẏ, 0)`,
`-2 w × v = (2 Ω sin φ ẏ, -2 Ω sin φ ẋ, 2 Ω cos φ ẋ)`; its horizontal part is
`(2 Ω_z ẏ, -2 Ω_z ẋ)` with `Ω_z = Ω sin φ`. -/
theorem coriolis_horizontal (Ω φ vx vy : ℝ) :
    -((2 : ℝ) • (earthOmega Ω φ ⨯₃ ![vx, vy, 0])) =
      ![2 * (Ω * Real.sin φ) * vy, -(2 * (Ω * Real.sin φ) * vx), 2 * (Ω * Real.cos φ) * vx] := by
  ext i
  fin_cases i <;> simp [earthOmega, cross_apply] <;> ring

/-! ### Complex form -/

/-- The Foucault equations `a_x - 2 Ω_z v_y + k x = 0`, `a_y + 2 Ω_z v_x + k y = 0` are the real
and imaginary parts of `a + 2 i Ω_z v + k z = 0`, with `z = x + i y`, `v = v_x + i v_y`,
`a = a_x + i a_y`. -/
theorem complex_iff (Ωz k x y vx vy ax ay : ℝ) :
    (ax + ay * I) + 2 * I * Ωz * (vx + vy * I) + k * (x + y * I) = 0 ↔
      ax - 2 * Ωz * vy + k * x = 0 ∧ ay + 2 * Ωz * vx + k * y = 0 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp <;> linarith

/-- The complex **Foucault equation** `z̈ + 2 i Ω_z ż + k z = 0`, for a trajectory `z` with
velocity `z'` and acceleration `z''`. -/
def Solves (Ωz k : ℝ) (z z' z'' : ℝ → ℂ) : Prop :=
  ∀ t, HasDerivAt z (z' t) t ∧ HasDerivAt z' (z'' t) t ∧
    z'' t + 2 * I * Ωz * z' t + k * z t = 0

/-- The complex **non-rotating pendulum** `ζ̈ + ω² ζ = 0`, written with `ω² = w2`. -/
def Pendulum (w2 : ℝ) (ζ ζ' ζ'' : ℝ → ℂ) : Prop :=
  ∀ t, HasDerivAt ζ (ζ' t) t ∧ HasDerivAt ζ' (ζ'' t) t ∧ ζ'' t + w2 * ζ t = 0

/-- Derivative of `t ↦ e^{c t}` for `c : ℂ`. -/
theorem hasDerivAt_cexp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cexp (c * s)) (c * cexp (c * t)) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul c).cexp).comp_ofReal
  simpa [mul_comm] using h

/-- Product rule for `e^{c t} ζ(t)`. -/
theorem hasDerivAt_cexp_mul_mul {c : ℂ} {ζ : ℝ → ℂ} {ζ' : ℂ} {t : ℝ}
    (h : HasDerivAt ζ ζ' t) :
    HasDerivAt (fun s : ℝ => cexp (c * s) * ζ s) (cexp (c * t) * (ζ' + c * ζ t)) t := by
  convert (hasDerivAt_cexp_mul c t).mul h using 1
  ring

/-- **Change of frame by a uniform rotation**: if `ζ` has velocity `ζ'` and acceleration `ζ''`,
then `e^{c t} ζ` has velocity `e^{c t}(ζ' + c ζ)` and acceleration
`e^{c t}(ζ'' + 2 c ζ' + c² ζ)`. -/
theorem rotate_derivs {c : ℂ} {ζ ζ' : ℝ → ℂ} {ζ'' : ℂ} {t : ℝ} (h1 : ∀ s, HasDerivAt ζ (ζ' s) s)
    (h2 : HasDerivAt ζ' ζ'' t) :
    HasDerivAt (fun s : ℝ => cexp (c * s) * (ζ' s + c * ζ s))
      (cexp (c * t) * (ζ'' + 2 * c * ζ' t + c ^ 2 * ζ t)) t := by
  convert hasDerivAt_cexp_mul_mul (c := c) (h2.add ((h1 t).const_mul c)) using 1
  simp only [Pi.add_apply]
  ring

/-- **Precession theorem** (one direction): if `ζ` solves the non-rotating pendulum
`ζ̈ + (k + Ω_z²) ζ = 0`, then `z(t) = e^{-i Ω_z t} ζ(t)` solves the Foucault equation. -/
theorem solves_of_pendulum {Ωz k : ℝ} {ζ ζ' ζ'' : ℝ → ℂ} (h : Pendulum (k + Ωz ^ 2) ζ ζ' ζ'') :
    Solves Ωz k (fun t => cexp (-(Ωz * I) * t) * ζ t)
      (fun t => cexp (-(Ωz * I) * t) * (ζ' t + -(Ωz * I) * ζ t))
      (fun t => cexp (-(Ωz * I) * t) *
        (ζ'' t + 2 * -(Ωz * I) * ζ' t + (-(Ωz * I)) ^ 2 * ζ t)) := fun t => by
  refine ⟨hasDerivAt_cexp_mul_mul (h t).1, rotate_derivs (fun s => (h s).1) (h t).2.1, ?_⟩
  have e := (h t).2.2
  push_cast at e
  linear_combination cexp (-(Ωz * I) * t) * e + (-(Ωz ^ 2) * cexp (-(Ωz * I) * t) * ζ t) *
    I_sq

/-- **Precession theorem** (converse): if `z` solves the Foucault equation, then
`ζ(t) = e^{i Ω_z t} z(t)` solves the non-rotating pendulum `ζ̈ + (k + Ω_z²) ζ = 0`; and `z` is
recovered as `z(t) = e^{-i Ω_z t} ζ(t)`. -/
theorem pendulum_of_solves {Ωz k : ℝ} {z z' z'' : ℝ → ℂ} (h : Solves Ωz k z z' z'') :
    Pendulum (k + Ωz ^ 2) (fun t => cexp (Ωz * I * t) * z t)
      (fun t => cexp (Ωz * I * t) * (z' t + Ωz * I * z t))
      (fun t => cexp (Ωz * I * t) * (z'' t + 2 * (Ωz * I) * z' t + (Ωz * I) ^ 2 * z t)) ∧
    ∀ t, z t = cexp (-(Ωz * I) * t) * (cexp (Ωz * I * t) * z t) := by
  refine ⟨fun t => ⟨hasDerivAt_cexp_mul_mul (h t).1, rotate_derivs (fun s => (h s).1)
    (h t).2.1, ?_⟩, fun t => ?_⟩
  · have e := (h t).2.2
    push_cast
    linear_combination cexp (Ωz * I * t) * e + (Ωz ^ 2 * cexp (Ωz * I * t) * z t) * I_sq
  · rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Precession of the plane of oscillation**: if the non-rotating motion is planar,
`ζ(t) = r(t) u` with `r(t)` real, then the Foucault motion is `z(t) = r(t) (e^{-i Ω_z t} u)`:
the plane of oscillation, spanned by `e^{-i Ω_z t} u`, turns with angular velocity `-Ω_z`. -/
theorem planar_precesses (Ωz : ℝ) (r : ℝ → ℝ) (u : ℂ) (t : ℝ) :
    cexp (-(Ωz * I) * t) * (r t * u) = r t * (cexp ((-Ωz * t : ℝ) * I) * u) := by
  push_cast
  ring_nf

/-! ### Explicit solutions -/

/-- **Explicit solution**: with `ω² = k + Ω_z²`, `ζ(t) = A cos ωt + B sin ωt` solves the
non-rotating pendulum; hence `z(t) = e^{-i Ω_z t}(A cos ωt + B sin ωt)` solves the Foucault
equation. -/
theorem explicit_solves {Ωz k ω : ℝ} (hω : ω ^ 2 = k + Ωz ^ 2) (A B : ℂ) :
    Pendulum (k + Ωz ^ 2) (fun t => A * Complex.cos (ω * t) + B * Complex.sin (ω * t))
      (fun t => ω * (-A * Complex.sin (ω * t) + B * Complex.cos (ω * t)))
      (fun t => -(ω : ℂ) ^ 2 * (A * Complex.cos (ω * t) + B * Complex.sin (ω * t))) := by
  intro t
  have hω' : ((k + Ωz ^ 2 : ℝ) : ℂ) = (ω : ℂ) ^ 2 := by rw [← hω]; push_cast; ring
  have hl : HasDerivAt (fun s : ℝ => (ω : ℂ) * s) ω t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (ω : ℂ)
  have hc := (Complex.hasDerivAt_cos (ω * t)).comp t hl
  have hs := (Complex.hasDerivAt_sin (ω * t)).comp t hl
  refine ⟨?_, ?_, ?_⟩
  · convert (hc.const_mul A).add (hs.const_mul B) using 1
    · rfl
    · beta_reduce; ring
  · convert ((hs.const_mul (-A)).add (hc.const_mul B)).const_mul (ω : ℂ) using 1
    · funext s; simp only [Pi.add_apply, Function.comp]
    · beta_reduce; ring
  · rw [hω']; ring

/-- Real part of a rotated motion: if `z = e^{-i θ} ζ`, then
`x = cos θ · Re ζ + sin θ · Im ζ`. -/
theorem explicit_re (θ : ℝ) (ζ : ℂ) :
    (cexp (-(θ * I)) * ζ).re = Real.cos θ * ζ.re + Real.sin θ * ζ.im := by
  rw [show -(θ * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Imaginary part of a rotated motion: if `z = e^{-i θ} ζ`, then
`y = cos θ · Im ζ - sin θ · Re ζ`. -/
theorem explicit_im (θ : ℝ) (ζ : ℂ) :
    (cexp (-(θ * I)) * ζ).im = Real.cos θ * ζ.im - Real.sin θ * ζ.re := by
  rw [show -(θ * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- **Real form of the explicit solution** for a non-rotating oscillation along the `x` axis:
for `ζ(t) = a cos ωt` (`a` real), `x(t) = a cos(Ω_z t) cos ωt` and
`y(t) = -a sin(Ω_z t) cos ωt`. -/
theorem explicit_real (Ωz ω a t : ℝ) :
    (cexp (-((Ωz * t : ℝ) * I)) * (a * Complex.cos (ω * t))).re =
        a * Real.cos (Ωz * t) * Real.cos (ω * t) ∧
      (cexp (-((Ωz * t : ℝ) * I)) * (a * Complex.cos (ω * t))).im =
        -(a * Real.sin (Ωz * t) * Real.cos (ω * t)) := by
  rw [explicit_re, explicit_im, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  constructor <;> ring

/-! ### Precession period -/

/-- The vertical component `Ω_z = Ω sin φ` of the Earth's angular velocity. -/
def omegaZ (Ω φ : ℝ) : ℝ := Ω * Real.sin φ

/-- The **precession period** `T = 2π / (Ω |sin φ|)` of the plane of oscillation. -/
def precessionPeriod (Ω φ : ℝ) : ℝ := 2 * π / (Ω * |Real.sin φ|)

/-- After one precession period the rotation `e^{-i Ω_z t}` carrying the plane of oscillation
returns to itself: `e^{-i Ω_z (t + T)} = e^{-i Ω_z t}` (for `Ω ≠ 0`, `sin φ ≠ 0`). -/
theorem rotation_periodic {Ω φ : ℝ} (hΩ : Ω ≠ 0) (hφ : Real.sin φ ≠ 0) (t : ℝ) :
    cexp (-(omegaZ Ω φ * I) * ↑(t + precessionPeriod Ω φ)) = cexp (-(omegaZ Ω φ * I) * t) := by
  have key : ∃ n : ℤ, -(omegaZ Ω φ * precessionPeriod Ω φ) = n * (2 * π) := by
    simp only [omegaZ, precessionPeriod]
    rcases lt_or_gt_of_ne hφ with h | h
    · refine ⟨1, ?_⟩
      rw [abs_of_neg h]
      field_simp
      push_cast
      ring
    · refine ⟨-1, ?_⟩
      rw [abs_of_pos h]
      field_simp
      push_cast
      ring
  obtain ⟨n, hn⟩ := key
  have hc : -((omegaZ Ω φ : ℂ) * I) * (precessionPeriod Ω φ : ℂ) = n * (2 * π * I) := by
    have := congrArg (fun r : ℝ => (r : ℂ) * I) hn
    push_cast at this
    linear_combination this
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, hc, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

/-- **At the poles** (`φ = ±π/2`) the precession period is the sidereal day `2π/Ω`. -/
theorem precessionPeriod_pole (Ω : ℝ) :
    precessionPeriod Ω (π / 2) = 2 * π / Ω ∧ precessionPeriod Ω (-(π / 2)) = 2 * π / Ω := by
  simp [precessionPeriod]

/-- **At the equator** (`φ = 0`) there is no precession, `Ω_z = 0`. -/
theorem omegaZ_equator (Ω : ℝ) : omegaZ Ω 0 = 0 := by simp [omegaZ]

end Foucault

/-! ### The real equations of motion -/

/-- A **Foucault pendulum** in the small-amplitude horizontal model: position `(x, y)`, velocity
`(v_x, v_y)`, acceleration `(a_x, a_y)`, with `ẍ - 2 Ω_z ẏ + k x = 0`, `ÿ + 2 Ω_z ẋ + k y = 0`
(`k = ω₀² = g/ℓ`). -/
structure Foucault where
  Ωz : ℝ
  k : ℝ
  x : ℝ → ℝ
  y : ℝ → ℝ
  vx : ℝ → ℝ
  vy : ℝ → ℝ
  ax : ℝ → ℝ
  ay : ℝ → ℝ
  hasDerivAt_x : ∀ t, HasDerivAt x (vx t) t
  hasDerivAt_y : ∀ t, HasDerivAt y (vy t) t
  hasDerivAt_vx : ∀ t, HasDerivAt vx (ax t) t
  hasDerivAt_vy : ∀ t, HasDerivAt vy (ay t) t
  eq_x : ∀ t, ax t - 2 * Ωz * vy t + k * x t = 0
  eq_y : ∀ t, ay t + 2 * Ωz * vx t + k * y t = 0

namespace Foucault

variable (F : Foucault)

/-- **Complex form**: `z = x + i y` solves `z̈ + 2 i Ω_z ż + k z = 0`. -/
theorem complex_eq : Solves F.Ωz F.k (fun t => F.x t + F.y t * I) (fun t => F.vx t + F.vy t * I)
    (fun t => F.ax t + F.ay t * I) := fun t =>
  ⟨((F.hasDerivAt_x t).ofReal_comp).add (((F.hasDerivAt_y t).ofReal_comp).mul_const I),
    ((F.hasDerivAt_vx t).ofReal_comp).add (((F.hasDerivAt_vy t).ofReal_comp).mul_const I),
    (complex_iff _ _ _ _ _ _ _ _).2 ⟨F.eq_x t, F.eq_y t⟩⟩

/-- **Precession**: `ζ(t) = e^{i Ω_z t}(x + i y)` is a motion of the non-rotating pendulum
`ζ̈ + (k + Ω_z²) ζ = 0`; the Foucault motion is `e^{-i Ω_z t} ζ(t)`. -/
theorem precession :
    Pendulum (F.k + F.Ωz ^ 2) (fun t => cexp (F.Ωz * I * t) * (F.x t + F.y t * I))
      (fun t => cexp (F.Ωz * I * t) * ((F.vx t + F.vy t * I) + F.Ωz * I * (F.x t + F.y t * I)))
      (fun t => cexp (F.Ωz * I * t) * ((F.ax t + F.ay t * I) +
        2 * (F.Ωz * I) * (F.vx t + F.vy t * I) + (F.Ωz * I) ^ 2 * (F.x t + F.y t * I))) :=
  (pendulum_of_solves F.complex_eq).1

/-- **At the equator** (`Ω_z = 0`) the equations decouple into two harmonic oscillators
`ẍ + k x = 0`, `ÿ + k y = 0`. -/
theorem equator_decouple (h : F.Ωz = 0) (t : ℝ) :
    F.ax t + F.k * F.x t = 0 ∧ F.ay t + F.k * F.y t = 0 := by
  have h1 := F.eq_x t
  have h2 := F.eq_y t
  rw [h] at h1 h2
  constructor <;> linarith

/-- The angular-momentum-like quantity `x ẏ - y ẋ + Ω_z (x² + y²)`. -/
def angMom (t : ℝ) : ℝ := F.x t * F.vy t - F.y t * F.vx t + F.Ωz * (F.x t ^ 2 + F.y t ^ 2)

/-- The energy `½ (ẋ² + ẏ²) + ½ k (x² + y²)`. -/
def energy (t : ℝ) : ℝ := (F.vx t ^ 2 + F.vy t ^ 2) / 2 + F.k * (F.x t ^ 2 + F.y t ^ 2) / 2

/-- **Conservation of `x ẏ - y ẋ + Ω_z (x² + y²)`**. -/
theorem angMom_const (s t : ℝ) : F.angMom s = F.angMom t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have hx := F.hasDerivAt_x t
  have hy := F.hasDerivAt_y t
  have h := ((hx.mul (F.hasDerivAt_vy t)).sub (hy.mul (F.hasDerivAt_vx t))).add
    (((hx.pow 2).add (hy.pow 2)).const_mul F.Ωz)
  convert h using 1
  · rfl
  linear_combination F.y t * F.eq_x t - F.x t * F.eq_y t

/-- **Conservation of energy**: the Coriolis force does no work. -/
theorem energy_const (s t : ℝ) : F.energy s = F.energy t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((((F.hasDerivAt_vx t).pow 2).add ((F.hasDerivAt_vy t).pow 2)).div_const 2).add
    (((((F.hasDerivAt_x t).pow 2).add ((F.hasDerivAt_y t).pow 2)).const_mul F.k).div_const 2)
  convert h using 1
  · rfl
  linear_combination (-F.vx t) * F.eq_x t - F.vy t * F.eq_y t

end Foucault

end ClassicalMechanics
