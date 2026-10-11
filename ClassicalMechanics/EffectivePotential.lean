import ClassicalMechanics.Kepler

/-!
# Central forces and the effective potential

A particle of mass `m > 0` moves in a **central potential** `V(r)`, differentiable on `(0, ∞)`
with derivative `V'`:

`m ẍ = -(V'(r) / r) x`,  `r = |x| > 0`

([Goldstein2002], §§3.1–3.3; [Arnold1989], §8).

* **Angular momentum** `L = x × m ẋ` is conserved (`angMom_const`).
* **Energy** `E = ½ m |ẋ|² + V(r)` is conserved (`energy_const`).
* The radial velocity is `ṙ = (x · ẋ) / r` (`hasDerivAt_r`), and by **Lagrange's identity**
  `|x|² |ẋ|² = (x · ẋ)² + |x × ẋ|²` (`dot_mul_dot_eq`) the speed splits into radial and
  angular parts, `|ẋ|² = ṙ² + |L|² / (m² r²)` (`speed_sq`).
* **Reduction to one dimension**: with the **effective potential**
  `U_eff(r) = V(r) + |L|² / (2 m r²)` (`effPot`), the energy reads
  `E = ½ m ṙ² + U_eff(r)` (`energy_radial`).
* Consequently the motion is confined to the **classically allowed region** `U_eff(r) ≤ E`
  (`effPot_le_energy`), and at a **turning point** (`ṙ = 0`) one has `U_eff(r) = E`
  (`effPot_eq_energy_of_turning`).
* The Kepler problem is the special case `V(r) = -k / r` (`KeplerMotion.toCentralMotion`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.1–3.3.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §8.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- **Lagrange's identity** `|x|² |v|² = (x · v)² + |x × v|²`. -/
theorem dot_mul_dot_eq (x v : Vec) :
    (x ⬝ᵥ x) * (v ⬝ᵥ v) = (x ⬝ᵥ v) ^ 2 + (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) := by
  rw [cross_dot_cross, dotProduct_comm v x]
  ring

/-- Motion in a **central potential** `V`: `m ẍ = -(V'(r) / r) x` with `x ≠ 0`, where `V` has
derivative `V'` on `(0, ∞)`. -/
structure CentralMotion where
  m : ℝ
  m_pos : 0 < m
  V : ℝ → ℝ
  V' : ℝ → ℝ
  hasDerivAt_V : ∀ ρ, 0 < ρ → HasDerivAt V (V' ρ) ρ
  x : ℝ → Vec
  v : ℝ → Vec
  a : ℝ → Vec
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  ne_zero : ∀ t, x t ≠ 0
  newton : ∀ t, m • a t = -(V' (radius (x t)) / radius (x t)) • x t

namespace CentralMotion

variable (C : CentralMotion)

/-- The distance to the centre of force. -/
def r (t : ℝ) : ℝ := radius (C.x t)

/-- The radial velocity `ṙ = (x · ẋ) / r`. -/
def rdot (t : ℝ) : ℝ := C.x t ⬝ᵥ C.v t / C.r t

/-- Angular momentum `L = x × m ẋ`. -/
def L (t : ℝ) : Vec := C.x t ⨯₃ (C.m • C.v t)

/-- Energy `E = ½ m |ẋ|² + V(r)`. -/
def E (t : ℝ) : ℝ := C.m / 2 * (C.v t ⬝ᵥ C.v t) + C.V (C.r t)

/-- The **effective potential** `U_eff(ρ) = V(ρ) + |L|² / (2 m ρ²)`. -/
def effPot (ρ : ℝ) : ℝ := C.V ρ + (C.L 0 ⬝ᵥ C.L 0) / (2 * C.m * ρ ^ 2)

theorem r_pos (t : ℝ) : 0 < C.r t := radius_pos (C.ne_zero t)

theorem r_sq (t : ℝ) : C.r t ^ 2 = C.x t ⬝ᵥ C.x t := radius_sq _

/-- The derivative of `r` is the radial velocity `ṙ = (x · ẋ) / r`. -/
theorem hasDerivAt_r (t : ℝ) : HasDerivAt C.r (C.rdot t) t := by
  have h := (hasDerivAt_dot (C.hasDerivAt_x t) (C.hasDerivAt_x t)).sqrt
    (dot_self_pos (C.ne_zero t)).ne'
  have hr := (C.r_pos t).ne'
  convert h using 1
  · rfl
  rw [dotProduct_comm (C.v t), rdot]
  change _ = _ / (2 * C.r t)
  field_simp
  ring

/-- `L̇ = 0`. -/
theorem hasDerivAt_L (t : ℝ) : HasDerivAt C.L 0 t := by
  have h := hasDerivAt_cross (C.hasDerivAt_x t) ((C.hasDerivAt_v t).const_smul C.m)
  convert h using 1
  · rfl
  rw [Pi.smul_apply, C.newton, map_smul, map_smul, cross_self, cross_self, smul_zero, smul_zero,
    add_zero]

/-- **Conservation of angular momentum**. -/
theorem angMom_const (s t : ℝ) : C.L s = C.L t := eq_of_hasDerivAt_zero C.hasDerivAt_L s t

/-- **Conservation of energy**. -/
theorem energy_const (s t : ℝ) : C.E s = C.E t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have hV := (C.hasDerivAt_V _ (C.r_pos t)).comp t (C.hasDerivAt_r t)
  have h := ((hasDerivAt_dot (C.hasDerivAt_v t) (C.hasDerivAt_v t)).const_mul (C.m / 2)).add hV
  have hr := (C.r_pos t).ne'
  have hma : C.m * (C.a t ⬝ᵥ C.v t) = -(C.V' (C.r t) / C.r t) * (C.x t ⬝ᵥ C.v t) := by
    rw [← smul_eq_mul, ← smul_dotProduct, C.newton, smul_dotProduct, smul_eq_mul]; rfl
  convert h using 1
  · funext s; simp [E, Function.comp_def]
  · rw [dotProduct_comm (C.v t) (C.a t), rdot]
    have : C.m / 2 * (C.a t ⬝ᵥ C.v t + C.a t ⬝ᵥ C.v t) = C.m * (C.a t ⬝ᵥ C.v t) := by
      ring
    rw [this, hma]
    field_simp
    ring

/-- `|L|² = m² |x × ẋ|²`. -/
theorem L_dot_L (t : ℝ) :
    C.L 0 ⬝ᵥ C.L 0 = C.m ^ 2 * ((C.x t ⨯₃ C.v t) ⬝ᵥ (C.x t ⨯₃ C.v t)) := by
  rw [← C.angMom_const t 0, L, map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  ring

/-- **Radial and angular parts of the speed**: `|ẋ|² = ṙ² + |L|² / (m² r²)`. -/
theorem speed_sq (t : ℝ) :
    C.v t ⬝ᵥ C.v t = C.rdot t ^ 2 + (C.L 0 ⬝ᵥ C.L 0) / (C.m ^ 2 * C.r t ^ 2) := by
  have hr := (C.r_pos t).ne'
  have hm := C.m_pos.ne'
  have h := dot_mul_dot_eq (C.x t) (C.v t)
  rw [← C.r_sq] at h
  rw [C.L_dot_L t, rdot]
  field_simp
  linear_combination h

/-- **Radial energy equation**: `E = ½ m ṙ² + U_eff(r)`, the energy of a one-dimensional
motion in the effective potential. -/
theorem energy_radial (t : ℝ) : C.E t = C.m / 2 * C.rdot t ^ 2 + C.effPot (C.r t) := by
  have hr := (C.r_pos t).ne'
  have hm := C.m_pos.ne'
  rw [E, effPot, C.speed_sq t]
  field_simp
  ring

/-- The motion stays in the **classically allowed region**: `U_eff(r(t)) ≤ E` for all `t`
(with `E` the conserved energy). -/
theorem effPot_le_energy (t : ℝ) : C.effPot (C.r t) ≤ C.E 0 := by
  rw [C.energy_const 0 t, C.energy_radial t]
  have := C.m_pos
  have : 0 ≤ C.m / 2 * C.rdot t ^ 2 := by positivity
  linarith

/-- At a **turning point** (`ṙ = 0`) the effective potential equals the energy. -/
theorem effPot_eq_energy_of_turning {t : ℝ} (h : C.rdot t = 0) : C.effPot (C.r t) = C.E 0 := by
  rw [C.energy_const 0 t, C.energy_radial t, h]
  ring

/-- Conversely, where `U_eff(r) = E` the radial velocity vanishes. -/
theorem rdot_eq_zero_of_effPot_eq {t : ℝ} (h : C.effPot (C.r t) = C.E 0) : C.rdot t = 0 := by
  rw [C.energy_const 0 t, C.energy_radial t] at h
  have hm := C.m_pos
  have : C.rdot t ^ 2 = 0 := by nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

end CentralMotion

namespace KeplerMotion

variable (K : KeplerMotion)

/-- The **Kepler problem** as a central motion in the potential `V(r) = -k / r`
(`V'(r) = k / r²`). -/
def toCentralMotion : CentralMotion where
  m := K.m
  m_pos := K.m_pos
  V := fun ρ => -K.k / ρ
  V' := fun ρ => K.k / ρ ^ 2
  hasDerivAt_V ρ hρ := by
    have h := (hasDerivAt_inv hρ.ne').const_mul (-K.k)
    convert h using 1
    · funext s; ring
    · field_simp
  x := K.x
  v := K.v
  a := K.a
  hasDerivAt_x := K.hasDerivAt_x
  hasDerivAt_v := K.hasDerivAt_v
  ne_zero := K.ne_zero
  newton t := by
    rw [K.newton t]
    have hr := (radius_pos (K.ne_zero t)).ne'
    congr 2
    field_simp

/-- The Kepler energy is the central-motion energy for `V = -k / r`. -/
theorem toCentralMotion_E (t : ℝ) : K.toCentralMotion.E t = K.E t := by
  simp only [CentralMotion.E, E, toCentralMotion, CentralMotion.r, r]
  ring

/-- **Kepler effective potential**: `-k / r + |L|² / (2 m r²) ≤ E` along the motion. -/
theorem effPot_le_energy (t : ℝ) :
    -K.k / K.r t + (K.L 0 ⬝ᵥ K.L 0) / (2 * K.m * K.r t ^ 2) ≤ K.E 0 := by
  have h := K.toCentralMotion.effPot_le_energy t
  rwa [toCentralMotion_E] at h

end KeplerMotion

end ClassicalMechanics
