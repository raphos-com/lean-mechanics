import ClassicalMechanics.Noether
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Constrained motion: d'Alembert's principle and Lagrange multipliers

A particle of mass `m` in `ℝ³` is constrained to the surface `g(x) = 0`, where `g` is
differentiable with gradient `∇g`. It moves under an applied force `F` and a **reaction** `R` of
the constraint. The constraint is **ideal** (frictionless) when the reaction does no virtual
work: `R · δx = 0` for every virtual displacement `δx` tangent to the surface, `∇g · δx = 0`
(**d'Alembert's principle**, [Goldstein2002], §1.4; [Arnold1989], §21; [Lanczos1970], ch. IV).

* **Lagrange multipliers** (`virtualWork_iff`): if `∇g ≠ 0`, the reaction does no virtual work
  iff `R = λ ∇g` for some `λ`. The equations of motion are then `m ẍ = F + λ ∇g(x)`
  (`ConstrainedMotion`).
* **Tangency** (`ConstrainedMotion.grad_dot_v`): differentiating `g(x(t)) = 0` gives
  `∇g(x) · ẋ = 0`.
* **Ideal constraints do no work** (`ConstrainedMotion.reaction_power`), so `Ṫ = F · ẋ`
  (`ConstrainedMotion.hasDerivAt_kinetic`) and, for a conservative applied force `F = -∇U`, the
  energy `T + U` is conserved (`ConstrainedMotion.energy_const`).
* **The spherical pendulum** (`SphericalPendulum`): `|x| = ℓ`, gravity `-m g e₃`, tension
  `R = λ x`. It is a constrained motion (`SphericalPendulum.toConstrainedMotion`); the vertical
  angular momentum `L₃ = m (x × ẋ)₃` (`SphericalPendulum.angMom₃_const`) and the energy
  `½ m |ẋ|² + m g x₃` (`SphericalPendulum.energy_const`) are conserved, and the multiplier is
  determined by position and velocity, `λ = m (g x₃ - |ẋ|²) / ℓ²`
  (`SphericalPendulum.multiplier_eq`).
* **The simple pendulum** (`SphericalPendulum.planar_energy_const`): for a motion in the plane
  `x₂ = 0`, written `x = (ℓ sin θ, 0, -ℓ cos θ)`, the energy integral is
  `½ m ℓ² θ̇² - m g ℓ cos θ = const`.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§1.4, 2.4.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §21.
* [Lanczos1970] C. Lanczos, *The Variational Principles of Mechanics*, 4th ed., ch. IV.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- **d'Alembert's principle and Lagrange multipliers**: for `n ≠ 0`, a vector `R` annihilates
every `u ⊥ n` (no virtual work) iff `R = λ n` for some `λ`. -/
theorem virtualWork_iff {n R : Vec} (hn : n ≠ 0) :
    (∀ u : Vec, n ⬝ᵥ u = 0 → R ⬝ᵥ u = 0) ↔ ∃ lam : ℝ, R = lam • n := by
  constructor
  · intro h
    have hnn : n ⬝ᵥ n ≠ 0 := fun h0 => hn (dotProduct_self_eq_zero.mp h0)
    set lam := (R ⬝ᵥ n) / (n ⬝ᵥ n)
    have hlam : lam * (n ⬝ᵥ n) = R ⬝ᵥ n := div_mul_cancel₀ _ hnn
    set u := R - lam • n
    have hu : n ⬝ᵥ u = 0 := by
      simp only [u, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm n R, hlam,
        sub_self]
    have hRu := h u hu
    have huu : u ⬝ᵥ u = 0 := by
      calc u ⬝ᵥ u = R ⬝ᵥ u - lam * (n ⬝ᵥ u) := by
            simp only [u, sub_dotProduct, smul_dotProduct, smul_eq_mul]
        _ = 0 := by rw [hRu, hu, mul_zero, sub_zero]
    exact ⟨lam, sub_eq_zero.mp (dotProduct_self_eq_zero.mp huu)⟩
  · rintro ⟨lam, rfl⟩ u hu
    rw [smul_dotProduct, hu, smul_zero]

/-- A particle constrained to the surface `g = 0` by an ideal constraint: `m ẍ = F + λ ∇g(x)`,
with Lagrange multiplier `λ(t)`. -/
structure ConstrainedMotion where
  /-- Mass. -/
  m : ℝ
  /-- The constraint function. -/
  g : Vec → ℝ
  /-- Its gradient `∇g`. -/
  grad : Vec → Vec
  hasFDerivAt_g : ∀ y, HasFDerivAt g (dotCLM (grad y)) y
  /-- Position. -/
  x : ℝ → Vec
  /-- Velocity. -/
  v : ℝ → Vec
  /-- Acceleration. -/
  a : ℝ → Vec
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  /-- The motion stays on the surface. -/
  constraint : ∀ t, g (x t) = 0
  /-- Applied force. -/
  F : ℝ → Vec
  /-- Lagrange multiplier. -/
  lam : ℝ → ℝ
  /-- Newton's law with the ideal reaction `λ ∇g`. -/
  newton : ∀ t, m • a t = F t + lam t • grad (x t)

namespace ConstrainedMotion

variable (C : ConstrainedMotion)

/-- The reaction of the constraint, `R = λ ∇g(x)`. -/
def reaction (t : ℝ) : Vec := C.lam t • C.grad (C.x t)

/-- Kinetic energy `T = ½ m |ẋ|²`. -/
def kinetic (t : ℝ) : ℝ := C.m / 2 * normSq (C.v t)

/-- The reaction does no virtual work: `R · δx = 0` for every `δx` tangent to the surface. -/
theorem reaction_virtualWork (t : ℝ) (u : Vec) (hu : C.grad (C.x t) ⬝ᵥ u = 0) :
    C.reaction t ⬝ᵥ u = 0 := by
  rw [reaction, smul_dotProduct, hu, smul_zero]

/-- **Tangency**: differentiating `g(x(t)) = 0` gives `∇g(x) · ẋ = 0`. -/
theorem grad_dot_v (t : ℝ) : C.grad (C.x t) ⬝ᵥ C.v t = 0 := by
  have h := (C.hasFDerivAt_g (C.x t)).comp_hasDerivAt t (C.hasDerivAt_x t)
  have he : C.g ∘ C.x = fun _ => 0 := funext C.constraint
  rw [he, dotCLM_apply] at h
  exact h.unique (hasDerivAt_const t 0)

/-- **Ideal constraints do no work**: `R · ẋ = 0`. -/
theorem reaction_power (t : ℝ) : C.reaction t ⬝ᵥ C.v t = 0 :=
  C.reaction_virtualWork t _ (C.grad_dot_v t)

/-- **Kinetic energy theorem**: only the applied force works, `Ṫ = F · ẋ`. -/
theorem hasDerivAt_kinetic (t : ℝ) : HasDerivAt C.kinetic (C.F t ⬝ᵥ C.v t) t := by
  have h := (hasDerivAt_dot (C.hasDerivAt_v t) (C.hasDerivAt_v t)).const_mul (C.m / 2)
  convert h using 1
  · rfl
  have hp := C.reaction_power t
  rw [reaction] at hp
  have e : C.m * (C.a t ⬝ᵥ C.v t) = C.F t ⬝ᵥ C.v t := by
    rw [← smul_eq_mul, ← smul_dotProduct, C.newton, add_dotProduct, hp, add_zero]
  rw [dotProduct_comm (C.v t) (C.a t), ← e]
  ring

/-- **Conservation of energy**: if the applied force is conservative, `F = -∇U`, then
`½ m |ẋ|² + U(x)` is constant. -/
theorem energy_const {U : Vec → ℝ} {gradU : Vec → Vec}
    (hU : ∀ y, HasFDerivAt U (dotCLM (gradU y)) y) (hF : ∀ t, C.F t = -gradU (C.x t))
    (s t : ℝ) : C.kinetic s + U (C.x s) = C.kinetic t + U (C.x t) := by
  refine eq_of_hasDerivAt_zero (F := fun s => C.kinetic s + U (C.x s)) (fun t => ?_) s t
  have h := (C.hasDerivAt_kinetic t).add ((hU (C.x t)).comp_hasDerivAt t (C.hasDerivAt_x t))
  rw [dotCLM_apply, hF, neg_dotProduct, neg_add_cancel] at h
  exact h

end ConstrainedMotion

/-- The derivative of `y ↦ |y|²` is `w ↦ 2 y · w`. -/
theorem hasFDerivAt_dot_self (y : Vec) :
    HasFDerivAt (fun z : Vec => z ⬝ᵥ z) (dotCLM ((2 : ℝ) • y)) y := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (show HasFDerivAt (fun z : Vec => z i * z i) _ y from
      (hasFDerivAt_apply (𝕜 := ℝ) i y).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) i y))
  convert h using 1
  · funext z; simp [dotProduct]
  · ext w
    simp only [dotCLM_apply, dotProduct, Pi.smul_apply, smul_eq_mul, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The **spherical pendulum**: a particle of mass `m` on the sphere `|x| = ℓ` in the uniform
gravitational field `-g e₃`, held by the tension `R = λ x` of a massless rod. -/
structure SphericalPendulum where
  /-- Mass. -/
  m : ℝ
  /-- Length. -/
  ℓ : ℝ
  /-- Gravitational acceleration. -/
  grav : ℝ
  ℓ_ne_zero : ℓ ≠ 0
  /-- Position. -/
  x : ℝ → Vec
  /-- Velocity. -/
  v : ℝ → Vec
  /-- Acceleration. -/
  a : ℝ → Vec
  hasDerivAt_x : ∀ t, HasDerivAt x (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t
  /-- The rod has length `ℓ`. -/
  constraint : ∀ t, x t ⬝ᵥ x t = ℓ ^ 2
  /-- The tension multiplier: the reaction is `λ x`. -/
  lam : ℝ → ℝ
  /-- Newton's law `m ẍ = -m g e₃ + λ x`. -/
  newton : ∀ t, m • a t = ![0, 0, -(m * grav)] + lam t • x t

namespace SphericalPendulum

variable (P : SphericalPendulum)

/-- The spherical pendulum is a constrained motion with `g(x) = |x|² - ℓ²`, `∇g = 2 x`,
applied force `-m g e₃` and multiplier `λ / 2`. -/
def toConstrainedMotion : ConstrainedMotion where
  m := P.m
  g y := y ⬝ᵥ y - P.ℓ ^ 2
  grad y := (2 : ℝ) • y
  hasFDerivAt_g y := (hasFDerivAt_dot_self y).sub_const _
  x := P.x
  v := P.v
  a := P.a
  hasDerivAt_x := P.hasDerivAt_x
  hasDerivAt_v := P.hasDerivAt_v
  constraint t := by rw [P.constraint, sub_self]
  F _ := ![0, 0, -(P.m * P.grav)]
  lam t := P.lam t / 2
  newton t := by
    rw [P.newton, smul_smul, div_mul_cancel₀ _ two_ne_zero]

/-- Vertical component of the angular momentum, `L₃ = m (x × ẋ)₃`. -/
def angMom₃ (t : ℝ) : ℝ := P.m * (P.x t ⨯₃ P.v t) 2

/-- The energy `½ m |ẋ|² + m g x₃`. -/
def energy (t : ℝ) : ℝ := P.m / 2 * normSq (P.v t) + P.m * P.grav * P.x t 2

/-- The velocity is tangent to the sphere: `x · ẋ = 0`. -/
theorem x_dot_v (t : ℝ) : P.x t ⬝ᵥ P.v t = 0 := by
  have h := P.toConstrainedMotion.grad_dot_v t
  simp only [toConstrainedMotion, smul_dotProduct, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- **Conservation of the vertical angular momentum**: the tension is radial and gravity is
vertical, so the torque has no vertical component. -/
theorem angMom₃_const (s t : ℝ) : P.angMom₃ s = P.angMom₃ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((hasDerivAt_pi.1 (hasDerivAt_cross (P.hasDerivAt_x t) (P.hasDerivAt_v t))) 2)
    |>.const_mul P.m
  have h0 : P.m * P.a t 0 = P.lam t * P.x t 0 := by simpa using congrFun (P.newton t) 0
  have h1 : P.m * P.a t 1 = P.lam t * P.x t 1 := by simpa using congrFun (P.newton t) 1
  convert h using 1
  · rfl
  rw [cross_self, zero_add]
  simp [cross_apply, -mul_eq_zero, -zero_eq_mul]
  linear_combination P.x t 1 * h0 - P.x t 0 * h1

/-- **Conservation of energy**: `½ m |ẋ|² + m g x₃` is constant. -/
theorem energy_const (s t : ℝ) : P.energy s = P.energy t := by
  have hU : ∀ y : Vec, HasFDerivAt (fun z : Vec => P.m * P.grav * z 2)
      (dotCLM ![0, 0, P.m * P.grav]) y := fun y => by
    have e : (fun z : Vec => P.m * P.grav * z 2) = ⇑(dotCLM ![0, 0, P.m * P.grav]) := by
      funext z; simp [dotProduct, Fin.sum_univ_three]
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  have hF : ∀ t, P.toConstrainedMotion.F t = -![0, 0, P.m * P.grav] := fun t => by
    ext i; fin_cases i <;> simp [toConstrainedMotion]
  exact P.toConstrainedMotion.energy_const hU hF s t

/-- `|ẋ|² + x · ẍ = 0`, from differentiating `x · ẋ = 0`. -/
theorem normSq_v_add_x_dot_a (t : ℝ) : normSq (P.v t) + P.x t ⬝ᵥ P.a t = 0 := by
  have h := hasDerivAt_dot (P.hasDerivAt_x t) (P.hasDerivAt_v t)
  have he : (fun s => P.x s ⬝ᵥ P.v s) = fun _ => 0 := funext P.x_dot_v
  rw [he] at h
  rw [normSq]
  exact h.unique (hasDerivAt_const t 0)

/-- **The tension**: the multiplier is determined by position and velocity,
`λ = m (g x₃ - |ẋ|²) / ℓ²`. -/
theorem multiplier_eq (t : ℝ) :
    P.lam t = P.m * (P.grav * P.x t 2 - normSq (P.v t)) / P.ℓ ^ 2 := by
  have h := congrArg (fun w => P.x t ⬝ᵥ w) (P.newton t)
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul, P.constraint] at h
  have hx : P.x t ⬝ᵥ ![0, 0, -(P.m * P.grav)] = -(P.m * P.grav) * P.x t 2 := by
    simp [dotProduct, Fin.sum_univ_three]; ring
  have ha := P.normSq_v_add_x_dot_a t
  rw [hx] at h
  rw [eq_div_iff (pow_ne_zero 2 P.ℓ_ne_zero)]
  linear_combination -h + P.m * ha

/-- **The simple pendulum**: for a motion in the plane `x₂ = 0`, written
`x = (ℓ sin θ, 0, -ℓ cos θ)` with `θ̇ = ω`, the energy integral is
`½ m ℓ² ω² - m g ℓ cos θ = const`. -/
theorem planar_energy_const {θ ω : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (ω t) t)
    (hx : ∀ t, P.x t = ![P.ℓ * Real.sin (θ t), 0, -(P.ℓ * Real.cos (θ t))]) (s t : ℝ) :
    P.m / 2 * P.ℓ ^ 2 * ω s ^ 2 - P.m * P.grav * P.ℓ * Real.cos (θ s) =
      P.m / 2 * P.ℓ ^ 2 * ω t ^ 2 - P.m * P.grav * P.ℓ * Real.cos (θ t) := by
  have hv : ∀ t, P.v t =
      ![P.ℓ * (Real.cos (θ t) * ω t), 0, P.ℓ * (Real.sin (θ t) * ω t)] := fun t => by
    have hd : HasDerivAt (fun s => ![P.ℓ * Real.sin (θ s), 0, -(P.ℓ * Real.cos (θ s))])
        ![P.ℓ * (Real.cos (θ t) * ω t), 0, P.ℓ * (Real.sin (θ t) * ω t)] t := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i
      · simpa using ((hθ t).sin).const_mul P.ℓ
      · simpa using hasDerivAt_const t (0 : ℝ)
      · simpa using (((hθ t).cos).const_mul P.ℓ).fun_neg
    have hX : P.x = fun s => ![P.ℓ * Real.sin (θ s), 0, -(P.ℓ * Real.cos (θ s))] := funext hx
    exact (P.hasDerivAt_x t).unique (hX ▸ hd)
  have E : ∀ t, P.energy t =
      P.m / 2 * P.ℓ ^ 2 * ω t ^ 2 - P.m * P.grav * P.ℓ * Real.cos (θ t) := fun t => by
    have hsc := Real.sin_sq_add_cos_sq (θ t)
    simp only [energy, normSq, hv, hx, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination P.m / 2 * P.ℓ ^ 2 * ω t ^ 2 * hsc
  rw [← E, ← E]
  exact P.energy_const s t

end SphericalPendulum

end ClassicalMechanics
