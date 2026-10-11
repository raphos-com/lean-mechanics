import ClassicalMechanics.Lagrangian
import ClassicalMechanics.Noether

/-!
# Cyclic coordinates and Routh reduction

A coordinate is **cyclic** (ignorable) if the Lagrangian does not depend on it. Its conjugate
momentum is then conserved, and fixing its value reduces the number of degrees of freedom: this
is **Routh's procedure** ([Goldstein2002], §8.3; [LandauLifshitz1976], §41; [Arnold1989], §15).

* **Cyclic coordinates in `ℝⁿ`** (`LagrangianN.cyclic_momentum_const`): if `∂L/∂qₖ = 0`, the
  conjugate momentum `pₖ = ∂L/∂q̇ₖ` is conserved along every solution of the Euler–Lagrange
  equations.
* **Two degrees of freedom** (`CyclicLagrangian`): a Lagrangian `L(x, ẋ, ẏ)` in the coordinates
  `(x, y)`, independent of `y`. The momentum `p = ∂L/∂ẏ` is conserved
  (`CyclicLagrangian.momentum_const`).
* **The Routhian** (`RouthInverse.routhian`): if, on a set `U` of states `(x, ẋ)`, the momentum
  relation `p = ∂L/∂ẏ(x, ẋ, ẏ)` has the unique differentiable solution `ẏ = Y(x, ẋ)`, the
  Routhian is `R(x, ẋ) = L(x, ẋ, Y) - p Y`. Its partial derivatives are
  `∂R/∂x = ∂L/∂x` and `∂R/∂ẋ = ∂L/∂ẋ` evaluated at `ẏ = Y` (`hasFDerivAt_routhian`), since the
  terms containing the derivatives of `Y` cancel by the momentum relation.
* **Routh reduction** (`RouthInverse.routh`, `RouthInverse.toLagrangian_EulerLagrange`): along a
  solution of the full Euler–Lagrange equations with momentum `p`, `ẏ = Y(x, ẋ)` and the reduced
  motion `x(t)` satisfies the Euler–Lagrange equation `d/dt ∂R/∂ẋ = ∂R/∂x` of the Routhian.
* **Central force in the plane** (`CyclicLagrangian.polar`): `L = ½ m (ṙ² + r² θ̇²) - V(r)`, with
  `θ` cyclic. The angular momentum `p = m r² θ̇` is conserved (`polar_angMom_const`), the
  Routhian is `R = ½ m ṙ² - V(r) - p² / (2 m r²) = ½ m ṙ² - V_eff(r)` (`polar_routhian`) with the
  effective potential `V_eff(r) = V(r) + p² / (2 m r²)`, and the radial motion obeys
  `m r̈ = -V'(r) + p² / (m r³) = -V_eff'(r)` (`polar_radial`, `polar_radial_effPot`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§2.6, 8.3.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §§14–15, 41.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §15.
* [Routh1877] E. J. Routh, *A Treatise on the Stability of a Given State of Motion* (1877).
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-! ### Cyclic coordinates in `ℝⁿ` -/

namespace LagrangianN

variable {n : ℕ} (𝓛 : LagrangianN n) (γ : MotionN n)

/-- **Cyclic coordinates**: if `∂L/∂qₖ = 0` everywhere, the conjugate momentum
`pₖ = ∂L/∂q̇ₖ` is conserved along every solution of the Euler–Lagrange equations. -/
theorem cyclic_momentum_const (k : Fin n) (hk : ∀ q v, 𝓛.Lq q v k = 0)
    (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) :
    𝓛.Lv (γ.q s) (γ.v s) k = 𝓛.Lv (γ.q t) (γ.v t) k := by
  have h := 𝓛.momentum_const γ (Pi.single k 1)
    (fun q v => by rw [dotProduct_single, mul_one, hk]) hEL s t
  simpa [dotProduct_single] using h

end LagrangianN

/-! ### Two degrees of freedom with a cyclic coordinate -/

/-- A Lagrangian `L(x, ẋ, ẏ)` of two degrees of freedom `(x, y)` which does not depend on `y`,
so that `y` is a **cyclic coordinate**, with its partial derivatives `L_x`, `L_ẋ`, `L_ẏ`. -/
structure CyclicLagrangian where
  /-- The Lagrangian `L(x, ẋ, ẏ)`. -/
  L : ℝ → ℝ → ℝ → ℝ
  /-- The partial derivative `∂L/∂x`. -/
  Lx : ℝ → ℝ → ℝ → ℝ
  /-- The partial derivative `∂L/∂ẋ`. -/
  Lxd : ℝ → ℝ → ℝ → ℝ
  /-- The partial derivative `∂L/∂ẏ`. -/
  Lyd : ℝ → ℝ → ℝ → ℝ
  hasFDerivAt : ∀ x xd yd, HasFDerivAt (fun w : ℝ × ℝ × ℝ => L w.1 w.2.1 w.2.2)
    (Lx x xd yd • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
      Lxd x xd yd • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
      Lyd x xd yd • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    (x, xd, yd)

namespace CyclicLagrangian

variable (𝓛 : CyclicLagrangian) (γ η : Motion)

/-- The **Euler–Lagrange equations** for the motion `x = γ.q`, `y = η.q`:
`d/dt L_ẋ = L_x` and, since `L` does not depend on `y`, `d/dt L_ẏ = 0`. -/
def EulerLagrange : Prop :=
  (∀ t, HasDerivAt (fun s => 𝓛.Lxd (γ.q s) (γ.v s) (η.v s)) (𝓛.Lx (γ.q t) (γ.v t) (η.v t)) t) ∧
    ∀ t, HasDerivAt (fun s => 𝓛.Lyd (γ.q s) (γ.v s) (η.v s)) 0 t

/-- The momentum `p = ∂L/∂ẏ` conjugate to the cyclic coordinate `y`. -/
def momentum (t : ℝ) : ℝ := 𝓛.Lyd (γ.q t) (γ.v t) (η.v t)

/-- **Conservation of the cyclic momentum** `p = ∂L/∂ẏ`. -/
theorem momentum_const (hEL : 𝓛.EulerLagrange γ η) (s t : ℝ) :
    𝓛.momentum γ η s = 𝓛.momentum γ η t :=
  eq_of_hasDerivAt_zero hEL.2 s t

end CyclicLagrangian

/-- Data for **Routh's reduction** at a fixed value `p` of the cyclic momentum: on a set `U` of
states `(x, ẋ)`, the momentum relation `L_ẏ(x, ẋ, ẏ) = p` has the unique solution
`ẏ = Y(x, ẋ)`, which is differentiable with derivative `DY`. -/
structure RouthInverse (𝓛 : CyclicLagrangian) (p : ℝ) where
  /-- The set of states `(x, ẋ)` on which the momentum relation is inverted. -/
  U : Set (ℝ × ℝ)
  /-- The cyclic velocity `ẏ = Y(x, ẋ)` as a function of the state, at momentum `p`. -/
  Y : ℝ × ℝ → ℝ
  /-- The derivative of `Y`. -/
  DY : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
  hasFDerivAt : ∀ z ∈ U, HasFDerivAt Y (DY z) z
  momentum_Y : ∀ z ∈ U, 𝓛.Lyd z.1 z.2 (Y z) = p
  unique : ∀ z ∈ U, ∀ yd, 𝓛.Lyd z.1 z.2 yd = p → yd = Y z

namespace RouthInverse

variable {𝓛 : CyclicLagrangian} {p : ℝ} (ρ : RouthInverse 𝓛 p)

/-- The **Routhian** `R(x, ẋ) = L(x, ẋ, ẏ) - p ẏ` with `ẏ = Y(x, ẋ)` eliminated through the
momentum relation. -/
def routhian (z : ℝ × ℝ) : ℝ := 𝓛.L z.1 z.2 (ρ.Y z) - p * ρ.Y z

/-- The partial derivative `∂R/∂x = L_x(x, ẋ, Y(x, ẋ))`. -/
def Rx (z : ℝ × ℝ) : ℝ := 𝓛.Lx z.1 z.2 (ρ.Y z)

/-- The partial derivative `∂R/∂ẋ = L_ẋ(x, ẋ, Y(x, ẋ))`. -/
def Rxd (z : ℝ × ℝ) : ℝ := 𝓛.Lxd z.1 z.2 (ρ.Y z)

/-- **Derivative of the Routhian**: on `U`, `∂R/∂x = L_x` and `∂R/∂ẋ = L_ẋ` at `ẏ = Y(x, ẋ)`;
the contributions of the derivative of `Y` cancel because `L_ẏ = p`. -/
theorem hasFDerivAt_routhian {z : ℝ × ℝ} (hz : z ∈ ρ.U) :
    HasFDerivAt ρ.routhian
      (ρ.Rx z • ContinuousLinearMap.fst ℝ ℝ ℝ + ρ.Rxd z • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  have hY := ρ.hasFDerivAt z hz
  have hw : HasFDerivAt (fun z : ℝ × ℝ => (z.1, z.2, ρ.Y z))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ρ.DY z))) z :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk hY)
  have hL := (𝓛.hasFDerivAt z.1 z.2 (ρ.Y z)).comp z hw
  have h := hL.sub (hY.const_mul p)
  convert h using 1
  · rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [Rx, Rxd, ρ.momentum_Y z hz]

/-- **Routh's reduction**: along a solution of the full Euler–Lagrange equations whose cyclic
momentum is `p` and whose states stay in `U`, the cyclic velocity is `ẏ = Y(x, ẋ)` and the
reduced motion `x(t)` satisfies the Euler–Lagrange equation `d/dt ∂R/∂ẋ = ∂R/∂x` of the
Routhian. -/
theorem routh {γ η : Motion} (hEL : 𝓛.EulerLagrange γ η) (hU : ∀ t, (γ.q t, γ.v t) ∈ ρ.U)
    (hp : 𝓛.momentum γ η 0 = p) :
    (∀ t, η.v t = ρ.Y (γ.q t, γ.v t)) ∧
      ∀ t, HasDerivAt (fun s => ρ.Rxd (γ.q s, γ.v s)) (ρ.Rx (γ.q t, γ.v t)) t := by
  have hY : ∀ t, η.v t = ρ.Y (γ.q t, γ.v t) := fun t =>
    ρ.unique _ (hU t) _ (by rw [← hp]; exact 𝓛.momentum_const γ η hEL t 0)
  refine ⟨hY, fun t => ?_⟩
  simpa only [Rx, Rxd, ← hY] using hEL.1 t

/-- When the momentum relation is inverted on all states, the Routhian is a Lagrangian of one
degree of freedom. -/
def toLagrangian (hU : ρ.U = Set.univ) : Lagrangian where
  L x xd := ρ.routhian (x, xd)
  Lq x xd := ρ.Rx (x, xd)
  Lv x xd := ρ.Rxd (x, xd)
  hasFDerivAt _ _ := ρ.hasFDerivAt_routhian (hU ▸ Set.mem_univ _)

/-- **Routh's reduction**, global form: the reduced motion `x(t)` is a solution of the
Euler–Lagrange equation of the Routhian Lagrangian. -/
theorem toLagrangian_EulerLagrange (hU : ρ.U = Set.univ) {γ η : Motion}
    (hEL : 𝓛.EulerLagrange γ η) (hp : 𝓛.momentum γ η 0 = p) :
    (ρ.toLagrangian hU).EulerLagrange γ :=
  (ρ.routh hEL (fun _ => hU ▸ Set.mem_univ _) hp).2

end RouthInverse

/-! ### Example: a particle in a central potential in the plane -/

namespace CyclicLagrangian

variable {m : ℝ} {V V' : ℝ → ℝ}

/-- The Lagrangian `L = ½ m (ṙ² + r² θ̇²) - V(r)` of a particle of mass `m` in the plane in polar
coordinates `(r, θ)`, moving in a central potential `V`; the angle `θ` is cyclic. -/
def polar (m : ℝ) (V V' : ℝ → ℝ) (hV : ∀ r, HasDerivAt V (V' r) r) : CyclicLagrangian where
  L r rd θd := m / 2 * (rd ^ 2 + r ^ 2 * θd ^ 2) - V r
  Lx r _ θd := m * r * θd ^ 2 - V' r
  Lxd _ rd _ := m * rd
  Lyd r _ θd := m * r ^ 2 * θd
  hasFDerivAt r rd θd := by
    have h1 : HasFDerivAt (fun w : ℝ × ℝ × ℝ => w.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (r, rd, θd) := hasFDerivAt_fst
    have h2 : HasFDerivAt (fun w : ℝ × ℝ × ℝ => w.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (r, rd, θd) := hasFDerivAt_snd.fst
    have h3 : HasFDerivAt (fun w : ℝ × ℝ × ℝ => w.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (r, rd, θd) := hasFDerivAt_snd.snd
    have hV' := (hV r).hasFDerivAt.comp (r, rd, θd) h1
    have h := (((h2.pow 2).add ((h1.pow 2).mul (h3.pow 2))).const_mul (m / 2)).sub hV'
    convert h using 1
    · rfl
    apply ContinuousLinearMap.ext
    intro w
    simp
    ring

variable (hV : ∀ r, HasDerivAt V (V' r) r)

/-- **Conservation of angular momentum** `p = m r² θ̇`: `θ` is cyclic. -/
theorem polar_angMom_const {γ η : Motion} (hEL : (polar m V V' hV).EulerLagrange γ η)
    (s t : ℝ) : m * γ.q s ^ 2 * η.v s = m * γ.q t ^ 2 * η.v t :=
  (polar m V V' hV).momentum_const γ η hEL s t

/-- The inversion `θ̇ = p / (m r²)` of the angular momentum relation `p = m r² θ̇`, valid for
`m ≠ 0` and `r ≠ 0`. -/
def polarInverse (hm : m ≠ 0) (p : ℝ) : RouthInverse (polar m V V' hV) p where
  U := {z | z.1 ≠ 0}
  Y z := p / (m * z.1 ^ 2)
  DY z := (-(2 * p) / (m * z.1 ^ 3)) • ContinuousLinearMap.fst ℝ ℝ ℝ
  hasFDerivAt z hz := by
    have hz : z.1 ≠ 0 := hz
    have hz' : m * z.1 ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hz)
    have h := ((((hasDerivAt_pow 2 z.1).const_mul m).inv hz').const_mul p).comp_hasFDerivAt z
      (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
    convert h using 1
    · funext w; simp [div_eq_mul_inv]
    · congr 1
      field_simp
      ring
  momentum_Y z hz := by
    have hz : z.1 ≠ 0 := hz
    simp only [polar]
    field_simp
  unique z hz yd h := by
    have hz' : m * z.1 ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hz)
    simp only [polar] at h
    rw [eq_div_iff hz', ← h]
    ring

/-- The **effective potential** `V_eff(r) = V(r) + p² / (2 m r²)` for angular momentum `p`. -/
def polarEffPot (m p : ℝ) (V : ℝ → ℝ) (r : ℝ) : ℝ := V r + p ^ 2 / (2 * m * r ^ 2)

include hV in
/-- The derivative of the effective potential: `V_eff'(r) = V'(r) - p² / (m r³)`. -/
theorem hasDerivAt_polarEffPot (hm : m ≠ 0) (p : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (polarEffPot m p V) (V' r - p ^ 2 / (m * r ^ 3)) r := by
  have hr' : 2 * m * r ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hr)
  have h := (hV r).add ((((hasDerivAt_pow 2 r).const_mul (2 * m)).inv hr').const_mul (p ^ 2))
  convert h using 1
  · funext s; simp [polarEffPot, div_eq_mul_inv]
  · field_simp
    ring

/-- The **Routhian** of the central-force problem is `R = ½ m ṙ² - V(r) - p² / (2 m r²)`, i.e. the
Lagrangian `½ m ṙ² - V_eff(r)` of a one-dimensional motion in the effective potential. -/
theorem polar_routhian (hm : m ≠ 0) (p : ℝ) {r rd : ℝ} (hr : r ≠ 0) :
    (polarInverse hV hm p).routhian (r, rd) = m / 2 * rd ^ 2 - V r - p ^ 2 / (2 * m * r ^ 2) ∧
      (polarInverse hV hm p).routhian (r, rd) = m / 2 * rd ^ 2 - polarEffPot m p V r := by
  have e : (polarInverse hV hm p).routhian (r, rd) =
      m / 2 * rd ^ 2 - V r - p ^ 2 / (2 * m * r ^ 2) := by
    simp only [RouthInverse.routhian, polarInverse, polar]
    field_simp
    ring
  exact ⟨e, by rw [e, polarEffPot]; ring⟩

/-- The partial derivative `∂R/∂r = -V'(r) + p² / (m r³) = -V_eff'(r)` of the Routhian. -/
theorem polar_Rx (hm : m ≠ 0) (p : ℝ) {r rd : ℝ} (hr : r ≠ 0) :
    (polarInverse hV hm p).Rx (r, rd) = -V' r + p ^ 2 / (m * r ^ 3) := by
  simp only [RouthInverse.Rx, polarInverse, polar]
  field_simp
  ring

/-- **The reduced radial equation**: along a solution of the full Euler–Lagrange equations of
`L = ½ m (ṙ² + r² θ̇²) - V(r)` that avoids the origin, with angular momentum `p = m r² θ̇`,
`θ̇ = p / (m r²)` and `m r̈ = -V'(r) + p² / (m r³)`. -/
theorem polar_radial (hm : m ≠ 0) {γ η : Motion} (hEL : (polar m V V' hV).EulerLagrange γ η)
    (hr : ∀ t, γ.q t ≠ 0) (t : ℝ) :
    η.v t = (polar m V V' hV).momentum γ η 0 / (m * γ.q t ^ 2) ∧
      m * γ.a t = -V' (γ.q t) + (polar m V V' hV).momentum γ η 0 ^ 2 / (m * γ.q t ^ 3) := by
  set p := (polar m V V' hV).momentum γ η 0
  have h := (polarInverse hV hm p).routh hEL hr rfl
  refine ⟨h.1 t, ?_⟩
  have h2 : HasDerivAt (fun s => m * γ.v s) (m * γ.a t) t := (γ.hasDerivAt_v t).const_mul m
  rw [h2.unique (h.2 t), polar_Rx hV hm p (hr t)]

/-- The reduced radial equation in terms of the effective potential: `m r̈ = -V_eff'(r)`, the
derivative being that of `V_eff(r) = V(r) + p² / (2 m r²)`. -/
theorem polar_radial_effPot (hm : m ≠ 0) {γ η : Motion}
    (hEL : (polar m V V' hV).EulerLagrange γ η) (hr : ∀ t, γ.q t ≠ 0) (t : ℝ) :
    HasDerivAt (polarEffPot m ((polar m V V' hV).momentum γ η 0) V) (-(m * γ.a t)) (γ.q t) := by
  have h := hasDerivAt_polarEffPot hV hm ((polar m V V' hV).momentum γ η 0) (hr t)
  rw [(polar_radial hV hm hEL hr t).2]
  convert h using 1
  ring

end CyclicLagrangian

end ClassicalMechanics
