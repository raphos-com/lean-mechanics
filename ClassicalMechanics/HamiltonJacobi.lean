import ClassicalMechanics.Oscillator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Hamilton–Jacobi theory and action–angle variables

For a time-dependent Hamiltonian `H(q, p, t)` with one degree of freedom, the
**Hamilton–Jacobi equation** for a generating function `S(q, α, t)` is

`∂ₜS + H(q, ∂_qS, t) = 0`.

* **Jacobi's theorem** (`CompleteIntegral.jacobi`): if `S` is a solution depending on a
  parameter `α` with `∂²S/∂q∂α ≠ 0` (a complete integral), and a curve `q(t)` satisfies
  `∂_αS(q(t), α, t) = β` for a constant `β`, then `(q(t), p(t) = ∂_qS(q(t), α, t))` solves
  Hamilton's equations `q̇ = H_p`, `ṗ = -H_q`. The proof differentiates `∂_αS(q(t), α, t) = β`
  in `t` and the Hamilton–Jacobi equation in `α` and in `q`.
* **Action–angle variables for the harmonic oscillator** `H = p²/(2m) + mω²q²/2`
  (`ActionAngle`): the map `(θ, I) ↦ (q, p) = (√(2I/(mω)) sin θ, √(2Imω) cos θ)`
  * is **area-preserving**: its Jacobian determinant is `1` (`ActionAngle.det_jacobian`);
  * turns the Hamiltonian into `H = ωI` (`ActionAngle.hamiltonian_eq`), so `I = E/ω`
    (`ActionAngle.action_eq`), and Hamilton's equations become `θ̇ = ω`, `İ = 0`;
  * the linear flow `θ(t) = θ₀ + ωt`, `I(t) = I` gives a solution of `q̇ = p/m`, `ṗ = -mω²q`
    (`ActionAngle.flow_solves`), namely the familiar
    `q(t) = q(0) cos ωt + (q̇(0)/ω) sin ωt` (`ActionAngle.flow_eq_sol`), and a motion of the
    harmonic oscillator of `ClassicalMechanics.Oscillator` (`ActionAngle.toHarmonic`).
* **Action as phase-space area** (`ActionAngle.action_eq_area`):
  `I = (1/2π) ∮ p dq`, computed as `(1/2π) ∫₀^{2π} p(θ) q'(θ) dθ`.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§47, 50.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§10.1–10.6.
-/

open Real ContinuousLinearMap
open scoped Real

noncomputable section

namespace ClassicalMechanics

namespace HamiltonJacobi

/-- Chain rule for a function of two real variables along a curve `s ↦ (f s, g s)`,
with the derivative given by partial derivatives `A`, `B`. -/
theorem hasDerivAt_comp₂ {F : ℝ → ℝ → ℝ} {A B : ℝ} {f g : ℝ → ℝ} {f' g' s : ℝ}
    (hF : HasFDerivAt (fun z : ℝ × ℝ => F z.1 z.2)
      (A • fst ℝ ℝ ℝ + B • snd ℝ ℝ ℝ) (f s, g s))
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun s => F (f s) (g s)) (A * f' + B * g') s := by
  have h := hF.comp_hasDerivAt s (hf.prodMk hg)
  convert h using 1
  · rfl
  · simp [smul_eq_mul]

end HamiltonJacobi

/-- A **time-dependent Hamiltonian** with one degree of freedom, `H(q, p, t)`, with its partial
derivatives `H_q`, `H_p` (jointly in `(q, p)` at each time). -/
structure TimeHamiltonian where
  H : ℝ → ℝ → ℝ → ℝ
  Hq : ℝ → ℝ → ℝ → ℝ
  Hp : ℝ → ℝ → ℝ → ℝ
  hasFDerivAt : ∀ q p t, HasFDerivAt (fun z : ℝ × ℝ => H z.1 z.2 t)
    (Hq q p t • fst ℝ ℝ ℝ + Hp q p t • snd ℝ ℝ ℝ) (q, p)

/-- A **complete integral** `S(q, α, t)` of the Hamilton–Jacobi equation
`∂ₜS + H(q, ∂_qS, t) = 0`, with the first partial derivatives `S_q`, `S_α`, `S_t` and the
second partial derivatives needed for Jacobi's theorem. Mixed partials are identified
(Schwarz's theorem, valid for `S` of class `C²`): `Sqα = ∂_α S_q = ∂_q S_α`,
`Sαt = ∂_t S_α = ∂_α S_t`, `Sqt = ∂_t S_q = ∂_q S_t`. Completeness is the nondegeneracy
condition `∂²S/∂q∂α ≠ 0`. -/
structure CompleteIntegral (H : TimeHamiltonian) where
  S : ℝ → ℝ → ℝ → ℝ
  Sq : ℝ → ℝ → ℝ → ℝ
  Sα : ℝ → ℝ → ℝ → ℝ
  St : ℝ → ℝ → ℝ → ℝ
  Sqq : ℝ → ℝ → ℝ → ℝ
  Sqα : ℝ → ℝ → ℝ → ℝ
  Sqt : ℝ → ℝ → ℝ → ℝ
  Sαt : ℝ → ℝ → ℝ → ℝ
  hasDerivAt_Sq : ∀ q a t, HasDerivAt (fun x => S x a t) (Sq q a t) q
  hasDerivAt_Sα : ∀ q a t, HasDerivAt (fun b => S q b t) (Sα q a t) a
  hasDerivAt_St : ∀ q a t, HasDerivAt (fun s => S q a s) (St q a t) t
  /-- The Hamilton–Jacobi equation. -/
  hj : ∀ q a t, St q a t + H.H q (Sq q a t) t = 0
  /-- `S_q` is differentiable in `(q, t)`. -/
  hasFDerivAt_Sq : ∀ q a t, HasFDerivAt (fun z : ℝ × ℝ => Sq z.1 a z.2)
    (Sqq q a t • fst ℝ ℝ ℝ + Sqt q a t • snd ℝ ℝ ℝ) (q, t)
  /-- `S_α` is differentiable in `(q, t)`. -/
  hasFDerivAt_Sα : ∀ q a t, HasFDerivAt (fun z : ℝ × ℝ => Sα z.1 a z.2)
    (Sqα q a t • fst ℝ ℝ ℝ + Sαt q a t • snd ℝ ℝ ℝ) (q, t)
  hasDerivAt_Sq_α : ∀ q a t, HasDerivAt (fun b => Sq q b t) (Sqα q a t) a
  hasDerivAt_St_α : ∀ q a t, HasDerivAt (fun b => St q b t) (Sαt q a t) a
  hasDerivAt_St_q : ∀ q a t, HasDerivAt (fun x => St x a t) (Sqt q a t) q
  /-- Completeness: `∂²S/∂q∂α ≠ 0`. -/
  Sqα_ne : ∀ q a t, Sqα q a t ≠ 0

namespace CompleteIntegral

variable {H : TimeHamiltonian} (C : CompleteIntegral H)

/-- The Hamilton–Jacobi equation differentiated in `α`: `∂_α∂ₜS + H_p ∂_α∂_qS = 0`. -/
theorem hj_α (q a t : ℝ) : C.Sαt q a t + H.Hp q (C.Sq q a t) t * C.Sqα q a t = 0 := by
  have h1 := (H.hasFDerivAt q (C.Sq q a t) t).comp_hasDerivAt a
    ((hasDerivAt_const a q).prodMk (C.hasDerivAt_Sq_α q a t))
  have h := (C.hasDerivAt_St_α q a t).add h1
  have h0 : HasDerivAt (fun b => C.St q b t + H.H q (C.Sq q b t) t) 0 a := by
    simp only [C.hj]
    exact hasDerivAt_const a 0
  have := h.unique h0
  simpa using this

/-- The Hamilton–Jacobi equation differentiated in `q`: `∂_q∂ₜS + H_q + H_p ∂²_qS = 0`. -/
theorem hj_q (q a t : ℝ) :
    C.Sqt q a t + (H.Hq q (C.Sq q a t) t + H.Hp q (C.Sq q a t) t * C.Sqq q a t) = 0 := by
  have hSq : HasDerivAt (fun x => C.Sq x a t) (C.Sqq q a t) q := by
    have h := HamiltonJacobi.hasDerivAt_comp₂ (F := fun x s => C.Sq x a s)
      (C.hasFDerivAt_Sq q a t) (hasDerivAt_id q) (hasDerivAt_const q t)
    simpa using h
  have h1 := (H.hasFDerivAt q (C.Sq q a t) t).comp_hasDerivAt q ((hasDerivAt_id q).prodMk hSq)
  have h := (C.hasDerivAt_St_q q a t).add h1
  have h0 : HasDerivAt (fun x => C.St x a t + H.H x (C.Sq x a t) t) 0 q := by
    simp only [C.hj]
    exact hasDerivAt_const q 0
  have := h.unique h0
  simpa using this

/-- **Jacobi's theorem.** Let `S(q, α, t)` be a complete integral of the Hamilton–Jacobi
equation and let `q(t)` be a differentiable curve with `∂_αS(q(t), α, t) = β` constant. Then
`q(t)` together with `p(t) = ∂_qS(q(t), α, t)` solves Hamilton's equations
`q̇ = H_p(q, p, t)`, `ṗ = -H_q(q, p, t)`. -/
theorem jacobi (a β : ℝ) {q v : ℝ → ℝ} (hq : ∀ t, HasDerivAt q (v t) t)
    (hβ : ∀ t, C.Sα (q t) a t = β) (t : ℝ) :
    HasDerivAt q (H.Hp (q t) (C.Sq (q t) a t) t) t ∧
      HasDerivAt (fun s => C.Sq (q s) a s) (-H.Hq (q t) (C.Sq (q t) a t) t) t := by
  -- differentiate `∂_αS(q(t), α, t) = β` in `t`
  have hg := HamiltonJacobi.hasDerivAt_comp₂ (F := fun x s => C.Sα x a s)
    (C.hasFDerivAt_Sα (q t) a t) (hq t) (hasDerivAt_id t)
  have hg0 : HasDerivAt (fun s => C.Sα (q s) a s) 0 t := by
    simp only [hβ]
    exact hasDerivAt_const t β
  have e1 := hg.unique hg0
  have e2 := C.hj_α (q t) a t
  have hv : v t = H.Hp (q t) (C.Sq (q t) a t) t := by
    have hne := C.Sqα_ne (q t) a t
    apply mul_left_cancel₀ hne
    simp only [mul_one] at e1
    linear_combination e1 - e2
  refine ⟨hv ▸ hq t, ?_⟩
  have hp := HamiltonJacobi.hasDerivAt_comp₂ (F := fun x s => C.Sq x a s)
    (C.hasFDerivAt_Sq (q t) a t) (hq t) (hasDerivAt_id t)
  refine hp.congr_deriv ?_
  have e3 := C.hj_q (q t) a t
  rw [hv]
  linear_combination e3

end CompleteIntegral

/-- The **harmonic oscillator** `H(q, p) = p²/(2m) + mω²q²/2` with mass `m > 0` and angular
frequency `ω > 0`, to be described in action–angle variables `(θ, I)`. -/
structure ActionAngle where
  m : ℝ
  ω : ℝ
  m_pos : 0 < m
  ω_pos : 0 < ω

namespace ActionAngle

variable (A : ActionAngle)

/-- The Hamiltonian `H(q, p) = p²/(2m) + mω²q²/2`. -/
def hamiltonian (q p : ℝ) : ℝ := p ^ 2 / (2 * A.m) + A.m * A.ω ^ 2 * q ^ 2 / 2

/-- The amplitude `√(2I/(mω))` of the position at action `I`. -/
def amp (I : ℝ) : ℝ := √(2 * I / (A.m * A.ω))

/-- The amplitude `√(2Imω)` of the momentum at action `I`. -/
def mom (I : ℝ) : ℝ := √(2 * I * A.m * A.ω)

/-- The position `q(θ, I) = √(2I/(mω)) sin θ`. -/
def q (I θ : ℝ) : ℝ := A.amp I * sin θ

/-- The momentum `p(θ, I) = √(2Imω) cos θ`. -/
def p (I θ : ℝ) : ℝ := A.mom I * cos θ

theorem mω_pos : 0 < A.m * A.ω := mul_pos A.m_pos A.ω_pos

/-- `(√(2I/(mω)))² = 2I/(mω)`. -/
theorem amp_sq {I : ℝ} (hI : 0 ≤ I) : A.amp I ^ 2 = 2 * I / (A.m * A.ω) :=
  sq_sqrt (div_nonneg (mul_nonneg zero_le_two hI) A.mω_pos.le)

/-- `√(2Imω) = mω √(2I/(mω))`. -/
theorem mom_eq (I : ℝ) : A.mom I = A.m * A.ω * A.amp I := by
  have h := A.mω_pos
  rw [mom, amp, ← sqrt_sq h.le, ← sqrt_mul (sq_nonneg _), sqrt_sq h.le]
  congr 1
  field_simp

/-- `√(2I/(mω)) · √(2Imω) = 2I`. -/
theorem amp_mul_mom {I : ℝ} (hI : 0 ≤ I) : A.amp I * A.mom I = 2 * I := by
  have h := A.mω_pos
  rw [A.mom_eq I, show A.amp I * (A.m * A.ω * A.amp I) = A.m * A.ω * A.amp I ^ 2 by ring,
    A.amp_sq hI]
  field_simp
  exact mul_div_cancel_left₀ I h.ne'

/-- In action–angle variables the Hamiltonian is `H = ωI`. -/
theorem hamiltonian_eq {I : ℝ} (hI : 0 ≤ I) (θ : ℝ) :
    A.hamiltonian (A.q I θ) (A.p I θ) = A.ω * I := by
  have hm := A.m_pos.ne'
  have hω := A.ω_pos.ne'
  have hs := sin_sq_add_cos_sq θ
  simp only [hamiltonian, q, p, mul_pow, A.mom_eq I, A.amp_sq hI]
  field_simp
  linear_combination I * hs

/-- The action is `I = E/ω`, with `E` the energy. -/
theorem action_eq {I : ℝ} (hI : 0 ≤ I) (θ : ℝ) :
    I = A.hamiltonian (A.q I θ) (A.p I θ) / A.ω := by
  rw [A.hamiltonian_eq hI]
  field_simp [A.ω_pos.ne']

/-- `∂q/∂θ = √(2I/(mω)) cos θ`. -/
theorem hasDerivAt_q_θ (I θ : ℝ) : HasDerivAt (A.q I) (A.amp I * cos θ) θ :=
  (hasDerivAt_sin θ).const_mul _

/-- `∂p/∂θ = -√(2Imω) sin θ`. -/
theorem hasDerivAt_p_θ (I θ : ℝ) : HasDerivAt (A.p I) (-A.mom I * sin θ) θ := by
  have h := (hasDerivAt_cos θ).const_mul (A.mom I)
  exact h.congr_deriv (by ring)

/-- `∂q/∂I = √(2I/(mω))/(2I) · sin θ` for `I > 0`. -/
theorem hasDerivAt_q_I {I : ℝ} (hI : 0 < I) (θ : ℝ) :
    HasDerivAt (fun J => A.q J θ) (A.amp I / (2 * I) * sin θ) I := by
  have h := A.mω_pos
  have hf : HasDerivAt (fun J => 2 * J / (A.m * A.ω)) (2 / (A.m * A.ω)) I := by
    simpa using ((hasDerivAt_id I).const_mul 2).div_const (A.m * A.ω)
  have ha := (hf.sqrt (div_pos (by linarith) h).ne').mul_const (sin θ)
  have hpos : 0 < A.amp I := sqrt_pos.mpr (div_pos (by linarith) h)
  have hsq : A.amp I ^ 2 * (A.m * A.ω) = 2 * I := by
    rw [A.amp_sq hI.le]; field_simp; exact div_self h.ne'
  refine ha.congr_deriv ?_
  change 2 / (A.m * A.ω) / (2 * A.amp I) * sin θ = _
  congr 1
  rw [div_div, div_eq_div_iff (by positivity) (by linarith)]
  linear_combination (-2) * hsq

/-- `∂p/∂I = √(2Imω)/(2I) · cos θ` for `I > 0`. -/
theorem hasDerivAt_p_I {I : ℝ} (hI : 0 < I) (θ : ℝ) :
    HasDerivAt (fun J => A.p J θ) (A.mom I / (2 * I) * cos θ) I := by
  have h := A.mω_pos
  have hf : HasDerivAt (fun J => 2 * J * A.m * A.ω) (2 * A.m * A.ω) I := by
    simpa [mul_assoc] using ((hasDerivAt_id I).const_mul 2).mul_const (A.m * A.ω)
  have hpos' : 0 < 2 * I * A.m * A.ω := by
    have := mul_pos hI h; linarith [show 2 * I * A.m * A.ω = 2 * (I * (A.m * A.ω)) by ring]
  have ha := (hf.sqrt hpos'.ne').mul_const (cos θ)
  have hpos : 0 < A.mom I := sqrt_pos.mpr hpos'
  have hsq : A.mom I ^ 2 = 2 * I * A.m * A.ω := sq_sqrt hpos'.le
  refine ha.congr_deriv ?_
  change 2 * A.m * A.ω / (2 * A.mom I) * cos θ = _
  congr 1
  rw [div_eq_div_iff (by positivity) (by linarith)]
  linear_combination (-2) * hsq

/-- The **Jacobian matrix** of `(θ, I) ↦ (q, p)`: rows `q`, `p`; columns `∂/∂θ`, `∂/∂I`. -/
def jacobian (I θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A.amp I * cos θ, A.amp I / (2 * I) * sin θ;
    -A.mom I * sin θ, A.mom I / (2 * I) * cos θ]

/-- **Area preservation**: the map `(θ, I) ↦ (q, p)` has Jacobian determinant `1`, i.e.
`dq ∧ dp = dθ ∧ dI` and `(θ, I)` are canonical coordinates. -/
theorem det_jacobian {I : ℝ} (hI : 0 < I) (θ : ℝ) : (A.jacobian I θ).det = 1 := by
  have hs := sin_sq_add_cos_sq θ
  have hab := A.amp_mul_mom hI.le
  rw [jacobian, Matrix.det_fin_two_of]
  field_simp
  linear_combination (A.amp I * A.mom I) * hs + hab

/-- **Hamilton's equations in action–angle variables.** For `K(θ, I) = ωI` we have
`∂K/∂I = ω` and `∂K/∂θ = 0`, so the linear flow `θ(t) = θ₀ + ωt`, `I(t) = I` solves
`θ̇ = ∂K/∂I`, `İ = -∂K/∂θ`. -/
theorem hamilton_actionAngle (θ₀ I t : ℝ) :
    HasDerivAt (fun J => A.ω * J) A.ω I ∧ HasDerivAt (fun _ : ℝ => A.ω * I) 0 θ₀ ∧
      HasDerivAt (fun s => θ₀ + A.ω * s) A.ω t ∧ HasDerivAt (fun _ : ℝ => I) (-0) t := by
  refine ⟨?_, hasDerivAt_const _ _, ?_, by simpa using hasDerivAt_const t I⟩
  · simpa using (hasDerivAt_id I).const_mul A.ω
  · simpa using ((hasDerivAt_id t).const_mul A.ω).const_add θ₀

/-- The position along the action–angle flow, `q(t) = √(2I/(mω)) sin(θ₀ + ωt)`. -/
def flowQ (θ₀ I t : ℝ) : ℝ := A.q I (θ₀ + A.ω * t)

/-- The momentum along the action–angle flow, `p(t) = √(2Imω) cos(θ₀ + ωt)`. -/
def flowP (θ₀ I t : ℝ) : ℝ := A.p I (θ₀ + A.ω * t)

/-- The action–angle flow solves Hamilton's equations of the oscillator,
`q̇ = p/m`, `ṗ = -mω²q`. -/
theorem flow_solves (I θ₀ t : ℝ) :
    HasDerivAt (A.flowQ θ₀ I) (A.flowP θ₀ I t / A.m) t ∧
      HasDerivAt (A.flowP θ₀ I) (-(A.m * A.ω ^ 2) * A.flowQ θ₀ I t) t := by
  have hθ : HasDerivAt (fun s => θ₀ + A.ω * s) A.ω t := by
    simpa using ((hasDerivAt_id t).const_mul A.ω).const_add θ₀
  have hm := A.m_pos.ne'
  constructor
  · have h := (A.hasDerivAt_q_θ I (θ₀ + A.ω * t)).comp t hθ
    refine h.congr_deriv ?_
    simp only [flowP, p, A.mom_eq I]
    field_simp
  · have h := (A.hasDerivAt_p_θ I (θ₀ + A.ω * t)).comp t hθ
    refine h.congr_deriv ?_
    simp only [flowQ, q, A.mom_eq I]
    ring

/-- The action–angle flow is the familiar solution
`q(t) = q(0) cos ωt + (q̇(0)/ω) sin ωt` with `q̇(0) = p(0)/m`. -/
theorem flow_eq_sol (I θ₀ t : ℝ) :
    A.flowQ θ₀ I t = A.flowQ θ₀ I 0 * cos (A.ω * t) +
      A.flowP θ₀ I 0 / A.m / A.ω * sin (A.ω * t) := by
  have hm := A.m_pos.ne'
  have hω := A.ω_pos.ne'
  simp only [flowQ, flowP, q, p, A.mom_eq I, mul_zero, add_zero, sin_add]
  field_simp

/-- The action–angle flow as a motion of the `Harmonic` oscillator with stiffness
`k = mω²`. -/
def toHarmonic (I θ₀ : ℝ) : Harmonic where
  m := A.m
  c := 0
  k := A.m * A.ω ^ 2
  m_pos := A.m_pos
  c_nonneg := le_rfl
  k_pos := mul_pos A.m_pos (pow_pos A.ω_pos 2)
  x := A.flowQ θ₀ I
  v := fun t => A.flowP θ₀ I t / A.m
  a := fun t => -A.ω ^ 2 * A.flowQ θ₀ I t
  hasDerivAt_x t := (A.flow_solves I θ₀ t).1
  hasDerivAt_v t := by
    have h := (A.flow_solves I θ₀ t).2.div_const A.m
    convert h using 1
    field_simp [A.m_pos.ne']
  eq t := by ring
  c_eq := rfl

/-- The frequency of the associated `Harmonic` oscillator is `ω`. -/
theorem toHarmonic_ω (I θ₀ : ℝ) : (A.toHarmonic I θ₀).ω = A.ω := by
  change √(A.m * A.ω ^ 2 / A.m) = A.ω
  rw [mul_div_cancel_left₀ _ A.m_pos.ne', sqrt_sq A.ω_pos.le]

/-- **Action as phase-space area**: `I = (1/2π) ∮ p dq`, the loop integral being computed with
the parametrization `θ ↦ (q(θ, I), p(θ, I))`, `θ ∈ [0, 2π]`. -/
theorem action_eq_area {I : ℝ} (hI : 0 ≤ I) :
    (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π, A.p I θ * (A.amp I * cos θ) = I := by
  have hfun : (fun θ => A.p I θ * (A.amp I * cos θ)) =
      fun θ => (A.amp I * A.mom I) * cos θ ^ 2 := by
    funext θ; simp only [p]; ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_cos_sq, A.amp_mul_mom hI]
  simp only [cos_two_pi, sin_two_pi, cos_zero, sin_zero]
  field_simp
  ring

end ActionAngle

end ClassicalMechanics
