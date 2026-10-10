import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Timoshenko beams: equations, boundary conditions, uniqueness

A Timoshenko beam has two kinematic fields, the deflection `w` and the cross-section rotation `θ`,
and accounts for shear deformation through the shear stiffness `κGA` (shear correction factor
`κ`, shear modulus `G`, area `A`). With bending moment `M = EI θ'` and shear force
`V = κGA (w' - θ)`, equilibrium under a transverse load `q` reads
([Reddy2007], §3.4; [TimoshenkoGere1997], §9.12)

* `EI θ'' + κGA (w' - θ) = 0` (moment balance, `M' + V = 0`),
* `κGA (w'' - θ') + q = 0` (force balance, `V' + q = 0`).

As `κGA → ∞` the shear strain `w' - θ` vanishes and the Euler–Bernoulli beam `EI w'''' = q` is
recovered (see `Beams/Timoshenko/Limit.lean`).

## Main results

* `TBeam.homogeneous_formula`: solutions of the homogeneous equations are explicit polynomials.
* `TBeam.simplySupported_unique`, `TBeam.cantilever_unique`: uniqueness of `C²` solutions.

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.4.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §9.12.
-/

open Set

namespace ContinuumMechanics.Beams

/-- A prismatic **Timoshenko beam**: length `L`, bending stiffness `EI`, shear stiffness `κGA`. -/
structure TBeam where
  /-- Length. -/
  L : ℝ
  /-- Bending stiffness `E I`. -/
  EI : ℝ
  /-- Shear stiffness `κ G A`. -/
  kGA : ℝ
  L_pos : 0 < L
  EI_pos : 0 < EI
  kGA_pos : 0 < kGA

namespace TBeam

variable (b : TBeam)

/-- The underlying Euler–Bernoulli beam (same length and bending stiffness). -/
def toEB : EBBeam := ⟨b.L, b.EI, b.L_pos, b.EI_pos⟩

/-- The **Timoshenko beam equations** on `[0, L]`. [Reddy2007], §3.4. -/
def Equations (q w θ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 b.L, b.EI * iteratedDeriv 2 θ x + b.kGA * (deriv w x - θ x) = 0 ∧
    b.kGA * (iteratedDeriv 2 w x - deriv θ x) + q x = 0

/-- Simply supported ends: `w = 0` and `M = EI θ' = 0` at `x = 0, L`. -/
def SimplySupported (w θ : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ deriv θ 0 = 0 ∧ w b.L = 0 ∧ deriv θ b.L = 0

/-- Cantilever clamped at `0` (`w = θ = 0`) and free at `L` with tip load `P`
(`M(L) = 0`, `V(L) = κGA (w'(L) - θ(L)) = P`). -/
def Cantilever (P : ℝ) (w θ : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ θ 0 = 0 ∧ deriv θ b.L = 0 ∧ b.kGA * (deriv w b.L - θ b.L) = P

/-! ### Homogeneous solutions -/

/-- **Homogeneous solution formula.** If `(w, θ)` are `C²` and solve the unloaded equations on
`[0, L]`, then with `V₀ = κGA (w'(0) - θ(0))` the shear force is constant and
`θ = θ₀ + θ'₀ x - V₀ x² / (2 EI)`, `w = w₀ + (θ₀ + V₀ / κGA) x + θ'₀ x² / 2 - V₀ x³ / (6 EI)`. -/
theorem homogeneous_formula {w θ : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (hθ : ContDiff ℝ 2 θ)
    (h : b.Equations (fun _ => 0) w θ) (x : ℝ) (hx : x ∈ Icc 0 b.L) :
    let V₀ := b.kGA * (deriv w 0 - θ 0)
    b.kGA * (deriv w x - θ x) = V₀ ∧
      deriv θ x = deriv θ 0 - V₀ / b.EI * x ∧
      θ x = θ 0 + deriv θ 0 * x - V₀ / b.EI * x ^ 2 / 2 ∧
      w x = w 0 + (θ 0 + V₀ / b.kGA) * x + deriv θ 0 * x ^ 2 / 2 - V₀ / b.EI * x ^ 3 / 6 := by
  intro V₀
  have hEI := b.EI_pos.ne'
  have hS := b.kGA_pos.ne'
  have dw : Differentiable ℝ w := hw.differentiable (by norm_num)
  have dθ : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have ddw : Differentiable ℝ (deriv w) := (hw.deriv' (n := 1)).differentiable (by norm_num)
  have ddθ : Differentiable ℝ (deriv θ) := (hθ.deriv' (n := 1)).differentiable (by norm_num)
  have i2 : ∀ f : ℝ → ℝ, ∀ y, iteratedDeriv 2 f y = deriv (deriv f) y := fun f y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- the shear force is constant
  have hV : ∀ y ∈ Icc 0 b.L, b.kGA * (deriv w y - θ y) = V₀ := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun _ => 0) (fun y hy => ?_)
      (fun y _ => hasDerivAt_const y V₀) rfl
    have := (((ddw y).hasDerivAt.sub (dθ y).hasDerivAt).const_mul b.kGA)
    convert this using 1
    have := (h y hy).2
    rw [i2] at this
    simpa using this.symm
  -- `θ'` is affine
  have hθ' : ∀ y ∈ Icc 0 b.L, deriv θ y = deriv θ 0 - V₀ / b.EI * y := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun _ => -(V₀ / b.EI)) (fun y hy => ?_)
      (fun y _ => ?_) (by simp)
    · have := (ddθ y).hasDerivAt
      convert this using 1
      have e := (h y hy).1
      rw [i2, hV y hy] at e
      field_simp
      linarith
    · have := (hasDerivAt_const y (deriv θ 0)).sub ((hasDerivAt_id y).const_mul (V₀ / b.EI))
      convert this using 1
      · ext z; simp [id]
      · simp
  -- `θ` is quadratic
  have hθq : ∀ y ∈ Icc 0 b.L, θ y = θ 0 + deriv θ 0 * y - V₀ / b.EI * y ^ 2 / 2 := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun y => deriv θ 0 - V₀ / b.EI * y)
      (fun y hy => ?_) (fun y _ => ?_) (by simp)
    · rw [← hθ' y hy]; exact (dθ y).hasDerivAt
    · have := (((hasDerivAt_id y).const_mul (deriv θ 0)).const_add (θ 0)).sub
        (((hasDerivAt_pow 2 y).const_mul (V₀ / b.EI)).div_const 2)
      convert this using 1
      · ext z; simp [id]
      · simp; ring
  -- `w` is cubic
  have hwc : ∀ y ∈ Icc 0 b.L, w y = w 0 + (θ 0 + V₀ / b.kGA) * y + deriv θ 0 * y ^ 2 / 2
      - V₀ / b.EI * y ^ 3 / 6 := by
    refine eqOn_Icc_of_hasDerivAt
      (F' := fun y => θ 0 + deriv θ 0 * y - V₀ / b.EI * y ^ 2 / 2 + V₀ / b.kGA)
      (fun y hy => ?_) (fun y _ => ?_) (by simp)
    · have e : deriv w y = θ 0 + deriv θ 0 * y - V₀ / b.EI * y ^ 2 / 2 + V₀ / b.kGA := by
        rw [← hθq y hy]
        have := hV y hy
        field_simp
        linarith
      rw [← e]; exact (dw y).hasDerivAt
    · have := (((((hasDerivAt_id y).const_mul (θ 0 + V₀ / b.kGA)).const_add (w 0)).add
        (((hasDerivAt_pow 2 y).const_mul (deriv θ 0)).div_const 2)).sub
        (((hasDerivAt_pow 3 y).const_mul (V₀ / b.EI)).div_const 6))
      convert this using 1
      · ext z; simp [id]
      · simp; ring
  exact ⟨hV x hx, hθ' x hx, hθq x hx, hwc x hx⟩

/-! ### Uniqueness -/

/-- The difference of two solutions with the same load solves the unloaded equations. -/
theorem equations_sub {q w₁ θ₁ w₂ θ₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ 2 w₁) (hθ₁ : ContDiff ℝ 2 θ₁)
    (hw₂ : ContDiff ℝ 2 w₂) (hθ₂ : ContDiff ℝ 2 θ₂)
    (h₁ : b.Equations q w₁ θ₁) (h₂ : b.Equations q w₂ θ₂) :
    b.Equations (fun _ => 0) (w₁ - w₂) (θ₁ - θ₂) := by
  intro x hx
  have s2 : ∀ {f g : ℝ → ℝ}, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      iteratedDeriv 2 (f - g) x = iteratedDeriv 2 f x - iteratedDeriv 2 g x :=
    fun hf hg => iteratedDeriv_sub hf.contDiffAt hg.contDiffAt
  have s1 : ∀ {f g : ℝ → ℝ}, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      deriv (f - g) x = deriv f x - deriv g x :=
    fun hf hg => deriv_sub (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)
  obtain ⟨a₁, b₁⟩ := h₁ x hx
  obtain ⟨a₂, b₂⟩ := h₂ x hx
  rw [s2 hθ₁ hθ₂, s1 hw₁ hw₂, s2 hw₁ hw₂, s1 hθ₁ hθ₂, Pi.sub_apply]
  refine ⟨?_, ?_⟩
  · linear_combination a₁ - a₂
  · linear_combination b₁ - b₂

/-- **Uniqueness** for the simply supported Timoshenko beam. -/
theorem simplySupported_unique {q w₁ θ₁ w₂ θ₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ 2 w₁)
    (hθ₁ : ContDiff ℝ 2 θ₁) (hw₂ : ContDiff ℝ 2 w₂) (hθ₂ : ContDiff ℝ 2 θ₂)
    (h₁ : b.Equations q w₁ θ₁) (h₂ : b.Equations q w₂ θ₂)
    (bc₁ : b.SimplySupported w₁ θ₁) (bc₂ : b.SimplySupported w₂ θ₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x ∧ θ₁ x = θ₂ x := by
  have hw : ContDiff ℝ 2 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hθ : ContDiff ℝ 2 (θ₁ - θ₂) := ContDiff.sub hθ₁ hθ₂
  have H := b.homogeneous_formula hw hθ (b.equations_sub hw₁ hθ₁ hw₂ hθ₂ h₁ h₂)
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  have d1 : ∀ y, deriv (θ₁ - θ₂) y = deriv θ₁ y - deriv θ₂ y := fun y =>
    deriv_sub (hθ₁.differentiable (by norm_num) y) (hθ₂.differentiable (by norm_num) y)
  obtain ⟨-, eθ'L, -, ewL⟩ := H b.L hL
  set V₀ := b.kGA * (deriv (w₁ - w₂) 0 - (θ₁ - θ₂) 0)
  have w0 : (w₁ - w₂) 0 = 0 := by simp [bc₁.1, bc₂.1]
  have t0 : deriv (θ₁ - θ₂) 0 = 0 := by rw [d1, bc₁.2.1, bc₂.2.1, sub_self]
  have wL : (w₁ - w₂) b.L = 0 := by simp [bc₁.2.2.1, bc₂.2.2.1]
  have tL : deriv (θ₁ - θ₂) b.L = 0 := by rw [d1, bc₁.2.2.2, bc₂.2.2.2, sub_self]
  have hEI := b.EI_pos.ne'
  have hS := b.kGA_pos.ne'
  have hV : V₀ = 0 := by
    rw [tL, t0] at eθ'L
    have : V₀ / b.EI * b.L = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hEI
    · exact absurd h b.L_pos.ne'
  have hθ0 : (θ₁ - θ₂) 0 = 0 := by
    rw [w0, wL, t0, hV] at ewL
    simp only [zero_div, add_zero, zero_mul, sub_zero, zero_add] at ewL
    rcases mul_eq_zero.mp ewL.symm with h | h
    · exact h
    · exact absurd h b.L_pos.ne'
  intro x hx
  obtain ⟨-, -, eθ, ew⟩ := H x hx
  rw [hθ0, t0, hV] at eθ
  rw [w0, hθ0, t0, hV] at ew
  simp only [zero_div, add_zero, zero_mul, sub_zero, Pi.sub_apply, sub_eq_zero] at eθ ew
  exact ⟨ew, eθ⟩

/-- **Uniqueness** for the Timoshenko cantilever with tip load. -/
theorem cantilever_unique {q w₁ θ₁ w₂ θ₂ : ℝ → ℝ} {P : ℝ} (hw₁ : ContDiff ℝ 2 w₁)
    (hθ₁ : ContDiff ℝ 2 θ₁) (hw₂ : ContDiff ℝ 2 w₂) (hθ₂ : ContDiff ℝ 2 θ₂)
    (h₁ : b.Equations q w₁ θ₁) (h₂ : b.Equations q w₂ θ₂)
    (bc₁ : b.Cantilever P w₁ θ₁) (bc₂ : b.Cantilever P w₂ θ₂) :
    ∀ x ∈ Icc 0 b.L, w₁ x = w₂ x ∧ θ₁ x = θ₂ x := by
  have hw : ContDiff ℝ 2 (w₁ - w₂) := ContDiff.sub hw₁ hw₂
  have hθ : ContDiff ℝ 2 (θ₁ - θ₂) := ContDiff.sub hθ₁ hθ₂
  have H := b.homogeneous_formula hw hθ (b.equations_sub hw₁ hθ₁ hw₂ hθ₂ h₁ h₂)
  have hL : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  have d1 : ∀ {f g : ℝ → ℝ}, ContDiff ℝ 2 f → ContDiff ℝ 2 g → ∀ y,
      deriv (f - g) y = deriv f y - deriv g y := fun hf hg y =>
    deriv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  obtain ⟨eVL, eθ'L, -, -⟩ := H b.L hL
  set V₀ := b.kGA * (deriv (w₁ - w₂) 0 - (θ₁ - θ₂) 0)
  have w0 : (w₁ - w₂) 0 = 0 := by simp [bc₁.1, bc₂.1]
  have θ0 : (θ₁ - θ₂) 0 = 0 := by simp [bc₁.2.1, bc₂.2.1]
  have tL : deriv (θ₁ - θ₂) b.L = 0 := by rw [d1 hθ₁ hθ₂, bc₁.2.2.1, bc₂.2.2.1, sub_self]
  have hEI := b.EI_pos.ne'
  have hV : V₀ = 0 := by
    rw [← eVL, d1 hw₁ hw₂, Pi.sub_apply]
    have := bc₁.2.2.2.trans bc₂.2.2.2.symm
    linear_combination this
  have t0 : deriv (θ₁ - θ₂) 0 = 0 := by rw [tL, hV] at eθ'L; simpa using eθ'L.symm
  intro x hx
  obtain ⟨-, -, eθ, ew⟩ := H x hx
  rw [θ0, t0, hV] at eθ
  rw [w0, θ0, t0, hV] at ew
  simp only [zero_div, add_zero, zero_mul, sub_zero, Pi.sub_apply, sub_eq_zero] at eθ ew
  exact ⟨ew, eθ⟩

end TBeam

end ContinuumMechanics.Beams
