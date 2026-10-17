import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Beams on an elastic (Winkler) foundation

A beam of bending stiffness `EI > 0` resting on a **Winkler foundation** of modulus `k > 0`
(the foundation reacts with a distributed force `-k w` proportional to the local deflection)
under a transverse load `q` satisfies

`EI w'''' + k w = q`

([Hetenyi1946], §§1–2; [TimoshenkoGere1997], §10.9). With the **characteristic parameter**
`β = (k / (4 EI))^{1/4}` (so `4 EI β⁴ = k`) the homogeneous equation reads
`w'''' + 4 β⁴ w = 0`, whose solutions are spanned by `e^{±βx} cos βx`, `e^{±βx} sin βx`.

Deflection `w` is positive in the direction of the load; the bending moment is
`M = -EI w''` and the shear force is `V = -EI w'''` (as in `EBBeam`).

## Main results

* `Winkler.iteratedDeriv_four_expTrig`: `(e^{sβx}(A cos βx + B sin βx))'''' = -4β⁴ (…)` for
  `s = ±1`; hence `Winkler.homSol_solves` (the four-parameter family
  `e^{βx}(C₁ cos βx + C₂ sin βx) + e^{-βx}(C₃ cos βx + C₄ sin βx)` solves `EI w'''' + k w = 0`)
  and `Winkler.exp_cos_solves` etc. for the four basic functions.
* **Infinite beam under a point load** `P` at `x = 0` (Hetényi): the half-line deflection
  `Winkler.pointLoad = (Pβ/(2k)) e^{-βx}(cos βx + sin βx)` solves the homogeneous equation
  (`Winkler.pointLoad_solves`), has zero slope at the load (`Winkler.pointLoad_slope_zero`), the
  shear condition `V(0⁺) = -EI w'''(0⁺) = -P/2` (`Winkler.pointLoad_shear`; half the load is
  carried by each side), and decays at infinity (`Winkler.tendsto_pointLoad_atTop`).
  The maximum deflection is `w(0) = Pβ/(2k)` (`Winkler.pointLoad_zero`,
  `Winkler.abs_pointLoad_le`), the maximum moment is `M(0) = P/(4β)` (`Winkler.moment_zero`,
  `Winkler.abs_moment_le`), and the deflection is positive on `[0, 3π/(4β))`, vanishes at
  `3π/(4β)` and is negative just beyond (`Winkler.pointLoad_pos`,
  `Winkler.pointLoad_first_zero`, `Winkler.pointLoad_neg`).
* **Uniform load**: the constant `w = q/k` solves `EI w'''' + k w = q`
  (`Winkler.uniform_solves`), and so does `q/k` plus any homogeneous solution
  (`Winkler.uniform_add_homSol_solves`).

## References

* [Hetenyi1946] M. Hetényi, *Beams on Elastic Foundation*, University of Michigan Press, 1946.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §10.9.
* [Timoshenko1956] S. P. Timoshenko, *Strength of Materials, Part II*, 3rd ed., Ch. I.
-/

open Set Real Filter Topology
open scoped Real

noncomputable section

namespace ContinuumMechanics.Beams.Winkler

/-! ### The equation and the characteristic parameter -/

/-- The **Winkler beam equation** `EI w'''' + k w = q` on a set `S`. -/
def Equation (EI k : ℝ) (q w : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, EI * iteratedDeriv 4 w x + k * w x = q x

/-- The **characteristic parameter** `β = (k / (4 EI))^{1/4}` of a beam on a Winkler
foundation (units of inverse length). -/
def beta (EI k : ℝ) : ℝ := (k / (4 * EI)) ^ (1 / 4 : ℝ)

/-- The characteristic parameter is positive. -/
theorem beta_pos {EI k : ℝ} (hEI : 0 < EI) (hk : 0 < k) : 0 < beta EI k := by
  unfold beta
  positivity

/-- The defining identity `4 EI β⁴ = k` of the characteristic parameter. -/
theorem four_mul_beta_pow {EI k : ℝ} (hEI : 0 < EI) (hk : 0 < k) :
    4 * EI * beta EI k ^ 4 = k := by
  unfold beta
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  field_simp

/-! ### Homogeneous solutions -/

/-- The function `e^{sβx}(A cos βx + B sin βx)` (used with `s = ±1`). -/
def expTrig (s β A B : ℝ) (x : ℝ) : ℝ := exp (s * β * x) * (A * cos (β * x) + B * sin (β * x))

/-- Pointwise derivative of `expTrig`: it is again of this form. -/
theorem hasDerivAt_expTrig (s β A B x : ℝ) :
    HasDerivAt (expTrig s β A B) (expTrig s β (β * (s * A + B)) (β * (s * B - A)) x) x := by
  have he : HasDerivAt (fun y => exp (s * β * y)) (exp (s * β * x) * (s * β)) x := by
    simpa using ((hasDerivAt_id x).const_mul (s * β)).exp
  have hc := ((hasDerivAt_id x).const_mul β).cos
  have hs := ((hasDerivAt_id x).const_mul β).sin
  have := he.mul ((hc.const_mul A).add (hs.const_mul B))
  refine this.congr_deriv ?_
  simp only [expTrig, id, Pi.add_apply]
  ring

/-- Derivative of `expTrig`. -/
theorem deriv_expTrig (s β A B : ℝ) :
    deriv (expTrig s β A B) = expTrig s β (β * (s * A + B)) (β * (s * B - A)) :=
  funext fun x => (hasDerivAt_expTrig s β A B x).deriv

/-- `expTrig` is smooth. -/
theorem contDiff_expTrig (s β A B : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (expTrig s β A B) := by
  unfold expTrig
  fun_prop

/-- For `s = ±1`, `(e^{sβx}(A cos βx + B sin βx))'''' = -4β⁴ e^{sβx}(A cos βx + B sin βx)`. -/
theorem iteratedDeriv_four_expTrig {s : ℝ} (hs : s = 1 ∨ s = -1) (β A B x : ℝ) :
    iteratedDeriv 4 (expTrig s β A B) x = -4 * β ^ 4 * expTrig s β A B x := by
  simp only [iteratedDeriv_succ', iteratedDeriv_zero, deriv_expTrig]
  rcases hs with rfl | rfl <;> simp only [expTrig] <;> ring

/-- The **general homogeneous solution**
`e^{βx}(C₁ cos βx + C₂ sin βx) + e^{-βx}(C₃ cos βx + C₄ sin βx)`. -/
def homSol (β C₁ C₂ C₃ C₄ : ℝ) : ℝ → ℝ := expTrig 1 β C₁ C₂ + expTrig (-1) β C₃ C₄

/-- `(homSol)'''' = -4β⁴ homSol`. -/
theorem iteratedDeriv_four_homSol (β C₁ C₂ C₃ C₄ x : ℝ) :
    iteratedDeriv 4 (homSol β C₁ C₂ C₃ C₄) x = -4 * β ^ 4 * homSol β C₁ C₂ C₃ C₄ x := by
  rw [homSol, iteratedDeriv_add (contDiff_expTrig _ _ _ _).contDiffAt
    (contDiff_expTrig _ _ _ _).contDiffAt, Pi.add_apply,
    iteratedDeriv_four_expTrig (Or.inl rfl), iteratedDeriv_four_expTrig (Or.inr rfl)]
  ring

/-- **(a)** With `4 EI β⁴ = k`, every `homSol` solves the homogeneous Winkler equation
`EI w'''' + k w = 0` on all of `ℝ`. -/
theorem homSol_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) (C₁ C₂ C₃ C₄ : ℝ) :
    Equation EI k (fun _ => 0) (homSol β C₁ C₂ C₃ C₄) univ := by
  intro x _
  rw [iteratedDeriv_four_homSol, ← hβ]
  ring

/-- With `4 EI β⁴ = k`, each `expTrig (±1) β A B` solves `EI w'''' + k w = 0`. -/
theorem expTrig_solves {EI k β s : ℝ} (hβ : 4 * EI * β ^ 4 = k) (hs : s = 1 ∨ s = -1)
    (A B : ℝ) : Equation EI k (fun _ => 0) (expTrig s β A B) univ := by
  intro x _
  rw [iteratedDeriv_four_expTrig hs, ← hβ]
  ring

/-- **(a)** `e^{βx} cos βx` solves the homogeneous Winkler equation. -/
theorem exp_cos_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) :
    Equation EI k (fun _ => 0) (fun x => exp (β * x) * cos (β * x)) univ := by
  have := expTrig_solves hβ (Or.inl rfl) 1 0
  convert this using 2 with x
  simp [expTrig]

/-- **(a)** `e^{βx} sin βx` solves the homogeneous Winkler equation. -/
theorem exp_sin_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) :
    Equation EI k (fun _ => 0) (fun x => exp (β * x) * sin (β * x)) univ := by
  have := expTrig_solves hβ (Or.inl rfl) 0 1
  convert this using 2 with x
  simp [expTrig]

/-- **(a)** `e^{-βx} cos βx` solves the homogeneous Winkler equation. -/
theorem exp_neg_cos_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) :
    Equation EI k (fun _ => 0) (fun x => exp (-(β * x)) * cos (β * x)) univ := by
  have := expTrig_solves hβ (Or.inr rfl) 1 0
  convert this using 2 with x
  simp [expTrig]

/-- **(a)** `e^{-βx} sin βx` solves the homogeneous Winkler equation. -/
theorem exp_neg_sin_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) :
    Equation EI k (fun _ => 0) (fun x => exp (-(β * x)) * sin (β * x)) univ := by
  have := expTrig_solves hβ (Or.inr rfl) 0 1
  convert this using 2 with x
  simp [expTrig]

/-- **Decay of edge disturbances**: for `β > 0` and `x ≥ 0`,
`|e^{-βx}(A cos βx + B sin βx)| ≤ (|A| + |B|) e^{-βx}`. -/
theorem abs_expTrig_neg_le (β A B x : ℝ) :
    |expTrig (-1) β A B x| ≤ (|A| + |B|) * exp (-(β * x)) := by
  have hc := abs_cos_le_one (β * x)
  have hs := abs_sin_le_one (β * x)
  rw [expTrig, abs_mul, abs_of_pos (exp_pos _), show -1 * β * x = -(β * x) by ring, mul_comm]
  gcongr
  calc |A * cos (β * x) + B * sin (β * x)|
      ≤ |A| * |cos (β * x)| + |B| * |sin (β * x)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |A| * 1 + |B| * 1 := by gcongr
    _ = |A| + |B| := by ring

/-- Decaying homogeneous solutions tend to zero: `e^{-βx}(A cos βx + B sin βx) → 0` as
`x → ∞` for `β > 0`. -/
theorem tendsto_expTrig_neg {β : ℝ} (hβ : 0 < β) (A B : ℝ) :
    Tendsto (expTrig (-1) β A B) atTop (𝓝 0) := by
  have h : Tendsto (fun x => (|A| + |B|) * exp (-(β * x))) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hβ)).const_mul (|A| + |B|)
  exact squeeze_zero_norm (fun x => abs_expTrig_neg_le β A B x) h

/-! ### Infinite beam under a point load (Hetényi) -/

/-- The deflection of an **infinite beam on a Winkler foundation under a point load** `P` at
`x = 0`, on the half-line `x ≥ 0`: `w(x) = (Pβ/(2k)) e^{-βx}(cos βx + sin βx)` (extended
evenly to `x < 0`). [Hetenyi1946], §9. -/
def pointLoad (P k β : ℝ) : ℝ → ℝ := expTrig (-1) β (P * β / (2 * k)) (P * β / (2 * k))

/-- Explicit form of `pointLoad`. -/
theorem pointLoad_apply (P k β x : ℝ) :
    pointLoad P k β x = P * β / (2 * k) * exp (-(β * x)) * (cos (β * x) + sin (β * x)) := by
  simp only [pointLoad, expTrig, neg_mul, one_mul]
  ring

/-- Derivatives of `pointLoad`: `w' = -2βc e^{-βx} sin βx`,
`w'' = -2β²c e^{-βx}(cos βx - sin βx)`, `w''' = 4β³c e^{-βx} cos βx`, `c = Pβ/(2k)`. -/
theorem iteratedDeriv_pointLoad (P k β x : ℝ) :
    iteratedDeriv 1 (pointLoad P k β) x =
        -(2 * β * (P * β / (2 * k))) * exp (-(β * x)) * sin (β * x) ∧
      iteratedDeriv 2 (pointLoad P k β) x =
        -(2 * β ^ 2 * (P * β / (2 * k))) * exp (-(β * x)) * (cos (β * x) - sin (β * x)) ∧
      iteratedDeriv 3 (pointLoad P k β) x =
        4 * β ^ 3 * (P * β / (2 * k)) * exp (-(β * x)) * cos (β * x) := by
  simp only [pointLoad, iteratedDeriv_succ', iteratedDeriv_zero, deriv_expTrig, expTrig,
    neg_mul, one_mul]
  refine ⟨by ring, by ring, by ring⟩

/-- **(b)** The point-load deflection solves the homogeneous Winkler equation (in particular on
`x > 0`). -/
theorem pointLoad_solves {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) (P : ℝ) :
    Equation EI k (fun _ => 0) (pointLoad P k β) (Ioi 0) :=
  fun x _ => expTrig_solves hβ (Or.inr rfl) _ _ x (mem_univ x)

/-- **(b)** Symmetry: the slope vanishes under the load, `w'(0) = 0`. -/
theorem pointLoad_slope_zero (P k β : ℝ) : iteratedDeriv 1 (pointLoad P k β) 0 = 0 := by
  rw [(iteratedDeriv_pointLoad P k β 0).1]
  simp

/-- **(b)** Shear condition: `V(0⁺) = -EI w'''(0⁺) = -P/2`, i.e. `EI w'''(0⁺) = P/2`; each half
of the beam carries half the load (the jump of `EI w'''` across the load is `P`). -/
theorem pointLoad_shear {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) (hk : 0 < k) (P : ℝ) :
    -(EI * iteratedDeriv 3 (pointLoad P k β) 0) = -(P / 2) := by
  rw [(iteratedDeriv_pointLoad P k β 0).2.2]
  simp only [mul_zero, neg_zero, exp_zero, cos_zero, mul_one]
  have hk' := hk.ne'
  field_simp
  rw [← hβ]
  ring

/-- **(b)** Maximum deflection at the load: `w(0) = Pβ/(2k)`. -/
theorem pointLoad_zero (P k β : ℝ) : pointLoad P k β 0 = P * β / (2 * k) := by
  simp [pointLoad_apply]

/-- `|cos y + sin y| ≤ e^y` for `y ≥ 0` (from `(cos y + sin y)² = 1 + sin 2y ≤ 1 + 2y`). -/
theorem abs_cos_add_sin_le_exp {y : ℝ} (hy : 0 ≤ y) : |cos y + sin y| ≤ exp y := by
  apply abs_le_of_sq_le_sq _ (exp_pos y).le
  have h1 := sin_le (by linarith : 0 ≤ 2 * y)
  have h2 := add_one_le_exp (2 * y)
  have h3 : exp (2 * y) = exp y ^ 2 := by rw [sq, ← exp_add]; ring_nf
  rw [sin_two_mul] at h1
  nlinarith [sin_sq_add_cos_sq y]

/-- `|cos y - sin y| ≤ e^y` for `y ≥ 0` (from `(cos y - sin y)² = 1 - sin 2y ≤ 1 + 2y`). -/
theorem abs_cos_sub_sin_le_exp {y : ℝ} (hy : 0 ≤ y) : |cos y - sin y| ≤ exp y := by
  apply abs_le_of_sq_le_sq _ (exp_pos y).le
  have h1 := neg_abs_le (sin (2 * y))
  have h1' := abs_sin_le_abs (x := 2 * y)
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * y)] at h1'
  have h2 := add_one_le_exp (2 * y)
  have h3 : exp (2 * y) = exp y ^ 2 := by rw [sq, ← exp_add]; ring_nf
  rw [sin_two_mul] at h1 h1'
  nlinarith [sin_sq_add_cos_sq y]

/-- **(b)** The deflection is largest under the load: `|w(x)| ≤ w(0) = Pβ/(2k)` for `x ≥ 0`
(`P ≥ 0`, `k, β > 0`). -/
theorem abs_pointLoad_le {P k β x : ℝ} (hP : 0 ≤ P) (hk : 0 < k) (hβ : 0 < β) (hx : 0 ≤ x) :
    |pointLoad P k β x| ≤ P * β / (2 * k) := by
  have hc : 0 ≤ P * β / (2 * k) := by positivity
  have h := abs_cos_add_sin_le_exp (mul_nonneg hβ.le hx)
  rw [pointLoad_apply, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos (exp_pos _)]
  calc P * β / (2 * k) * exp (-(β * x)) * |cos (β * x) + sin (β * x)|
      ≤ P * β / (2 * k) * exp (-(β * x)) * exp (β * x) := by gcongr
    _ = P * β / (2 * k) := by rw [mul_assoc, ← exp_add]; simp

/-- **(b)** The deflection decays at infinity: `w(x) → 0` as `x → ∞` (`β > 0`). -/
theorem tendsto_pointLoad_atTop {β : ℝ} (hβ : 0 < β) (P k : ℝ) :
    Tendsto (pointLoad P k β) atTop (𝓝 0) :=
  tendsto_expTrig_neg hβ _ _

/-- The bending moment `M = -EI w''` of the point-load solution:
`M(x) = (P/(4β)) e^{-βx}(cos βx - sin βx)`. -/
theorem moment_apply {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) (hk : 0 < k) (hβ0 : 0 < β)
    (P x : ℝ) :
    -(EI * iteratedDeriv 2 (pointLoad P k β) x) =
      P / (4 * β) * exp (-(β * x)) * (cos (β * x) - sin (β * x)) := by
  rw [(iteratedDeriv_pointLoad P k β x).2.1]
  have hk' := hk.ne'
  have hβ' := hβ0.ne'
  rw [← hβ] at hk' ⊢
  have hEI : EI ≠ 0 := by rintro rfl; simp at hk'
  field_simp

/-- **(b)** Maximum moment under the load: `M(0) = P/(4β)`. -/
theorem moment_zero {EI k β : ℝ} (hβ : 4 * EI * β ^ 4 = k) (hk : 0 < k) (hβ0 : 0 < β) (P : ℝ) :
    -(EI * iteratedDeriv 2 (pointLoad P k β) 0) = P / (4 * β) := by
  rw [moment_apply hβ hk hβ0]
  simp

/-- **(b)** The moment is largest under the load: `|M(x)| ≤ M(0) = P/(4β)` for `x ≥ 0`. -/
theorem abs_moment_le {EI k β P x : ℝ} (hβ : 4 * EI * β ^ 4 = k) (hk : 0 < k) (hβ0 : 0 < β)
    (hP : 0 ≤ P) (hx : 0 ≤ x) :
    |-(EI * iteratedDeriv 2 (pointLoad P k β) x)| ≤ P / (4 * β) := by
  have hc : 0 ≤ P / (4 * β) := by positivity
  have h := abs_cos_sub_sin_le_exp (mul_nonneg hβ0.le hx)
  rw [moment_apply hβ hk hβ0, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos (exp_pos _)]
  calc P / (4 * β) * exp (-(β * x)) * |cos (β * x) - sin (β * x)|
      ≤ P / (4 * β) * exp (-(β * x)) * exp (β * x) := by gcongr
    _ = P / (4 * β) := by rw [mul_assoc, ← exp_add]; simp

/-- `cos y + sin y = √2 sin(y + π/4)`. -/
theorem cos_add_sin_eq (y : ℝ) : cos y + sin y = √2 * sin (y + π / 4) := by
  rw [sin_add, sin_pi_div_four, cos_pi_div_four]
  have h2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  linear_combination (-(sin y + cos y) / 2) * h2

/-- **(b)** The deflection is positive (downward, with the load) on `0 ≤ x < 3π/(4β)`. -/
theorem pointLoad_pos {P k β x : ℝ} (hP : 0 < P) (hk : 0 < k) (hβ : 0 < β) (hx : 0 ≤ x)
    (hx' : x < 3 * π / (4 * β)) : 0 < pointLoad P k β x := by
  rw [pointLoad_apply, cos_add_sin_eq]
  have hbx : β * x < 3 * π / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hx'; linarith
  have := sin_pos_of_pos_of_lt_pi (x := β * x + π / 4) (by positivity) (by linarith)
  positivity

/-- **(b)** The deflection first vanishes at `x = 3π/(4β)`, the zero of `cos βx + sin βx`. -/
theorem pointLoad_first_zero {P k β : ℝ} (hβ : 0 < β) :
    pointLoad P k β (3 * π / (4 * β)) = 0 := by
  rw [pointLoad_apply, cos_add_sin_eq, show β * (3 * π / (4 * β)) + π / 4 = π by
    field_simp; ring, sin_pi]
  simp

/-- **(b)** Beyond the first zero the beam lifts off (negative deflection) on
`3π/(4β) < x < 7π/(4β)`: the deflection changes sign at `3π/(4β)`. -/
theorem pointLoad_neg {P k β x : ℝ} (hP : 0 < P) (hk : 0 < k) (hβ : 0 < β)
    (hx : 3 * π / (4 * β) < x) (hx' : x < 7 * π / (4 * β)) : pointLoad P k β x < 0 := by
  rw [pointLoad_apply, cos_add_sin_eq]
  have h1 : 3 * π / 4 < β * x := by
    rw [div_lt_iff₀ (by positivity)] at hx; linarith
  have h2 : β * x < 7 * π / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hx'; linarith
  have h := sin_pos_of_pos_of_lt_pi (x := β * x + π / 4 - π) (by linarith) (by linarith)
  rw [sin_sub_pi] at h
  have hc : 0 < P * β / (2 * k) * exp (-(β * x)) * √2 := by positivity
  nlinarith

/-! ### Uniform load -/

/-- **(c)** An infinite beam under a uniform load `q` sinks uniformly: `w = q/k` solves
`EI w'''' + k w = q` (no bending). -/
theorem uniform_solves {EI k : ℝ} (hk : k ≠ 0) (q : ℝ) :
    Equation EI k (fun _ => q) (fun _ => q / k) univ := by
  intro x _
  simp only [iteratedDeriv_const, OfNat.ofNat_ne_zero, ite_false]
  field_simp
  ring

/-- **(c)** `q/k` plus any homogeneous solution solves `EI w'''' + k w = q`. -/
theorem uniform_add_homSol_solves {EI k β : ℝ} (hk : k ≠ 0) (hβ : 4 * EI * β ^ 4 = k)
    (q C₁ C₂ C₃ C₄ : ℝ) :
    Equation EI k (fun _ => q) (fun x => q / k + homSol β C₁ C₂ C₃ C₄ x) univ := by
  intro x _
  rw [iteratedDeriv_const_add (by norm_num), iteratedDeriv_four_homSol, ← hβ]
  rw [← hβ] at hk
  have hEI : EI ≠ 0 := by rintro rfl; simp at hk
  have hβ0 : β ≠ 0 := by rintro rfl; simp at hk
  field_simp
  ring

end ContinuumMechanics.Beams.Winkler
