import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.IntermediateValue
import ContinuumMechanics.Beams.Rayleigh

/-!
# Column buckling beyond the pinned–pinned case

A column of length `L`, bending stiffness `EI`, under an axial compressive load `P = EI k²`
(`k > 0`) has lateral deflection `w` satisfying `EI w'''' + P w'' = 0`, i.e.
`w'''' + k² w'' = 0` ([TimoshenkoGere1961], §§2.1–2.4). Its general solution is
`w = A + B x + C cos(kx) + D sin(kx)`; each set of four homogeneous boundary conditions gives a
`4 × 4` linear system whose determinant is the **characteristic equation** in `kL`.

## Main results

* General solution (`EBBeam.genSol`): `EBBeam.genSol_bucklingEquation` (it solves the equation)
  and `EBBeam.eq_genSol_of_bucklingEquation` (every `C⁴` solution, with its first three
  derivatives, agrees with one on `[0, L]`).
* **Clamped–free (flagpole)**, with the shear condition `EI w'''(L) + P w'(L) = 0`:
  `EBBeam.clampedFree_iff` (buckling iff `cos kL = 0`), `EBBeam.clampedFree_mode`
  (`w = c (1 - cos kx)`), `EBBeam.clampedFree_critical_load` (`P_cr = π² EI / (4 L²)`).
* **Clamped–clamped**: `EBBeam.clampedClamped_iff` (buckling iff
  `2 (1 - cos kL) - kL sin kL = 0`), `EBBeam.clampedClamped_char_factor` (the factorisation
  `4 sin(kL/2) (sin(kL/2) - (kL/2) cos(kL/2))`), `EBBeam.clampedClamped_mode`
  (`c (1 - cos(2πx/L))` is a mode at `P = 4π² EI / L²`) and
  `EBBeam.clampedClamped_critical_load` (`P_cr = 4π² EI / L²`, effective length `L/2`).
* **Clamped–pinned**: `EBBeam.clampedPinned_iff` (buckling iff `sin kL = kL cos kL`, i.e.
  `tan kL = kL`); the lowest positive root `EBBeam.cpRoot` exists by the intermediate value
  theorem, is unique in `(π, 2π)` and satisfies `4.49 < cpRoot < 4.50`
  (`EBBeam.cpRoot_bounds`); `EBBeam.clampedPinned_critical_load`
  (`P_cr = cpRoot² EI / L²`), `EBBeam.clampedPinned_critical_load_bounds`
  (`20.16 EI/L² < P_cr < 20.25 EI/L²`) and `EBBeam.clampedPinned_effective_length`
  (`P_cr = π² EI / (K L)²` with `0.69 < K < 0.70`; the textbook `K ≈ 0.7` is approximate).
* **Imperfect column**: `EBBeam.imperfect_solves` (the additional deflection
  `P/(P_E - P) · a sin(πx/L)` solves `EI w'' + P (w + w₀) = 0`, `w(0) = w(L) = 0`),
  `EBBeam.imperfect_total` (total amplitude `a / (1 - P/P_E)`) and
  `EBBeam.tendsto_amplification` (it tends to `+∞` as `P → P_E⁻`).
* **Lateral–torsional buckling** (`LTBeam`): `LTBeam.buckles_iff` (a nontrivial sinusoidal
  pair exists iff `M² = (π/L)² EI_y GJ`) and `LTBeam.critical_moment`
  (`|M| = (π/L) √(EI_y GJ)`).

## References

* [TimoshenkoGere1961] S. P. Timoshenko, J. M. Gere, *Theory of Elastic Stability*, 2nd ed.,
  §§1.11, 2.1–2.4 (columns), §6.2 (lateral buckling of beams in pure bending).
-/

open Set Real Filter Topology
open scoped Real

namespace ContinuumMechanics.Beams

namespace EBBeam

/-! ### The general solution -/

/-- The **general solution** `A + B x + C cos(kx) + D sin(kx)` of `w'''' + k² w'' = 0`. -/
noncomputable def genSol (k A B C D : ℝ) : ℝ → ℝ :=
  fun x => A + B * x + C * cos (k * x) + D * sin (k * x)

/-- Pointwise derivative of the general solution. -/
theorem hasDerivAt_genSol (k A B C D x : ℝ) :
    HasDerivAt (genSol k A B C D) (genSol k B 0 (D * k) (-(C * k)) x) x := by
  have := (((hasDerivAt_id' x).const_mul B).const_add A).add
    ((hasDerivAt_cos_mul C k x).add (hasDerivAt_sin_mul D k x))
  convert this using 1
  · ext y; simp only [genSol, Pi.add_apply]; ring
  · simp only [genSol]; ring

/-- The derivative of a general solution is again of this form. -/
theorem deriv_genSol (k A B C D : ℝ) :
    deriv (genSol k A B C D) = genSol k B 0 (D * k) (-(C * k)) :=
  funext fun x => (hasDerivAt_genSol k A B C D x).deriv

/-- The general solution is smooth. -/
theorem contDiff_genSol (k A B C D : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (genSol k A B C D) := by
  unfold genSol
  fun_prop

/-- Iterated derivatives of the general solution. -/
theorem iteratedDeriv_genSol (k A B C D x : ℝ) :
    iteratedDeriv 1 (genSol k A B C D) x = B - C * k * sin (k * x) + D * k * cos (k * x) ∧
    iteratedDeriv 2 (genSol k A B C D) x = -(C * k ^ 2 * cos (k * x)) - D * k ^ 2 * sin (k * x) ∧
    iteratedDeriv 3 (genSol k A B C D) x = C * k ^ 3 * sin (k * x) - D * k ^ 3 * cos (k * x) ∧
    iteratedDeriv 4 (genSol k A B C D) x = C * k ^ 4 * cos (k * x) + D * k ^ 4 * sin (k * x) := by
  simp only [iteratedDeriv_succ', iteratedDeriv_zero, deriv_genSol]
  simp only [genSol]
  refine ⟨by ring, by ring, by ring, by ring⟩

variable (b : EBBeam)

/-- **(a)** The general solution solves the buckling equation `EI w'''' + P w'' = 0` when
`P = EI k²`. -/
theorem genSol_bucklingEquation {k P : ℝ} (hP : P = b.EI * k ^ 2) (A B C D : ℝ) :
    b.BucklingEquation P (genSol k A B C D) := by
  intro x _
  obtain ⟨-, h2, -, h4⟩ := iteratedDeriv_genSol k A B C D x
  rw [h2, h4, hP]
  ring

/-- Uniqueness for `v'''' + k² v'' = 0` with zero data at `0`: `v, v', v'', v'''` vanish on
`[0, L]`, by conservation of the energy `v'''² + k² v''²`. -/
theorem eq_zero_of_buckling_data {k : ℝ} (hk : k ≠ 0) {v : ℝ → ℝ} (hv : ContDiff ℝ 4 v)
    (h : ∀ x ∈ Icc 0 b.L, iteratedDeriv 4 v x + k ^ 2 * iteratedDeriv 2 v x = 0)
    (h0 : v 0 = 0) (h1 : iteratedDeriv 1 v 0 = 0) (h2 : iteratedDeriv 2 v 0 = 0)
    (h3 : iteratedDeriv 3 v 0 = 0) :
    ∀ x ∈ Icc 0 b.L, ∀ j ≤ 3, iteratedDeriv j v x = 0 := by
  have hD : ∀ j < 4, ∀ x, HasDerivAt (iteratedDeriv j v) (iteratedDeriv (j + 1) v x) x := by
    intro j hj x
    rw [iteratedDeriv_succ]
    exact ((hv.differentiable_iteratedDeriv j (by exact_mod_cast hj)) x).hasDerivAt
  let e := fun x => iteratedDeriv 3 v x ^ 2 + k ^ 2 * iteratedDeriv 2 v x ^ 2
  have he : ∀ x ∈ Icc 0 b.L, e x = e 0 := by
    refine eqOn_Icc_of_hasDerivAt (F' := fun _ => 0) (fun x hx => ?_)
      (fun x _ => hasDerivAt_const x (e 0)) rfl
    have := ((hD 3 (by norm_num) x).pow 2).add (((hD 2 (by norm_num) x).pow 2).const_mul (k ^ 2))
    convert this using 1
    have e4 := h x hx
    push_cast
    linear_combination (-2 * iteratedDeriv 3 v x) * e4
  have he0 : e 0 = 0 := by simp only [e, h2, h3]; ring
  have hk2 : 0 < k ^ 2 := by positivity
  have z2 : ∀ x ∈ Icc 0 b.L, iteratedDeriv 2 v x = 0 ∧ iteratedDeriv 3 v x = 0 := by
    intro x hx
    have := he x hx
    rw [he0] at this
    simp only [e] at this
    have a : k ^ 2 * iteratedDeriv 2 v x ^ 2 = 0 := by
      nlinarith [sq_nonneg (iteratedDeriv 3 v x),
        mul_nonneg hk2.le (sq_nonneg (iteratedDeriv 2 v x))]
    refine ⟨pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp a).resolve_left hk2.ne'), ?_⟩
    exact pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg (iteratedDeriv 3 v x)])
  have z1 : ∀ x ∈ Icc 0 b.L, iteratedDeriv 1 v x = 0 :=
    eqOn_Icc_of_hasDerivAt (F' := fun _ => 0)
      (fun x hx => by have := hD 1 (by norm_num) x; rwa [(z2 x hx).1] at this)
      (fun x _ => hasDerivAt_const x 0) h1
  have z0 : ∀ x ∈ Icc 0 b.L, iteratedDeriv 0 v x = 0 :=
    eqOn_Icc_of_hasDerivAt (F' := fun _ => 0)
      (fun x hx => by have := hD 0 (by norm_num) x; rwa [z1 x hx] at this)
      (fun x _ => hasDerivAt_const x 0) (by simpa using h0)
  intro x hx j hj
  interval_cases j
  · exact z0 x hx
  · exact z1 x hx
  · exact (z2 x hx).1
  · exact (z2 x hx).2

/-- **(a)** Every `C⁴` solution of `EI w'''' + P w'' = 0` (`P = EI k²`, `k ≠ 0`) is a general
solution `A + B x + C cos(kx) + D sin(kx)` on `[0, L]`, together with its first three
derivatives (so that boundary conditions at `0` and `L` transfer). -/
theorem eq_genSol_of_bucklingEquation {k P : ℝ} (hk : k ≠ 0) (hP : P = b.EI * k ^ 2)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) (h : b.BucklingEquation P w) :
    ∃ A B C D : ℝ, ∀ x ∈ Icc 0 b.L, ∀ j ≤ 3,
      iteratedDeriv j w x = iteratedDeriv j (genSol k A B C D) x := by
  refine ⟨w 0 - -iteratedDeriv 2 w 0 / k ^ 2,
    iteratedDeriv 1 w 0 - -iteratedDeriv 3 w 0 / k ^ 3 * k, -iteratedDeriv 2 w 0 / k ^ 2,
    -iteratedDeriv 3 w 0 / k ^ 3, fun x hx j hj => ?_⟩
  have hG : ContDiff ℝ 4 (genSol k (w 0 - -iteratedDeriv 2 w 0 / k ^ 2)
      (iteratedDeriv 1 w 0 - -iteratedDeriv 3 w 0 / k ^ 3 * k)
      (-iteratedDeriv 2 w 0 / k ^ 2) (-iteratedDeriv 3 w 0 / k ^ 3)) := contDiff_genSol _ _ _ _ _
  have s := iteratedDeriv_sub_apply hw hG
  have hEI := b.EI_pos.ne'
  have hv : ContDiff ℝ 4 (w - genSol k (w 0 - -iteratedDeriv 2 w 0 / k ^ 2)
      (iteratedDeriv 1 w 0 - -iteratedDeriv 3 w 0 / k ^ 3 * k)
      (-iteratedDeriv 2 w 0 / k ^ 2) (-iteratedDeriv 3 w 0 / k ^ 3)) := hw.sub hG
  have key := b.eq_zero_of_buckling_data hk hv ?_ ?_ ?_ ?_ ?_ x hx j hj
  · rw [s j (by omega)] at key; linarith
  · intro y hy
    rw [s 4 le_rfl, s 2 (by norm_num)]
    obtain ⟨-, g2, -, g4⟩ := iteratedDeriv_genSol k (w 0 - -iteratedDeriv 2 w 0 / k ^ 2)
      (iteratedDeriv 1 w 0 - -iteratedDeriv 3 w 0 / k ^ 3 * k)
      (-iteratedDeriv 2 w 0 / k ^ 2) (-iteratedDeriv 3 w 0 / k ^ 3) y
    rw [g2, g4]
    have e := h y hy
    rw [hP] at e
    have e' : b.EI * (iteratedDeriv 4 w y + k ^ 2 * iteratedDeriv 2 w y) = 0 := by
      linear_combination e
    linear_combination (mul_eq_zero.mp e').resolve_left hEI
  · simp [genSol]
  · rw [s 1 (by norm_num), (iteratedDeriv_genSol _ _ _ _ _ _).1]
    simp
  · rw [s 2 (by norm_num), (iteratedDeriv_genSol _ _ _ _ _ _).2.1]
    field_simp
    simp
  · rw [s 3 (by norm_num), (iteratedDeriv_genSol _ _ _ _ _ _).2.2.1]
    field_simp
    simp

/-- A general solution vanishing on `[0, L]` (`k ≠ 0`) has all coefficients zero. -/
theorem genSol_coeffs_eq_zero {k A B C D : ℝ} (hk : k ≠ 0)
    (h : ∀ x ∈ Icc 0 b.L, genSol k A B C D x = 0) : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hL := b.L_pos
  have hev : genSol k A B C D =ᶠ[𝓝 (b.L / 2)] fun _ => 0 := by
    filter_upwards [Icc_mem_nhds (by positivity : 0 < b.L / 2) (by linarith : b.L / 2 < b.L)]
      with x hx using h x hx
  have hd : ∀ n, iteratedDeriv n (genSol k A B C D) (b.L / 2) = 0 := fun n => by
    rw [(hev.iteratedDeriv n).eq_of_nhds, iteratedDeriv_fun_const_zero]
  obtain ⟨g1, g2, g3, -⟩ := iteratedDeriv_genSol k A B C D (b.L / 2)
  rw [hd] at g1 g2 g3
  have h0 := hd 0
  simp only [iteratedDeriv_zero, genSol] at h0
  have e2' : k ^ 2 * (C * cos (k * (b.L / 2)) + D * sin (k * (b.L / 2))) = 0 := by
    linear_combination g2
  have e3' : k ^ 3 * (C * sin (k * (b.L / 2)) - D * cos (k * (b.L / 2))) = 0 := by
    linear_combination -g3
  have e2 := (mul_eq_zero.mp e2').resolve_left (pow_ne_zero 2 hk)
  have e3 := (mul_eq_zero.mp e3').resolve_left (pow_ne_zero 3 hk)
  have hC : C = 0 := by
    linear_combination cos (k * (b.L / 2)) * e2 + sin (k * (b.L / 2)) * e3
      - C * sin_sq_add_cos_sq (k * (b.L / 2))
  have hD : D = 0 := by
    linear_combination sin (k * (b.L / 2)) * e2 - cos (k * (b.L / 2)) * e3
      - D * sin_sq_add_cos_sq (k * (b.L / 2))
  subst hC hD
  have hB : B = 0 := by linear_combination -g1
  subst hB
  refine ⟨by linear_combination h0, rfl, rfl, rfl⟩

/-- If `w` agrees with a general solution on `[0, L]` and is nonzero somewhere there, not all
coefficients vanish. -/
theorem coeffs_ne_zero_of_nontrivial {k A B C D : ℝ} {w : ℝ → ℝ}
    (hG : ∀ x ∈ Icc 0 b.L, ∀ j ≤ 3, iteratedDeriv j w x = iteratedDeriv j (genSol k A B C D) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 b.L) (hne : w x₀ ≠ 0) : ¬(A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0) := by
  rintro ⟨rfl, rfl, rfl, rfl⟩
  apply hne
  have := hG x₀ hx₀ 0 (by norm_num)
  simp only [iteratedDeriv_zero] at this
  rw [this]
  simp [genSol]

/-- The column **buckles** under the load `P` with boundary conditions `bc`: there is a
nontrivial `C⁴` solution of `EI w'''' + P w'' = 0` satisfying `bc`. -/
def Buckles (bc : (ℝ → ℝ) → Prop) (P : ℝ) : Prop :=
  ∃ w : ℝ → ℝ, ContDiff ℝ 4 w ∧ b.BucklingEquation P w ∧ bc w ∧ ∃ x ∈ Icc 0 b.L, w x ≠ 0

/-- **Critical loads from a characteristic equation**: if buckling under `P = EI k²` is
equivalent to `χ (kL)`, and `y > 0` is the least positive root of `χ`, then the least buckling
load is `y² EI / L²`. -/
theorem isLeast_of_char {bc : ℝ → (ℝ → ℝ) → Prop} {χ : ℝ → Prop}
    (hchar : ∀ k P : ℝ, 0 < k → P = b.EI * k ^ 2 → (b.Buckles (bc P) P ↔ χ (k * b.L)))
    {y : ℝ} (hy : 0 < y) (hχ : χ y) (hmin : ∀ z, 0 < z → χ z → y ≤ z) :
    IsLeast {P | 0 < P ∧ b.Buckles (bc P) P} (y ^ 2 * b.EI / b.L ^ 2) := by
  have hL := b.L_pos
  have hEI := b.EI_pos
  have hP : y ^ 2 * b.EI / b.L ^ 2 = b.EI * (y / b.L) ^ 2 := by field_simp
  refine ⟨⟨by positivity, (hchar (y / b.L) _ (by positivity) hP).mpr ?_⟩, ?_⟩
  · rwa [div_mul_cancel₀ _ hL.ne']
  · rintro P ⟨hP, hb⟩
    obtain ⟨k, hk, rfl⟩ : ∃ k, 0 < k ∧ P = b.EI * k ^ 2 :=
      ⟨√(P / b.EI), Real.sqrt_pos.mpr (div_pos hP hEI), by
        rw [Real.sq_sqrt (div_pos hP hEI).le]; field_simp⟩
    have := hmin _ (mul_pos hk hL) ((hchar k _ hk rfl).mp hb)
    have h2 : y ^ 2 ≤ (k * b.L) ^ 2 := pow_le_pow_left₀ hy.le this 2
    change y ^ 2 * b.EI / b.L ^ 2 ≤ b.EI * k ^ 2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hEI.le]

/-! ### Clamped–free column (flagpole) -/

/-- Clamped at `0`, free at `L` under the axial load `P`: `w(0) = w'(0) = 0`, zero moment
`w''(L) = 0` and zero transverse shear `EI w'''(L) + P w'(L) = 0` (the axial load follows the
deflected tip). [TimoshenkoGere1961], §2.1. -/
def ClampedFree (P : ℝ) (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ iteratedDeriv 1 w 0 = 0 ∧ iteratedDeriv 2 w b.L = 0 ∧
    b.EI * iteratedDeriv 3 w b.L + P * iteratedDeriv 1 w b.L = 0

/-- **Elimination** for the clamped–free column: every `C⁴` solution with these boundary
conditions is `c (1 - cos kx)` on `[0, L]` with `c cos kL = 0`. -/
theorem clampedFree_mode {k P : ℝ} (hk : 0 < k) (hP : P = b.EI * k ^ 2) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 4 w) (h : b.BucklingEquation P w) (hbc : b.ClampedFree P w) :
    ∃ c : ℝ, (∀ x ∈ Icc 0 b.L, w x = c * (1 - cos (k * x))) ∧ c * cos (k * b.L) = 0 := by
  obtain ⟨c0, c1, c2, c3⟩ := hbc
  obtain ⟨A, B, C, D, hG⟩ := b.eq_genSol_of_bucklingEquation hk.ne' hP hw h
  have hL := b.L_pos
  have m0 : (0 : ℝ) ∈ Icc 0 b.L := ⟨le_rfl, hL.le⟩
  have mL : b.L ∈ Icc 0 b.L := ⟨hL.le, le_rfl⟩
  have v0 := hG 0 m0 0 (by norm_num)
  simp only [iteratedDeriv_zero] at v0
  rw [c0] at v0
  rw [hG 0 m0 1 (by norm_num), (iteratedDeriv_genSol k A B C D 0).1] at c1
  rw [hG _ mL 2 (by norm_num), (iteratedDeriv_genSol k A B C D _).2.1] at c2
  rw [hG _ mL 3 (by norm_num), hG _ mL 1 (by norm_num), (iteratedDeriv_genSol k A B C D _).2.2.1,
    (iteratedDeriv_genSol k A B C D _).1] at c3
  simp only [genSol, mul_zero, cos_zero, sin_zero, mul_one, add_zero, sub_zero] at v0 c1
  have hB' : b.EI * k ^ 2 * B = 0 := by rw [hP] at c3; linear_combination c3
  have hB : B = 0 := (mul_eq_zero.mp hB').resolve_left (by have := b.EI_pos; positivity)
  have hD : D = 0 := by
    have : D * k = 0 := by linear_combination c1 - hB
    exact (mul_eq_zero.mp this).resolve_right hk.ne'
  subst hB hD
  refine ⟨-C, fun x hx => ?_, ?_⟩
  · have := hG x hx 0 (by norm_num)
    simp only [iteratedDeriv_zero] at this
    rw [this]
    simp only [genSol]
    linear_combination -v0
  · have : k ^ 2 * (C * cos (k * b.L)) = 0 := by linear_combination -c2
    linear_combination -((mul_eq_zero.mp this).resolve_left (by positivity))

/-- **(b) Clamped–free (flagpole) buckling**: a nontrivial solution exists iff `cos kL = 0`.
[TimoshenkoGere1961], §2.1. -/
theorem clampedFree_iff {k P : ℝ} (hk : 0 < k) (hP : P = b.EI * k ^ 2) :
    b.Buckles (b.ClampedFree P) P ↔ cos (k * b.L) = 0 := by
  have hL := b.L_pos
  constructor
  · rintro ⟨w, hw, h, hbc, x₀, hx₀, hne⟩
    obtain ⟨c, hc, hcos⟩ := b.clampedFree_mode hk hP hw h hbc
    by_contra hcos'
    apply hne
    rw [hc x₀ hx₀, (mul_eq_zero.mp hcos).resolve_right hcos', zero_mul]
  · intro hcos
    refine ⟨genSol k 1 0 (-1) 0, contDiff_genSol _ _ _ _ _, b.genSol_bucklingEquation hP _ _ _ _,
      ⟨by simp [genSol], ?_, ?_, ?_⟩, b.L, ⟨hL.le, le_rfl⟩, ?_⟩
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1]; simp
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).2.1, hcos]; ring
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).2.2.1, (iteratedDeriv_genSol _ _ _ _ _ _).1, hP]
      ring
    · simp [genSol, hcos]

/-- **Critical load of the flagpole**: `P_cr = π² EI / (4 L²)`, the Euler load of a pinned
column of effective length `2L`. [TimoshenkoGere1961], §2.1. -/
theorem clampedFree_critical_load :
    IsLeast {P | 0 < P ∧ b.Buckles (b.ClampedFree P) P} (π ^ 2 * b.EI / (4 * b.L ^ 2)) := by
  have key := b.isLeast_of_char (bc := b.ClampedFree) (χ := fun z => cos z = 0)
    (fun k P hk hP => b.clampedFree_iff hk hP) (y := π / 2) (by positivity) cos_pi_div_two
    (fun z hz hcz => by
      obtain ⟨n, rfl⟩ := Real.cos_eq_zero_iff.mp hcz
      have h1 : (0 : ℝ) < 2 * n + 1 := by
        by_contra hneg
        push Not at hneg
        have : (2 * n + 1) * π / 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg pi_pos.le)
            (by norm_num)
        linarith
      have hn : (-1 : ℤ) < n := by exact_mod_cast (by linarith : (-1 : ℝ) < n)
      have hn' : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
      nlinarith [pi_pos])
  convert key using 1
  ring

/-! ### Clamped–clamped column -/

/-- **(c) Clamped–clamped buckling**: a nontrivial solution exists iff the determinant
`2 (1 - cos kL) - kL sin kL` vanishes. [TimoshenkoGere1961], §2.4. -/
theorem clampedClamped_iff {k P : ℝ} (hk : 0 < k) (hP : P = b.EI * k ^ 2) :
    b.Buckles b.ClampedClamped P ↔ 2 * (1 - cos (k * b.L)) - k * b.L * sin (k * b.L) = 0 := by
  have hL := b.L_pos
  have m0 : (0 : ℝ) ∈ Icc 0 b.L := ⟨le_rfl, hL.le⟩
  have mL : b.L ∈ Icc 0 b.L := ⟨hL.le, le_rfl⟩
  constructor
  · rintro ⟨w, hw, h, ⟨c0, c1, c2, c3⟩, x₀, hx₀, hne⟩
    obtain ⟨A, B, C, D, hG⟩ := b.eq_genSol_of_bucklingEquation hk.ne' hP hw h
    have triv := b.coeffs_ne_zero_of_nontrivial hG hx₀ hne
    have v0 := hG 0 m0 0 (by norm_num)
    have vL := hG _ mL 0 (by norm_num)
    simp only [iteratedDeriv_zero] at v0 vL
    rw [c0] at v0
    rw [c2] at vL
    rw [hG 0 m0 1 (by norm_num), (iteratedDeriv_genSol k A B C D 0).1] at c1
    rw [hG _ mL 1 (by norm_num), (iteratedDeriv_genSol k A B C D _).1] at c3
    simp only [genSol, mul_zero, cos_zero, sin_zero, mul_one, add_zero, sub_zero] at v0 vL c1
    by_contra hdet
    have E1 : C * (cos (k * b.L) - 1) + D * (sin (k * b.L) - k * b.L) = 0 := by
      linear_combination -vL + v0 - b.L * c1
    have E2' : k * (-C * sin (k * b.L) + D * (cos (k * b.L) - 1)) = 0 := by
      linear_combination c3 - c1
    have E2 := (mul_eq_zero.mp E2').resolve_left hk.ne'
    have hC' : C * (2 * (1 - cos (k * b.L)) - k * b.L * sin (k * b.L)) = 0 := by
      linear_combination (cos (k * b.L) - 1) * E1 - (sin (k * b.L) - k * b.L) * E2
        - C * sin_sq_add_cos_sq (k * b.L)
    have hD' : D * (2 * (1 - cos (k * b.L)) - k * b.L * sin (k * b.L)) = 0 := by
      linear_combination sin (k * b.L) * E1 + (cos (k * b.L) - 1) * E2
        - D * sin_sq_add_cos_sq (k * b.L)
    have hC := (mul_eq_zero.mp hC').resolve_right hdet
    have hD := (mul_eq_zero.mp hD').resolve_right hdet
    subst hC hD
    exact triv ⟨by linear_combination -v0, by linear_combination c1, rfl, rfl⟩
  · intro hdet
    refine ⟨genSol k (-(sin (k * b.L) - k * b.L)) (-((1 - cos (k * b.L)) * k))
      (sin (k * b.L) - k * b.L) (1 - cos (k * b.L)), contDiff_genSol _ _ _ _ _,
      b.genSol_bucklingEquation hP _ _ _ _, ⟨by simp [genSol], ?_, ?_, ?_⟩, ?_⟩
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1]; simp
    · simp only [genSol]; ring
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1]
      linear_combination (-k) * hdet - k * sin_sq_add_cos_sq (k * b.L)
    · by_contra hall
      push Not at hall
      obtain ⟨-, -, hC, -⟩ := b.genSol_coeffs_eq_zero hk.ne' hall
      have := sin_lt (mul_pos hk hL)
      linarith

/-- **Factorisation of the clamped–clamped determinant**:
`2 (1 - cos y) - y sin y = 4 sin(y/2) (sin(y/2) - (y/2) cos(y/2))`, separating the symmetric
modes (`sin(y/2) = 0`) from the antisymmetric ones (`tan(y/2) = y/2`). -/
theorem clampedClamped_char_factor (y : ℝ) :
    2 * (1 - cos y) - y * sin y = 4 * sin (y / 2) * (sin (y / 2) - y / 2 * cos (y / 2)) := by
  have hy : y = 2 * (y / 2) := by ring
  conv_lhs => rw [hy, cos_two_mul, sin_two_mul]
  linear_combination (-4) * sin_sq_add_cos_sq (y / 2)

/-- **The symmetric clamped–clamped mode**: `w = c (1 - cos(2πx/L))` solves the buckling
equation at `P = 4π² EI / L²` (`kL = 2π`) and is clamped at both ends. -/
theorem clampedClamped_mode (c : ℝ) :
    b.BucklingEquation (4 * π ^ 2 * b.EI / b.L ^ 2) (fun x => c * (1 - cos (2 * π / b.L * x))) ∧
      b.ClampedClamped (fun x => c * (1 - cos (2 * π / b.L * x))) := by
  have hL := b.L_pos.ne'
  have e : (fun x => c * (1 - cos (2 * π / b.L * x))) = genSol (2 * π / b.L) c 0 (-c) 0 := by
    funext x; simp only [genSol]; ring
  have hkL : 2 * π / b.L * b.L = 2 * π := by field_simp
  rw [e]
  refine ⟨b.genSol_bucklingEquation (by field_simp; ring) _ _ _ _, by simp [genSol], ?_, ?_, ?_⟩
  · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1]; simp
  · simp only [genSol, hkL, cos_two_pi, sin_two_pi]; ring
  · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1, hkL, cos_two_pi, sin_two_pi]; ring

/-! ### The function `sin y - y cos y` -/

/-- `χ(y) = sin y - y cos y`: its zeros are the roots of `tan y = y` (clamped–pinned
characteristic function, and the antisymmetric clamped–clamped factor at `y = kL/2`). -/
noncomputable def charCP (y : ℝ) : ℝ := sin y - y * cos y

/-- `χ'(y) = y sin y`. -/
theorem hasDerivAt_charCP (y : ℝ) : HasDerivAt charCP (y * sin y) y := by
  have := (hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (hasDerivAt_cos y))
  convert this using 1
  · ext x; simp [charCP]
  · simp

/-- `χ` is continuous. -/
theorem continuous_charCP : Continuous charCP := by
  unfold charCP
  fun_prop

/-- `χ` is strictly increasing on `[0, π]`. -/
theorem strictMonoOn_charCP : StrictMonoOn charCP (Icc 0 π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) continuous_charCP.continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_charCP x).deriv]
  exact mul_pos hx.1 (sin_pos_of_pos_of_lt_pi hx.1 hx.2)

/-- `χ` is strictly decreasing on `[π, 2π]`. -/
theorem strictAntiOn_charCP : StrictAntiOn charCP (Icc π (2 * π)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc π (2 * π)) continuous_charCP.continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_charCP x).deriv]
  have : 0 < sin (x - π) := sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  rw [sin_sub_pi] at this
  nlinarith [hx.1, pi_pos]

/-- `χ > 0` on `(0, π]`. -/
theorem charCP_pos {y : ℝ} (hy : y ∈ Ioc 0 π) : 0 < charCP y := by
  have := strictMonoOn_charCP ⟨le_rfl, pi_pos.le⟩ ⟨hy.1.le, hy.2⟩ hy.1
  simpa [charCP] using this

/-- Numerical sign check: `χ(4.49) > 0`. -/
theorem charCP_four_point_four_nine : 0 < charCP 4.49 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have e : (4.49 : ℝ) = (π / 2 - (3 * π / 2 - 4.49)) + π := by ring
  have hsin : sin (4.49 : ℝ) = -cos (3 * π / 2 - 4.49) := by
    have := sin_add_pi (π / 2 - (3 * π / 2 - 4.49))
    rwa [sin_pi_div_two_sub, ← e] at this
  have hcos : cos (4.49 : ℝ) = -sin (3 * π / 2 - 4.49) := by
    have := cos_add_pi (π / 2 - (3 * π / 2 - 4.49))
    rwa [cos_pi_div_two_sub, ← e] at this
  unfold charCP
  rw [hsin, hcos]
  generalize hs : 3 * π / 2 - 4.49 = s
  have s1 : 0.2223 < s := by rw [← hs]; linarith
  have s2 : s < 0.2224 := by rw [← hs]; linarith
  have h3 : s ^ 3 < (0.2224 : ℝ) ^ 3 := pow_lt_pow_left₀ s2 (by linarith) (by norm_num)
  have hsn : 0.22 < sin s := by
    have := sin_gt_sub_cube (by linarith : 0 < s); norm_num at h3; linarith
  have hc : cos s < 0.976 := by nlinarith [sin_sq_add_cos_sq s]
  linarith

/-- Numerical sign check: `χ(4.50) < 0`. -/
theorem charCP_four_point_five : charCP 4.5 < 0 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have e : (4.5 : ℝ) = (π / 2 - (3 * π / 2 - 4.5)) + π := by ring
  have hsin : sin (4.5 : ℝ) = -cos (3 * π / 2 - 4.5) := by
    have := sin_add_pi (π / 2 - (3 * π / 2 - 4.5))
    rwa [sin_pi_div_two_sub, ← e] at this
  have hcos : cos (4.5 : ℝ) = -sin (3 * π / 2 - 4.5) := by
    have := cos_add_pi (π / 2 - (3 * π / 2 - 4.5))
    rwa [cos_pi_div_two_sub, ← e] at this
  unfold charCP
  rw [hsin, hcos]
  generalize hs : 3 * π / 2 - 4.5 = s
  have s1 : 0.2123 < s := by rw [← hs]; linarith
  have s2 : s < 0.2124 := by rw [← hs]; linarith
  have hsn := sin_lt (by linarith : 0 < s)
  have hc := one_sub_sq_div_two_le_cos (x := s)
  nlinarith

/-- **Existence of a root of `tan y = y` in `(4.49, 4.50)`** by the intermediate value theorem
(applied to `sin y - y cos y`). -/
theorem exists_root_charCP : ∃ y ∈ Ioo (4.49 : ℝ) 4.5, charCP y = 0 := by
  have h1 := charCP_four_point_four_nine
  have h2 := charCP_four_point_five
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' (by norm_num : (4.49 : ℝ) ≤ 4.5)
    continuous_charCP.continuousOn ⟨h2.le, h1.le⟩
  refine ⟨y, ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩, hy0⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- The **lowest positive root** of `tan y = y` (`≈ 4.4934`). -/
noncomputable def cpRoot : ℝ := Classical.choose exists_root_charCP

/-- `4.49 < cpRoot < 4.50`. -/
theorem cpRoot_bounds : 4.49 < cpRoot ∧ cpRoot < 4.5 :=
  (Classical.choose_spec exists_root_charCP).1

/-- `cpRoot` is a root of `sin y - y cos y`. -/
theorem charCP_cpRoot : charCP cpRoot = 0 := (Classical.choose_spec exists_root_charCP).2

/-- `cpRoot ∈ (π, 3π/2)`. -/
theorem cpRoot_mem : cpRoot ∈ Ioo π (3 * π / 2) := by
  have := cpRoot_bounds
  have := Real.pi_gt_d6
  have := Real.pi_lt_d6
  constructor <;> linarith

/-- `cpRoot` solves `tan y = y`. -/
theorem tan_cpRoot : tan cpRoot = cpRoot := by
  have h := charCP_cpRoot
  have hm := cpRoot_mem
  have hc : cos cpRoot < 0 := by
    have : 0 < sin (cpRoot - π + π / 2) :=
      sin_pos_of_pos_of_lt_pi (by linarith [hm.1, pi_pos]) (by linarith [hm.2])
    rw [show cpRoot - π + π / 2 = cpRoot - π / 2 + 0 by ring, add_zero, sin_sub_pi_div_two]
      at this
    linarith
  rw [tan_eq_sin_div_cos, div_eq_iff hc.ne]
  unfold charCP at h
  linarith

/-- `cpRoot` is the least positive root of `sin y - y cos y`. -/
theorem cpRoot_le {z : ℝ} (hz : 0 < z) (h : charCP z = 0) : cpRoot ≤ z := by
  by_contra hlt
  push Not at hlt
  have hb := cpRoot_bounds
  have := Real.pi_gt_d6
  rcases le_or_gt z π with hzπ | hzπ
  · linarith [charCP_pos ⟨hz, hzπ⟩]
  · have := strictAntiOn_charCP ⟨hzπ.le, by linarith⟩ ⟨by linarith, by linarith⟩ hlt
    rw [h, charCP_cpRoot] at this
    exact lt_irrefl _ this

/-- `cpRoot` is the only root of `sin y - y cos y` in `[π, 2π]`. -/
theorem cpRoot_unique {z : ℝ} (hz : z ∈ Icc π (2 * π)) (h : charCP z = 0) : z = cpRoot := by
  have hb := cpRoot_bounds
  have := Real.pi_gt_d6
  have := Real.pi_lt_d6
  exact strictAntiOn_charCP.injOn hz ⟨by linarith, by linarith⟩ (h.trans charCP_cpRoot.symm)

/-- **The clamped–clamped critical load** `P_cr = 4π² EI / L²` (effective length `L/2`):
`kL = 2π` is the least positive root of `2 (1 - cos kL) - kL sin kL`.
[TimoshenkoGere1961], §2.4. -/
theorem clampedClamped_critical_load :
    IsLeast {P | 0 < P ∧ b.Buckles b.ClampedClamped P} (4 * π ^ 2 * b.EI / b.L ^ 2) := by
  have key := b.isLeast_of_char (bc := fun _ => b.ClampedClamped)
    (χ := fun z => 2 * (1 - cos z) - z * sin z = 0)
    (fun k P hk hP => b.clampedClamped_iff hk hP) (y := 2 * π) (by positivity)
    (by simp) (fun z hz hcz => by
      by_contra hlt
      push Not at hlt
      have hcz' := hcz
      rw [clampedClamped_char_factor] at hcz'
      have h1 : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
      have h2 := charCP_pos (y := z / 2) ⟨by positivity, by linarith⟩
      unfold charCP at h2
      have : 0 < 4 * sin (z / 2) * (sin (z / 2) - z / 2 * cos (z / 2)) := by positivity
      linarith)
  convert key using 1
  ring

/-! ### Clamped–pinned column -/

/-- **(d) Clamped–pinned buckling**: a nontrivial solution exists iff `sin kL = kL cos kL`.
[TimoshenkoGere1961], §2.4. -/
theorem clampedPinned_iff {k P : ℝ} (hk : 0 < k) (hP : P = b.EI * k ^ 2) :
    b.Buckles b.ClampedPinned P ↔ sin (k * b.L) = k * b.L * cos (k * b.L) := by
  have hL := b.L_pos
  have m0 : (0 : ℝ) ∈ Icc 0 b.L := ⟨le_rfl, hL.le⟩
  have mL : b.L ∈ Icc 0 b.L := ⟨hL.le, le_rfl⟩
  constructor
  · rintro ⟨w, hw, h, ⟨c0, c1, c2, c3⟩, x₀, hx₀, hne⟩
    obtain ⟨A, B, C, D, hG⟩ := b.eq_genSol_of_bucklingEquation hk.ne' hP hw h
    have triv := b.coeffs_ne_zero_of_nontrivial hG hx₀ hne
    have v0 := hG 0 m0 0 (by norm_num)
    have vL := hG _ mL 0 (by norm_num)
    simp only [iteratedDeriv_zero] at v0 vL
    rw [c0] at v0
    rw [c2] at vL
    rw [hG 0 m0 1 (by norm_num), (iteratedDeriv_genSol k A B C D 0).1] at c1
    rw [hG _ mL 2 (by norm_num), (iteratedDeriv_genSol k A B C D _).2.1] at c3
    simp only [genSol, mul_zero, cos_zero, sin_zero, mul_one, add_zero, sub_zero] at v0 vL c1
    by_contra hne'
    have E' : k ^ 2 * (C * cos (k * b.L) + D * sin (k * b.L)) = 0 := by linear_combination -c3
    have E := (mul_eq_zero.mp E').resolve_left (by positivity)
    have F : C + D * k * b.L = 0 := by linear_combination vL - v0 + b.L * c1 + E
    have G' : D * (sin (k * b.L) - k * b.L * cos (k * b.L)) = 0 := by
      linear_combination E - cos (k * b.L) * F
    have hD := (mul_eq_zero.mp G').resolve_right (sub_ne_zero.mpr hne')
    subst hD
    have hC : C = 0 := by linear_combination F
    subst hC
    exact triv ⟨by linear_combination -v0, by linear_combination c1, rfl, rfl⟩
  · intro hroot
    refine ⟨genSol k (k * b.L) (-k) (-(k * b.L)) 1, contDiff_genSol _ _ _ _ _,
      b.genSol_bucklingEquation hP _ _ _ _, ⟨by simp [genSol], ?_, ?_, ?_⟩, ?_⟩
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).1]; simp
    · simp only [genSol]; linear_combination hroot
    · rw [(iteratedDeriv_genSol _ _ _ _ _ _).2.1]
      linear_combination (-k ^ 2) * hroot
    · by_contra hall
      push Not at hall
      obtain ⟨-, -, hC, -⟩ := b.genSol_coeffs_eq_zero hk.ne' hall
      have : 0 < k * b.L := mul_pos hk hL
      linarith

/-- The clamped–pinned characteristic equation in the textbook form `tan y = y`. -/
theorem sin_eq_mul_cos_iff_tan (y : ℝ) : sin y = y * cos y ↔ cos y ≠ 0 ∧ tan y = y := by
  constructor
  · intro h
    have hc : cos y ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at h
      have := sin_sq_add_cos_sq y
      rw [h, hc] at this
      norm_num at this
    refine ⟨hc, ?_⟩
    rw [tan_eq_sin_div_cos, div_eq_iff hc, h]
  · rintro ⟨hc, ht⟩
    rw [tan_eq_sin_div_cos, div_eq_iff hc] at ht
    exact ht

/-- **The clamped–pinned critical load** `P_cr = cpRoot² EI / L²`, where `cpRoot ≈ 4.4934` is
the least positive root of `tan y = y`. [TimoshenkoGere1961], §2.4. -/
theorem clampedPinned_critical_load :
    IsLeast {P | 0 < P ∧ b.Buckles b.ClampedPinned P} (cpRoot ^ 2 * b.EI / b.L ^ 2) := by
  have hb := cpRoot_bounds
  exact b.isLeast_of_char (bc := fun _ => b.ClampedPinned)
    (χ := fun z => sin z = z * cos z)
    (fun k P hk hP => b.clampedPinned_iff hk hP) (y := cpRoot) (by linarith)
    (by have := charCP_cpRoot; unfold charCP at this; linarith)
    (fun z hz hcz => cpRoot_le hz (by unfold charCP; linarith))

/-- **Numerical bounds on the clamped–pinned critical load**:
`20.16 EI / L² < P_cr < 20.25 EI / L²` (the textbook value is `≈ 20.19 EI / L²`). -/
theorem clampedPinned_critical_load_bounds :
    20.16 * b.EI / b.L ^ 2 < cpRoot ^ 2 * b.EI / b.L ^ 2 ∧
      cpRoot ^ 2 * b.EI / b.L ^ 2 < 20.25 * b.EI / b.L ^ 2 := by
  have hb := cpRoot_bounds
  have hEI := b.EI_pos
  have hL : 0 < b.L ^ 2 := by have := b.L_pos; positivity
  constructor
  · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by nlinarith) hEI) hL
  · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by nlinarith) hEI) hL

/-- **Effective length of the clamped–pinned column**: `P_cr = π² EI / (K L)²` with
`K = π / cpRoot`, and `0.69 < K < 0.70`; the textbook factor `K ≈ 0.7` is approximate
(`K ≈ 0.6992`). -/
theorem clampedPinned_effective_length :
    cpRoot ^ 2 * b.EI / b.L ^ 2 = π ^ 2 * b.EI / (π / cpRoot * b.L) ^ 2 ∧
      0.69 < π / cpRoot ∧ π / cpRoot < 0.7 := by
  have hb := cpRoot_bounds
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hr : 0 < cpRoot := by linarith
  have hL := b.L_pos.ne'
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [lt_div_iff₀ hr]; nlinarith
  · rw [div_lt_iff₀ hr]; nlinarith

/-! ### Imperfect pinned column -/

/-- The Euler load `P_E = π² EI / L²` of the pinned column. -/
noncomputable def eulerLoad : ℝ := π ^ 2 * b.EI / b.L ^ 2

/-- `P_E` is the least pinned–pinned buckling load (`euler_critical_load`). -/
theorem isLeast_bucklingLoads_eulerLoad : IsLeast b.bucklingLoads b.eulerLoad :=
  b.euler_critical_load

/-- `P_E > 0`. -/
theorem eulerLoad_pos : 0 < b.eulerLoad := by
  have := b.EI_pos
  have := b.L_pos
  unfold eulerLoad
  positivity

/-- The **additional deflection** of a pinned column with initial crookedness
`w₀ = a sin(πx/L)` under `P`: `w = P/(P_E - P) · a sin(πx/L)`. -/
noncomputable def imperfectDeflection (a P : ℝ) : ℝ → ℝ :=
  fun x => P / (b.eulerLoad - P) * a * b.mode x

/-- **(e) The imperfect column**: the additional deflection solves
`EI w'' + P (w + w₀) = 0` with `w(0) = w(L) = 0`, where `w₀ = a sin(πx/L)`.
[TimoshenkoGere1961], §1.11. -/
theorem imperfect_solves (a P : ℝ) (hP : P ≠ b.eulerLoad) :
    (∀ x, b.EI * iteratedDeriv 2 (b.imperfectDeflection a P) x +
        P * (b.imperfectDeflection a P x + a * b.mode x) = 0) ∧
      b.imperfectDeflection a P 0 = 0 ∧ b.imperfectDeflection a P b.L = 0 := by
  have hL := b.L_pos.ne'
  have e : b.imperfectDeflection a P = genSol (π / b.L) 0 0 0 (P / (b.eulerLoad - P) * a) := by
    funext x; simp [imperfectDeflection, genSol, mode]
  have hne : b.eulerLoad - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
  have hl : b.EI * (π / b.L) ^ 2 = b.eulerLoad := by unfold eulerLoad; field_simp
  have hD : P / (b.eulerLoad - P) * a * (b.eulerLoad - P) = P * a := by field_simp
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [e, (iteratedDeriv_genSol _ _ _ _ _ _).2.1]
    simp only [genSol, mode]
    linear_combination (-(P / (b.eulerLoad - P) * a * sin (π / b.L * x))) * hl
      - sin (π / b.L * x) * hD
  · simp [imperfectDeflection, mode]
  · simp only [imperfectDeflection, mode]
    rw [div_mul_cancel₀ _ hL, sin_pi, mul_zero]

/-- **Total deflection** `w + w₀ = a / (1 - P/P_E) · sin(πx/L)`: the initial amplitude is
multiplied by the **amplification factor** `1 / (1 - P/P_E)`. -/
theorem imperfect_total (a P : ℝ) (hP : P ≠ b.eulerLoad) (x : ℝ) :
    b.imperfectDeflection a P x + a * b.mode x = a / (1 - P / b.eulerLoad) * b.mode x := by
  have hE := b.eulerLoad_pos.ne'
  have hne : b.eulerLoad - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
  rw [show 1 - P / b.eulerLoad = (b.eulerLoad - P) / b.eulerLoad by field_simp]
  simp only [imperfectDeflection]
  field_simp
  ring

/-- **Divergence of the amplification**: for `a > 0`, the total amplitude `a / (1 - P/P_E)`
tends to `+∞` as `P → P_E⁻`. -/
theorem tendsto_amplification {a : ℝ} (ha : 0 < a) :
    Tendsto (fun P => a / (1 - P / b.eulerLoad)) (𝓝[<] b.eulerLoad) atTop := by
  have hPe := b.eulerLoad_pos
  have h1 : Tendsto (fun P => 1 - P / b.eulerLoad) (𝓝[<] b.eulerLoad) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun P => 1 - P / b.eulerLoad) (𝓝 b.eulerLoad)
          (𝓝 (1 - b.eulerLoad / b.eulerLoad)) :=
        ((continuous_const.sub (continuous_id.div_const _)).tendsto _)
      rw [div_self hPe.ne', sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with P hP
      have : P / b.eulerLoad < 1 := (div_lt_one hPe).mpr hP
      simp only [mem_Ioi]
      linarith
  refine (Tendsto.const_mul_atTop ha (tendsto_inv_nhdsGT_zero.comp h1)).congr fun P => ?_
  simp [div_eq_mul_inv]

end EBBeam

/-! ### Lateral–torsional buckling -/

/-- A simply supported beam under uniform moment `M`, for **lateral–torsional buckling**:
length `L`, lateral bending stiffness `EI_y` and St Venant torsional stiffness `GJ` (warping
neglected). -/
structure LTBeam where
  /-- Length. -/
  L : ℝ
  /-- Lateral (weak-axis) bending stiffness `E I_y`. -/
  EIy : ℝ
  /-- Torsional stiffness `G J`. -/
  GJ : ℝ
  L_pos : 0 < L
  EIy_pos : 0 < EIy
  GJ_pos : 0 < GJ

namespace LTBeam

variable (l : LTBeam)

/-- The coupled **lateral–torsional equations** `EI_y u'''' + M φ'' = 0`,
`GJ φ'' - M u'' = 0` on `[0, L]` for the lateral deflection `u` and twist `φ`. -/
def Equations (M : ℝ) (u φ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 l.L, l.EIy * iteratedDeriv 4 u x + M * iteratedDeriv 2 φ x = 0 ∧
    l.GJ * iteratedDeriv 2 φ x - M * iteratedDeriv 2 u x = 0

/-- **(f) Lateral–torsional buckling**: the equations have a nontrivial pair
`u = A sin(πx/L)`, `φ = B sin(πx/L)` iff the `2 × 2` determinant vanishes,
`M² = (π/L)² EI_y GJ`. [TimoshenkoGere1961], §6.2. -/
theorem buckles_iff (M : ℝ) :
    (∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
      l.Equations M (fun x => A * sin (π / l.L * x)) (fun x => B * sin (π / l.L * x))) ↔
      M ^ 2 = (π / l.L) ^ 2 * l.EIy * l.GJ := by
  have hL := l.L_pos
  have e : ∀ A : ℝ, (fun x => A * sin (π / l.L * x)) = EBBeam.genSol (π / l.L) 0 0 0 A :=
    fun A => by funext x; simp [EBBeam.genSol]
  have hlam : 0 < π / l.L := by positivity
  constructor
  · rintro ⟨A, B, hAB, h⟩
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := h (l.L / 2) ⟨by positivity, by linarith⟩
    obtain ⟨-, a2, -, a4⟩ := EBBeam.iteratedDeriv_genSol (π / l.L) 0 0 0 A (l.L / 2)
    obtain ⟨-, b2, -, -⟩ := EBBeam.iteratedDeriv_genSol (π / l.L) 0 0 0 B (l.L / 2)
    have hs : sin (π / l.L * (l.L / 2)) = 1 := by
      rw [show π / l.L * (l.L / 2) = π / 2 by field_simp]
      exact sin_pi_div_two
    rw [a4, b2, hs] at h1
    rw [b2, a2, hs] at h2
    have E1' : (π / l.L) ^ 2 * (l.EIy * (π / l.L) ^ 2 * A - M * B) = 0 := by
      linear_combination h1
    have E2' : (π / l.L) ^ 2 * (M * A - l.GJ * B) = 0 := by linear_combination h2
    have E1 := (mul_eq_zero.mp E1').resolve_left (by positivity)
    have E2 := (mul_eq_zero.mp E2').resolve_left (by positivity)
    by_contra hM
    have hd : (π / l.L) ^ 2 * l.EIy * l.GJ - M ^ 2 ≠ 0 := fun h0 => hM (by linarith)
    have hA : A * ((π / l.L) ^ 2 * l.EIy * l.GJ - M ^ 2) = 0 := by
      linear_combination l.GJ * E1 - M * E2
    have hB : B * ((π / l.L) ^ 2 * l.EIy * l.GJ - M ^ 2) = 0 := by
      linear_combination M * E1 - l.EIy * (π / l.L) ^ 2 * E2
    rcases hAB with hA0 | hB0
    · exact hA0 ((mul_eq_zero.mp hA).resolve_right hd)
    · exact hB0 ((mul_eq_zero.mp hB).resolve_right hd)
  · intro hM
    refine ⟨l.GJ, M, Or.inl l.GJ_pos.ne', ?_⟩
    rw [e, e]
    intro x _
    obtain ⟨-, a2, -, a4⟩ := EBBeam.iteratedDeriv_genSol (π / l.L) 0 0 0 l.GJ x
    obtain ⟨-, b2, -, -⟩ := EBBeam.iteratedDeriv_genSol (π / l.L) 0 0 0 M x
    rw [a4, b2, a2]
    constructor
    · linear_combination (-((π / l.L) ^ 2 * sin (π / l.L * x))) * hM
    · ring

/-- **The critical moment** `M_cr = (π/L) √(EI_y GJ)`: the determinant condition is
`|M| = (π/L) √(EI_y GJ)`. [TimoshenkoGere1961], §6.2. -/
theorem critical_moment (M : ℝ) :
    M ^ 2 = (π / l.L) ^ 2 * l.EIy * l.GJ ↔ |M| = π / l.L * √(l.EIy * l.GJ) := by
  have hL := l.L_pos
  have hE := l.EIy_pos
  have hG := l.GJ_pos
  have hsq : (π / l.L * √(l.EIy * l.GJ)) ^ 2 = (π / l.L) ^ 2 * l.EIy * l.GJ := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  constructor
  · intro h
    rw [← pow_left_inj₀ (abs_nonneg M) (by positivity) two_ne_zero, sq_abs, h, hsq]
  · intro h
    rw [← sq_abs, h, hsq]

end LTBeam

end ContinuumMechanics.Beams
