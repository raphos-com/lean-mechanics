import ContinuumMechanics.Fluids.Waves
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# One-dimensional steady compressible flow of a perfect gas

A calorically perfect gas with ratio of specific heats `γ > 1` has enthalpy `h = c_p T`,
sound speed `c² = γ p / ρ = (γ - 1) c_p T` (`Waves.hasDerivAt_polytrope`) and, along
isentropic processes, `p ∝ ρ^γ`. The Mach number is `M = V / c`.

**Isentropic relations.** The energy equation `h + V²/2 = h₀` gives the stagnation temperature
ratio `T₀/T = 1 + (γ - 1) M²/2`; isentropy then gives `p₀/p = (T₀/T)^{γ/(γ-1)}` and
`ρ₀/ρ = (T₀/T)^{1/(γ-1)}`.

**Quasi-one-dimensional flow.** Continuity `ρ V A = const`, Euler's equation `ρ V V' = -p'`
and `p' = c² ρ'` give the area–velocity (Hugoniot) relation `A'/A = (M² - 1) V'/V`: subsonic
flow accelerates in a converging duct, supersonic flow in a diverging one, and `M = 1` at a
throat. The area–Mach relation `A/A*` has its unique minimum `1` at `M = 1`.

**Normal shocks.** The Rankine–Hugoniot jump conditions across a stationary normal shock with
upstream Mach number `M₁` are solved by the classical ratios `M₂²`, `p₂/p₁`, `ρ₂/ρ₁`. The
entropy jump `Δs / c_v = log((p₂/p₁)(ρ₁/ρ₂)^γ)` is positive iff `M₁ > 1`: only compression
shocks are admissible (the analogue of the hydraulic jump of
`ContinuumMechanics.Fluids.OpenChannel`).

## Main definitions

* `tempRatio γ M = 1 + (γ - 1) M²/2`, `pressureRatio`, `densityRatio`: `T₀/T`, `p₀/p`, `ρ₀/ρ`.
* `areaRatio γ M`: the area–Mach function `A/A*`.
* `shockMachSq`, `shockPressureRatio`, `shockDensityRatio`: normal-shock relations.
* `shockEntropyJump γ M₁ = log((p₂/p₁)(ρ₂/ρ₁)^{-γ})`, the entropy jump `Δs/c_v`.

## Main results

* `stagnation_temperature`: `(c_p T + V²/2)/(c_p T) = 1 + (γ - 1) M²/2`.
* `pressureRatio_eq_densityRatio_rpow`, `pressureRatio_eq_densityRatio_mul_tempRatio`:
  `p₀/p = (ρ₀/ρ)^γ` and `p₀/p = (ρ₀/ρ)(T₀/T)` (isentropy and the equation of state).
* `hasDerivAt_isentropic`: along an isentropic flow `p' = (γ p/ρ) ρ'`.
* `area_velocity`: `A'/A = (M² - 1) V'/V`; `area_deriv_neg_of_subsonic`,
  `area_deriv_pos_of_supersonic`, `mach_eq_one_of_throat`.
* `one_le_areaRatio`, `one_lt_areaRatio`, `areaRatio_eq_one_iff`, `tendsto_areaRatio_zero`,
  `tendsto_areaRatio_atTop`: `A/A* ≥ 1` with equality iff `M = 1`, and `A/A* → ∞` at both ends.
* `normalShock_mass`, `normalShock_momentum`, `normalShock_energy`, `normalShock_mach`: the
  shock ratios satisfy the Rankine–Hugoniot conditions.
* `shockMachSq_lt_one`, `one_lt_shockPressureRatio`, `one_lt_shockDensityRatio`,
  `shockDensityRatio_lt`, `tendsto_shockDensityRatio`, `tendsto_shockMachSq`.
* `shockEntropyJump_pos`, `shockEntropyJump_neg`: `Δs > 0` for `M₁ > 1` and `Δs < 0` for an
  expansion "shock" with `M₁ < 1`.

## References

* [LandauLifshitz1987] L. D. Landau, E. M. Lifshitz, *Fluid Mechanics*, 2nd ed., §§83–85, 89, 97.
* [Anderson2003] J. D. Anderson, *Modern Compressible Flow*, 3rd ed., chs. 3, 5.
* [Liepmann1957] H. W. Liepmann, A. Roshko, *Elements of Gasdynamics*, chs. 2–3.
-/

open Real Filter Topology Set

noncomputable section

namespace ContinuumMechanics.Fluids.Compressible

variable {γ : ℝ}

/-! ### Isentropic relations -/

/-- The stagnation temperature ratio `T₀/T = 1 + (γ - 1) M²/2`. -/
def tempRatio (γ M : ℝ) : ℝ := 1 + (γ - 1) / 2 * M ^ 2

/-- The stagnation pressure ratio `p₀/p = (T₀/T)^{γ/(γ-1)}`. -/
def pressureRatio (γ M : ℝ) : ℝ := tempRatio γ M ^ (γ / (γ - 1))

/-- The stagnation density ratio `ρ₀/ρ = (T₀/T)^{1/(γ-1)}`. -/
def densityRatio (γ M : ℝ) : ℝ := tempRatio γ M ^ (1 / (γ - 1))

/-- `T₀/T ≥ 1`. -/
theorem one_le_tempRatio (hγ : 1 < γ) (M : ℝ) : 1 ≤ tempRatio γ M := by
  have : 0 ≤ (γ - 1) / 2 * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg M)
  unfold tempRatio; linarith

/-- `T₀/T > 0`. -/
theorem tempRatio_pos (hγ : 1 < γ) (M : ℝ) : 0 < tempRatio γ M :=
  lt_of_lt_of_le one_pos (one_le_tempRatio hγ M)

/-- At sonic conditions `T₀/T* = (γ + 1)/2`. -/
theorem tempRatio_one (γ : ℝ) : tempRatio γ 1 = (γ + 1) / 2 := by
  unfold tempRatio; ring

/-- **Stagnation temperature** from the energy equation `h + V²/2 = h₀` with `h = c_p T` and
`c² = (γ - 1) c_p T`: `T₀/T = h₀/h = 1 + (γ - 1) M²/2` where `V = M c`. -/
theorem stagnation_temperature {cp T V c M : ℝ} (hcp : 0 < cp) (hT : 0 < T)
    (hc : c ^ 2 = (γ - 1) * cp * T) (hM : V = M * c) :
    (cp * T + V ^ 2 / 2) / (cp * T) = tempRatio γ M := by
  subst hM
  unfold tempRatio
  field_simp
  rw [hc]; ring

/-- **Isentropy**: `p₀/p = (ρ₀/ρ)^γ`, i.e. `p ∝ ρ^γ` between the static and stagnation
states. -/
theorem pressureRatio_eq_densityRatio_rpow (hγ : 1 < γ) (M : ℝ) :
    pressureRatio γ M = densityRatio γ M ^ γ := by
  unfold pressureRatio densityRatio
  rw [← rpow_mul (tempRatio_pos hγ M).le]
  congr 1; ring

/-- **Equation of state** `p = ρ R T`: `p₀/p = (ρ₀/ρ)(T₀/T)`. -/
theorem pressureRatio_eq_densityRatio_mul_tempRatio (hγ : 1 < γ) (M : ℝ) :
    pressureRatio γ M = densityRatio γ M * tempRatio γ M := by
  have h1 : γ - 1 ≠ 0 := by linarith
  unfold pressureRatio densityRatio
  rw [show γ / (γ - 1) = 1 / (γ - 1) + 1 by field_simp; ring,
    rpow_add (tempRatio_pos hγ M), rpow_one]

/-! ### Quasi-one-dimensional flow: the area–velocity relation -/

/-- Along an isentropic flow `p = K ρ^γ`, the pressure gradient is `p' = c² ρ'` with
`c² = γ p / ρ`. -/
theorem hasDerivAt_isentropic {K : ℝ} {ρ : ℝ → ℝ} {ρ' x : ℝ} (hρ : HasDerivAt ρ ρ' x)
    (hpos : 0 < ρ x) :
    HasDerivAt (fun y => K * ρ y ^ γ) (γ * (K * ρ x ^ γ) / ρ x * ρ') x :=
  (Waves.hasDerivAt_polytrope K γ hpos).comp x hρ

/-- **Area–velocity (Hugoniot) relation.** For quasi-one-dimensional flow with constant mass
flux `ρ V A = m`, Euler's equation `ρ V V' = -p'` and `p' = c² ρ'`, the duct area satisfies
`A'/A = (M² - 1) V'/V` with `M = V/c`. -/
theorem area_velocity {ρ V A : ℝ → ℝ} {ρ' V' A' p' c M m x : ℝ}
    (hρ : HasDerivAt ρ ρ' x) (hV : HasDerivAt V V' x) (hA : HasDerivAt A A' x)
    (hmass : ∀ y, ρ y * V y * A y = m) (heuler : ρ x * V x * V' = -p')
    (hsound : p' = c ^ 2 * ρ') (hM : V x = M * c)
    (hρ0 : ρ x ≠ 0) (hV0 : V x ≠ 0) (hA0 : A x ≠ 0) :
    A' / A x = (M ^ 2 - 1) * V' / V x := by
  have hc : c ≠ 0 := by rintro rfl; rw [mul_zero] at hM; exact hV0 hM
  have hd := (hρ.mul hV).mul hA
  have hconst : ρ * V * A = fun _ => m := funext hmass
  rw [hconst] at hd
  have hcont := (hasDerivAt_const x m).unique hd
  simp only [Pi.mul_apply] at hcont
  have hM' : M = V x / c := by field_simp; exact hM.symm
  subst hM'
  rw [hsound] at heuler
  have key : ρ x * (A' * V x * c ^ 2) = ρ x * ((V x ^ 2 - c ^ 2) * V' * A x) := by
    linear_combination (-c ^ 2) * hcont - (V x * A x) * heuler
  have key' := mul_left_cancel₀ hρ0 key
  rw [div_eq_div_iff hA0 hV0]
  field_simp
  linear_combination key'

/-- In a subsonic (`0 < M < 1`) accelerating flow (`V' > 0`) the duct must converge. -/
theorem area_deriv_neg_of_subsonic {A' V' M Ax Vx : ℝ} (hA : 0 < Ax) (hV : 0 < Vx)
    (h : A' / Ax = (M ^ 2 - 1) * V' / Vx) (hM0 : 0 ≤ M) (hM : M < 1) (hV' : 0 < V') :
    A' < 0 := by
  have hM2 : M ^ 2 - 1 < 0 := by nlinarith
  have : A' / Ax < 0 := by rw [h]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hM2 hV') hV
  by_contra hA'
  have : 0 ≤ A' / Ax := div_nonneg (not_lt.1 hA') hA.le
  linarith

/-- In a supersonic (`M > 1`) accelerating flow (`V' > 0`) the duct must diverge. -/
theorem area_deriv_pos_of_supersonic {A' V' M Ax Vx : ℝ} (hA : 0 < Ax) (hV : 0 < Vx)
    (h : A' / Ax = (M ^ 2 - 1) * V' / Vx) (hM : 1 < M) (hV' : 0 < V') : 0 < A' := by
  have hM2 : 0 < M ^ 2 - 1 := by nlinarith
  have : 0 < A' / Ax := by rw [h]; positivity
  exact (div_pos_iff_of_pos_right hA).1 this

/-- **Sonic throat**: where the area is stationary (`A' = 0`) and the flow still accelerates or
decelerates (`V' ≠ 0`), the flow is sonic, `M = 1`. -/
theorem mach_eq_one_of_throat {V' M Ax Vx : ℝ} (hV : Vx ≠ 0)
    (h : 0 / Ax = (M ^ 2 - 1) * V' / Vx) (hM : 0 ≤ M) (hV' : V' ≠ 0) : M = 1 := by
  rw [zero_div, eq_comm, div_eq_zero_iff, or_iff_left hV, mul_eq_zero, or_iff_left hV',
    sub_eq_zero] at h
  nlinarith [sq_nonneg (M - 1), sq_nonneg (M + 1)]

/-! ### The area–Mach relation -/

/-- The **area–Mach relation**
`A/A* = (1/M)((2/(γ+1))(1 + (γ-1)M²/2))^{(γ+1)/(2(γ-1))}`. -/
def areaRatio (γ M : ℝ) : ℝ :=
  1 / M * (2 / (γ + 1) * tempRatio γ M) ^ ((γ + 1) / (2 * (γ - 1)))

/-- The base of the area–Mach function is the affine function `1 + b (M² - 1)` with
`b = (γ - 1)/(γ + 1)`. -/
theorem areaRatio_base (hγ : 1 < γ) (M : ℝ) :
    2 / (γ + 1) * tempRatio γ M = 1 + (γ - 1) / (γ + 1) * (M ^ 2 - 1) := by
  have : γ + 1 ≠ 0 := by linarith
  unfold tempRatio; field_simp; ring

/-- Bernoulli's inequality for the area–Mach function: `(M²)^b ≤ 1 + b (M² - 1)`, strictly
when `M ≠ 1`. -/
theorem rpow_lt_areaRatio_base (hγ : 1 < γ) {M : ℝ} (hM : 0 < M) (hM1 : M ≠ 1) :
    (M ^ 2) ^ ((γ - 1) / (γ + 1)) < 2 / (γ + 1) * tempRatio γ M := by
  rw [areaRatio_base hγ]
  have h := rpow_one_add_lt_one_add_mul_self (s := M ^ 2 - 1) (by nlinarith)
    (by intro h; apply hM1; nlinarith [sq_nonneg (M - 1)]) (p := (γ - 1) / (γ + 1))
    (div_pos (by linarith) (by linarith)) (by rw [div_lt_one (by linarith)]; linarith)
  simpa using h

/-- `(M²)^{b k} = M` where `b k = 1/2`. -/
theorem rpow_rpow_eq_self (hγ : 1 < γ) {M : ℝ} (hM : 0 < M) :
    ((M ^ 2) ^ ((γ - 1) / (γ + 1))) ^ ((γ + 1) / (2 * (γ - 1))) = M := by
  rw [← rpow_mul (by positivity), ← rpow_natCast, ← rpow_mul hM.le]
  have h1 : γ - 1 ≠ 0 := by linarith
  have h2 : γ + 1 ≠ 0 := by linarith
  have : ((2 : ℕ) : ℝ) * ((γ - 1) / (γ + 1) * ((γ + 1) / (2 * (γ - 1)))) = 1 := by
    field_simp; push_cast; ring
  rw [this, rpow_one]

/-- At `M = 1` the area ratio is `1`: the sonic area `A*` is the throat area. -/
theorem areaRatio_one (hγ : 1 < γ) : areaRatio γ 1 = 1 := by
  rw [areaRatio, areaRatio_base hγ]; simp

/-- **The throat is the minimum section**: `A/A* > 1` for `M ≠ 1`. -/
theorem one_lt_areaRatio (hγ : 1 < γ) {M : ℝ} (hM : 0 < M) (hM1 : M ≠ 1) :
    1 < areaRatio γ M := by
  have hk : 0 < (γ + 1) / (2 * (γ - 1)) := div_pos (by linarith) (by linarith)
  have h := rpow_lt_rpow (by positivity) (rpow_lt_areaRatio_base hγ hM hM1) hk
  rw [rpow_rpow_eq_self hγ hM] at h
  rw [areaRatio, one_div, ← div_eq_inv_mul, one_lt_div hM]
  exact h

/-- `A/A* ≥ 1` for every `M > 0`. -/
theorem one_le_areaRatio (hγ : 1 < γ) {M : ℝ} (hM : 0 < M) : 1 ≤ areaRatio γ M := by
  rcases eq_or_ne M 1 with rfl | h
  · exact (areaRatio_one hγ).ge
  · exact (one_lt_areaRatio hγ hM h).le

/-- `A/A* = 1` iff the flow is sonic. -/
theorem areaRatio_eq_one_iff (hγ : 1 < γ) {M : ℝ} (hM : 0 < M) : areaRatio γ M = 1 ↔ M = 1 :=
  ⟨fun h => by_contra fun h1 => (one_lt_areaRatio hγ hM h1).ne' h,
    fun h => h ▸ areaRatio_one hγ⟩

/-- `A/A* → ∞` as `M → 0⁺`. -/
theorem tendsto_areaRatio_zero (hγ : 1 < γ) :
    Tendsto (areaRatio γ) (𝓝[>] 0) atTop := by
  set k := (γ + 1) / (2 * (γ - 1))
  have hk : 0 < k := div_pos (by linarith) (by linarith)
  have hC : 0 < (2 / (γ + 1)) ^ k := rpow_pos_of_pos (div_pos two_pos (by linarith)) _
  refine tendsto_atTop_mono' _ ?_ (tendsto_inv_nhdsGT_zero.const_mul_atTop hC)
  filter_upwards [self_mem_nhdsWithin] with M (hM : 0 < M)
  have h2 : 0 < 2 / (γ + 1) := div_pos two_pos (by linarith)
  rw [areaRatio, one_div, mul_comm M⁻¹]
  refine mul_le_mul_of_nonneg_right (rpow_le_rpow h2.le ?_ hk.le) (inv_nonneg.2 hM.le)
  have : 1 ≤ tempRatio γ M := one_le_tempRatio hγ M
  nlinarith

/-- `A/A* → ∞` as `M → ∞`. -/
theorem tendsto_areaRatio_atTop (hγ : 1 < γ) : Tendsto (areaRatio γ) atTop atTop := by
  set k := (γ + 1) / (2 * (γ - 1))
  set b := (γ - 1) / (γ + 1)
  have hk : 0 < k := div_pos (by linarith) (by linarith)
  have hb : 0 < b := div_pos (by linarith) (by linarith)
  have hb1 : b < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2k : 0 < 2 * k - 1 := by
    have : 2 * k - 1 = 2 / (γ - 1) := by
      have : γ - 1 ≠ 0 := by linarith
      simp only [k]; field_simp; ring
    rw [this]; exact div_pos two_pos (by linarith)
  refine tendsto_atTop_mono' _ ?_
    ((tendsto_rpow_atTop h2k).const_mul_atTop (rpow_pos_of_pos hb k))
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hbase : b * M ^ 2 ≤ 2 / (γ + 1) * tempRatio γ M := by
    rw [areaRatio_base hγ]; nlinarith
  have h := rpow_le_rpow (by positivity) hbase hk.le
  rw [mul_rpow hb.le (by positivity), ← rpow_natCast, ← rpow_mul hM.le] at h
  rw [areaRatio, one_div, rpow_sub_one hM.ne', mul_div_assoc', div_eq_mul_inv,
    mul_comm _ M⁻¹]
  push_cast at h
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 hM.le)

/-! ### Normal shocks -/

/-- Downstream Mach number squared, `M₂² = (1 + (γ-1)M₁²/2)/(γ M₁² - (γ-1)/2)`. -/
def shockMachSq (γ M : ℝ) : ℝ := (1 + (γ - 1) / 2 * M ^ 2) / (γ * M ^ 2 - (γ - 1) / 2)

/-- Static pressure ratio across a normal shock, `p₂/p₁ = 1 + 2γ(M₁² - 1)/(γ + 1)`. -/
def shockPressureRatio (γ M : ℝ) : ℝ := 1 + 2 * γ / (γ + 1) * (M ^ 2 - 1)

/-- Density ratio across a normal shock, `ρ₂/ρ₁ = V₁/V₂ = (γ+1)M₁²/((γ-1)M₁² + 2)`. -/
def shockDensityRatio (γ M : ℝ) : ℝ := (γ + 1) * M ^ 2 / ((γ - 1) * M ^ 2 + 2)

/-- The density ratio is positive for `M₁ ≠ 0`. -/
theorem shockDensityRatio_pos (hγ : 1 < γ) {M : ℝ} (hM : M ≠ 0) : 0 < shockDensityRatio γ M := by
  have : 0 < M ^ 2 := by positivity
  unfold shockDensityRatio
  exact div_pos (by nlinarith) (by nlinarith)

/-- The pressure ratio is positive iff `M₁² > (γ - 1)/(2γ)`. -/
theorem shockPressureRatio_pos (hγ : 1 < γ) {M : ℝ} (hM : (γ - 1) / (2 * γ) < M ^ 2) :
    0 < shockPressureRatio γ M := by
  have h1 : 0 < 2 * γ := by linarith
  rw [div_lt_iff₀ h1] at hM
  have : 0 < γ + 1 := by linarith
  unfold shockPressureRatio
  rw [← sub_pos]
  have : 1 + 2 * γ / (γ + 1) * (M ^ 2 - 1) = (M ^ 2 * (2 * γ) - (γ - 1)) / (γ + 1) := by
    field_simp; ring
  rw [sub_zero, this]; exact div_pos (by linarith) (by linarith)

/-- Closed form `p₂/p₁ = (2γM₁² - γ + 1)/(γ + 1)`. -/
theorem shockPressureRatio_eq (hγ : 1 < γ) (M : ℝ) :
    shockPressureRatio γ M = (2 * γ * M ^ 2 - γ + 1) / (γ + 1) := by
  have : γ + 1 ≠ 0 := by linarith
  unfold shockPressureRatio; field_simp; ring

/-- Closed form `M₂² = ((γ-1)M₁² + 2)/(2γM₁² - γ + 1)`. -/
theorem shockMachSq_eq (γ M : ℝ) :
    shockMachSq γ M = ((γ - 1) * M ^ 2 + 2) / (2 * γ * M ^ 2 - γ + 1) := by
  unfold shockMachSq
  rw [← mul_div_mul_right _ _ (two_ne_zero (α := ℝ))]
  congr 1 <;> ring

section Conservation

variable {M ρ₁ p₁ V₁ : ℝ}

/-- **Conservation of mass** across the shock: `ρ₁ V₁ = ρ₂ V₂` with `ρ₂ = ρ₁ r`,
`V₂ = V₁ / r`. -/
theorem normalShock_mass (hγ : 1 < γ) (hM : M ≠ 0) :
    ρ₁ * V₁ = (ρ₁ * shockDensityRatio γ M) * (V₁ / shockDensityRatio γ M) := by
  have := (shockDensityRatio_pos hγ hM).ne'
  field_simp

/-- **Conservation of momentum** across the shock: `p₁ + ρ₁V₁² = p₂ + ρ₂V₂²`, where
`V₁² = M₁² γ p₁ / ρ₁`. -/
theorem normalShock_momentum (hγ : 1 < γ) (hM : M ≠ 0) (hρ : 0 < ρ₁)
    (hV : V₁ ^ 2 = M ^ 2 * (γ * p₁ / ρ₁)) :
    p₁ + ρ₁ * V₁ ^ 2 = p₁ * shockPressureRatio γ M +
      (ρ₁ * shockDensityRatio γ M) * (V₁ / shockDensityRatio γ M) ^ 2 := by
  have hr := (shockDensityRatio_pos hγ hM).ne'
  have h1 : (γ - 1) * M ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg M]
  have h2 : γ + 1 ≠ 0 := by linarith
  have hM2 : M ^ 2 ≠ 0 := by positivity
  rw [div_pow, hV]
  unfold shockPressureRatio shockDensityRatio at *
  field_simp
  ring

/-- **Conservation of energy** across the shock:
`γ/(γ-1) p₁/ρ₁ + V₁²/2 = γ/(γ-1) p₂/ρ₂ + V₂²/2`. -/
theorem normalShock_energy (hγ : 1 < γ) (hM : M ≠ 0) (hρ : 0 < ρ₁)
    (hV : V₁ ^ 2 = M ^ 2 * (γ * p₁ / ρ₁)) :
    γ / (γ - 1) * (p₁ / ρ₁) + V₁ ^ 2 / 2 =
      γ / (γ - 1) * (p₁ * shockPressureRatio γ M / (ρ₁ * shockDensityRatio γ M)) +
        (V₁ / shockDensityRatio γ M) ^ 2 / 2 := by
  have h1 : (γ - 1) * M ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg M]
  have h2 : γ + 1 ≠ 0 := by linarith
  have h3 : γ - 1 ≠ 0 := by linarith
  have hM2 : M ^ 2 ≠ 0 := by positivity
  rw [div_pow, hV]
  unfold shockPressureRatio shockDensityRatio
  field_simp
  ring

/-- **Downstream Mach number**: `V₂² = M₂² c₂²` with `c₂² = γ p₂ / ρ₂`. -/
theorem normalShock_mach (hγ : 1 < γ) (hM : M ≠ 0) (hP : (γ - 1) / (2 * γ) < M ^ 2)
    (hρ : 0 < ρ₁) (hp : 0 < p₁) (hV : V₁ ^ 2 = M ^ 2 * (γ * p₁ / ρ₁)) :
    (V₁ / shockDensityRatio γ M) ^ 2 =
      shockMachSq γ M * (γ * (p₁ * shockPressureRatio γ M) / (ρ₁ * shockDensityRatio γ M)) := by
  have h1 : (γ - 1) * M ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg M]
  have h2 : γ + 1 ≠ 0 := by linarith
  have hM2 : M ^ 2 ≠ 0 := by positivity
  have h4 : 2 * γ * M ^ 2 - γ + 1 ≠ 0 := by
    have : 0 < 2 * γ := by linarith
    rw [div_lt_iff₀ this] at hP
    linarith
  rw [div_pow, hV, shockPressureRatio_eq hγ, shockMachSq_eq]
  generalize 2 * γ * M ^ 2 - γ + 1 = D at h4 ⊢
  unfold shockDensityRatio
  field_simp

end Conservation

/-- Behind a shock the flow is subsonic: `M₁ > 1 ⇒ M₂² < 1`. -/
theorem shockMachSq_lt_one (hγ : 1 < γ) {M : ℝ} (hM : 1 < M) : shockMachSq γ M < 1 := by
  have : 1 < M ^ 2 := by nlinarith
  unfold shockMachSq
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- `M₂² > 0`, so `M₂ = √(M₂²)` is a genuine Mach number in `(0, 1)`. -/
theorem shockMachSq_pos (hγ : 1 < γ) {M : ℝ} (hM : 1 < M) : 0 < shockMachSq γ M := by
  have : 1 < M ^ 2 := by nlinarith
  unfold shockMachSq
  exact div_pos (by nlinarith) (by nlinarith)

/-- The pressure rises across a shock: `p₂ > p₁`. -/
theorem one_lt_shockPressureRatio (hγ : 1 < γ) {M : ℝ} (hM : 1 < M) :
    1 < shockPressureRatio γ M := by
  have : 1 < M ^ 2 := by nlinarith
  unfold shockPressureRatio
  have : 0 < 2 * γ / (γ + 1) := div_pos (by linarith) (by linarith)
  nlinarith

/-- The density rises across a shock: `ρ₂ > ρ₁`. -/
theorem one_lt_shockDensityRatio (hγ : 1 < γ) {M : ℝ} (hM : 1 < M) :
    1 < shockDensityRatio γ M := by
  have : 1 < M ^ 2 := by nlinarith
  unfold shockDensityRatio
  rw [one_lt_div (by nlinarith)]
  nlinarith

/-- **Limiting compression**: `ρ₂/ρ₁ < (γ + 1)/(γ - 1)` for every Mach number. -/
theorem shockDensityRatio_lt (hγ : 1 < γ) (M : ℝ) :
    shockDensityRatio γ M < (γ + 1) / (γ - 1) := by
  have := sq_nonneg M
  unfold shockDensityRatio
  rw [div_lt_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/-- The limiting compression `(γ + 1)/(γ - 1)` is attained as `M₁ → ∞`. -/
theorem tendsto_shockDensityRatio (hγ : 1 < γ) :
    Tendsto (shockDensityRatio γ) atTop (𝓝 ((γ + 1) / (γ - 1))) := by
  have h0 : Tendsto (fun M : ℝ => 2 / M ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h := (tendsto_const_nhds (x := γ + 1)).div (h0.const_add (γ - 1))
    (by rw [add_zero]; linarith)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  have : (γ - 1) * M ^ 2 + 2 ≠ 0 := by nlinarith [sq_nonneg M]
  change (γ + 1) / (γ - 1 + 2 / M ^ 2) = _
  have : M ^ 2 ≠ 0 := by positivity
  unfold shockDensityRatio
  rw [← mul_div_mul_right _ _ this]
  congr 1; field_simp

/-- As `M₁ → ∞`, `M₂² → (γ - 1)/(2γ)`. -/
theorem tendsto_shockMachSq (hγ : 1 < γ) :
    Tendsto (shockMachSq γ) atTop (𝓝 ((γ - 1) / (2 * γ))) := by
  have h0 : Tendsto (fun M : ℝ => 1 / M ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hnum := h0.add (tendsto_const_nhds (x := (γ - 1) / 2))
  have hden := (tendsto_const_nhds (x := γ)).sub (h0.const_mul ((γ - 1) / 2))
  have h := hnum.div hden (by rw [mul_zero, sub_zero]; linarith)
  rw [zero_add, mul_zero, sub_zero, div_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  have : M ^ 2 ≠ 0 := by positivity
  change (1 / M ^ 2 + (γ - 1) / 2) / (γ - (γ - 1) / 2 * (1 / M ^ 2)) = _
  unfold shockMachSq
  rw [← mul_div_mul_right _ _ this]
  congr 1 <;> field_simp

/-! ### Entropy jump across a shock -/

/-- The entropy jump across a normal shock in units of `c_v`,
`Δs / c_v = log((p₂/p₁)(ρ₂/ρ₁)^{-γ})`. -/
def shockEntropyJump (γ M : ℝ) : ℝ :=
  log (shockPressureRatio γ M * (shockDensityRatio γ M)⁻¹ ^ γ)

/-- The entropy jump as a function of `u = M₁²`. -/
def entropyFun (γ u : ℝ) : ℝ :=
  log (1 + 2 * γ / (γ + 1) * (u - 1)) - γ * (log ((γ + 1) * u) - log ((γ - 1) * u + 2))

/-- `Δs/c_v = log(p₂/p₁) - γ log(ρ₂/ρ₁) = entropyFun γ M₁²`. -/
theorem shockEntropyJump_eq (hγ : 1 < γ) {M : ℝ} (hM : (γ - 1) / (2 * γ) < M ^ 2) :
    shockEntropyJump γ M = entropyFun γ (M ^ 2) := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    have : 0 < (γ - 1) / (2 * γ) := div_pos (by linarith) (by linarith)
    simp at hM; linarith
  have hP := shockPressureRatio_pos hγ hM
  have hr := shockDensityRatio_pos hγ hM0
  have h1 : 0 < (γ + 1) * M ^ 2 := by have : 0 < M ^ 2 := by positivity
                                      nlinarith
  rw [shockEntropyJump, log_mul hP.ne' (rpow_pos_of_pos (inv_pos.2 hr) _).ne',
    log_rpow (inv_pos.2 hr), log_inv, shockDensityRatio, log_div h1.ne' (by nlinarith),
    entropyFun, shockPressureRatio]
  ring

/-- The derivative of the entropy function:
`f'(u) = 2γ(γ-1)(u-1)² / ((2γu - γ + 1) u ((γ-1)u + 2))`. -/
theorem hasDerivAt_entropyFun (hγ : 1 < γ) {u : ℝ} (hu : (γ - 1) / (2 * γ) < u) :
    HasDerivAt (entropyFun γ)
      (2 * γ * (γ - 1) * (u - 1) ^ 2 /
        ((2 * γ * u - γ + 1) * u * ((γ - 1) * u + 2))) u := by
  have hg : 0 < 2 * γ := by linarith
  have hu' := hu
  rw [div_lt_iff₀ hg] at hu'
  have hu0 : 0 < u := by
    have : 0 < (γ - 1) / (2 * γ) := div_pos (by linarith) hg
    linarith
  have h2 : γ + 1 ≠ 0 := by linarith
  have hP : 1 + 2 * γ / (γ + 1) * (u - 1) ≠ 0 := by
    have : 1 + 2 * γ / (γ + 1) * (u - 1) = (u * (2 * γ) - (γ - 1)) / (γ + 1) := by
      field_simp; ring
    rw [this]; exact (div_pos (by linarith) (by linarith)).ne'
  have hA : (γ + 1) * u ≠ 0 := by positivity
  have hB : (γ - 1) * u + 2 ≠ 0 := by nlinarith
  have d1 : HasDerivAt (fun u => 1 + 2 * γ / (γ + 1) * (u - 1)) (2 * γ / (γ + 1)) u := by
    simpa using ((hasDerivAt_id u).sub_const 1).const_mul (2 * γ / (γ + 1)) |>.const_add 1
  have d2 : HasDerivAt (fun u => (γ + 1) * u) (γ + 1) u := by
    simpa using (hasDerivAt_id u).const_mul (γ + 1)
  have d3 : HasDerivAt (fun u => (γ - 1) * u + 2) (γ - 1) u := by
    simpa using ((hasDerivAt_id u).const_mul (γ - 1)).add_const 2
  have hd := (d1.log hP).sub (((d2.log hA).sub (d3.log hB)).const_mul γ)
  convert hd using 1
  · funext y; simp only [entropyFun, Pi.sub_apply]
  have h5 : 2 * γ * u - γ + 1 ≠ 0 := by linarith
  have e1 : 2 * γ / (γ + 1) / (1 + 2 * γ / (γ + 1) * (u - 1)) = 2 * γ / (2 * γ * u - γ + 1) := by
    rw [div_eq_div_iff hP h5]; field_simp; ring
  rw [e1]
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * γ * u - γ + 1 := ⟨_, rfl⟩
  rw [← hD] at h5 ⊢
  field_simp
  subst hD
  ring

/-- The entropy function vanishes at `M₁ = 1` (no shock). -/
theorem entropyFun_one (γ : ℝ) : entropyFun γ 1 = 0 := by
  rw [entropyFun]; ring_nf; simp

/-- **Entropy increases across a compression shock**: `Δs > 0` for `M₁ > 1`. -/
theorem shockEntropyJump_pos (hγ : 1 < γ) {M : ℝ} (hM : 1 < M) : 0 < shockEntropyJump γ M := by
  have hg : 0 < 2 * γ := by linarith
  have ha : (γ - 1) / (2 * γ) < 1 := by rw [div_lt_one hg]; linarith
  have hM2 : 1 < M ^ 2 := by nlinarith
  rw [shockEntropyJump_eq hγ (by linarith), ← entropyFun_one γ]
  have hmono : StrictMonoOn (entropyFun γ) (Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · intro x hx
      exact (hasDerivAt_entropyFun hγ (lt_of_lt_of_le ha hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx : 1 < x := hx
      rw [(hasDerivAt_entropyFun hγ (by linarith)).deriv]
      have : 0 < 2 * γ * x - γ + 1 := by nlinarith
      have : 0 < (x - 1) ^ 2 := by have : x - 1 ≠ 0 := by linarith
                                   positivity
      have : 0 < 2 * γ * (γ - 1) := by nlinarith
      exact div_pos (by positivity) (mul_pos (mul_pos ‹_› (by linarith)) (by nlinarith))
  exact hmono (le_refl (1 : ℝ)) (le_of_lt hM2 : (1 : ℝ) ≤ M ^ 2) hM2

/-- **Expansion shocks are impossible**: for `M₁ < 1` (with `M₁² > (γ-1)/(2γ)`, so that
`p₂ > 0`) the entropy would decrease, `Δs < 0`, violating the second law. -/
theorem shockEntropyJump_neg (hγ : 1 < γ) {M : ℝ} (hM0 : 0 ≤ M) (hM : M < 1)
    (hP : (γ - 1) / (2 * γ) < M ^ 2) : shockEntropyJump γ M < 0 := by
  have hM2 : M ^ 2 < 1 := by nlinarith
  rw [shockEntropyJump_eq hγ hP, ← entropyFun_one γ]
  set a := (γ - 1) / (2 * γ)
  have hmono : StrictMonoOn (entropyFun γ) (Ioc a 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc a 1) ?_ ?_
    · intro x hx
      exact (hasDerivAt_entropyFun hγ hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hasDerivAt_entropyFun hγ hx.1).deriv]
      have hx1 := hx.1
      have hg : 0 < 2 * γ := by linarith
      rw [div_lt_iff₀ hg] at hx1
      have hx0 : 0 < x := by
        have : 0 < a := div_pos (by linarith) hg
        linarith [hx.1]
      have : 0 < 2 * γ * x - γ + 1 := by linarith
      have : 0 < (x - 1) ^ 2 := by have : x - 1 ≠ 0 := by linarith [hx.2]
                                   positivity
      have : 0 < 2 * γ * (γ - 1) := by nlinarith
      exact div_pos (by positivity) (mul_pos (mul_pos ‹_› hx0) (by nlinarith))
  exact hmono ⟨hP, hM2.le⟩ ⟨by rw [div_lt_one (by linarith)]; linarith, le_rfl⟩ hM2

end ContinuumMechanics.Fluids.Compressible
