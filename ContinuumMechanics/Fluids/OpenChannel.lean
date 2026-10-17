import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Open-channel hydraulics

Steady flow in a wide rectangular channel with discharge per unit width `q > 0`, depth
`y > 0`, mean velocity `V = q / y` and gravitational acceleration `g > 0`.

## Main definitions

* `specificEnergy g q y = y + q² / (2 g y²)`, the head above the channel bed.
* `criticalDepth g q = (q² / g)^{1/3}`.
* `froude g q y = V / √(g y)`, the Froude number (`√(g y)` is the shallow-water wave speed).
* `momentumFunction g q y = q² / (g y) + y² / 2`, the specific force.
* `hydraulicRadius`, `rectHydraulicRadius`, `manningVelocity`, `chezyVelocity`: uniform flow.
* `weirDischarge g H = (2/3) √(2g) H^{3/2}`.

## Main results

* `strictConvexOn_specificEnergy`, `tendsto_specificEnergy_zero`,
  `tendsto_specificEnergy_atTop`: `E` is strictly convex and tends to `∞` at both ends.
* `strictAntiOn_specificEnergy`, `strictMonoOn_specificEnergy`: `E` decreases on `(0, y_c]`
  and increases on `[y_c, ∞)`.
* `specificEnergy_criticalDepth`, `specificEnergy_lt_specificEnergy`, `isMinOn_specificEnergy`:
  the unique minimum `E_min = (3/2) y_c` is attained at the critical depth.
* `froude_criticalDepth`, `one_lt_froude_iff`, `froude_lt_one_iff`: `Fr = 1` at `y_c`; the flow
  is supercritical iff `y < y_c` and subcritical iff `y > y_c`.
* `exists_alternate_depths`: for `E > E_min` there are exactly two depths `y₁ < y_c < y₂`
  with specific energy `E`.
* `sequent_relation`: sequent depths satisfy `y₁ y₂ (y₁ + y₂) = 2 y_c³`.
* `momentum_balance_iff`: the mass and momentum balance across a jump is `M(y₁) = M(y₂)`.
* `belanger`: the sequent depth ratio `y₂/y₁ = (√(1 + 8 Fr₁²) - 1)/2`.
* `lt_of_supercritical`, `criticalDepth_mem_Ioo`: a jump from supercritical flow increases
  the depth; sequent depths straddle the critical depth.
* `jump_energy_loss`, `jump_energy_loss_nonneg`, `specificEnergy_lt_of_subcritical`: the head
  loss `ΔE = (y₂ - y₁)³ / (4 y₁ y₂)`; a jump from subcritical flow would create energy.
* `manning_eq_chezy`, `tendsto_rectHydraulicRadius`, `tendsto_manningVelocity_wide`: Manning and
  Chézy formulas and the wide-channel limit `R → y`.
* `perimeter_le_of_best`, `hydraulicRadius_le_of_best`: the most efficient rectangular section
  has `b = 2y`.
* `integral_weir`: `∫₀ᴴ √(2 g h) dh = (2/3) √(2g) H^{3/2}`.

## References

* [Chow1959] V. T. Chow, *Open-Channel Hydraulics*, chs. 3, 5, 6, 15.
* [Henderson1966] F. M. Henderson, *Open Channel Flow*, chs. 2–4.
-/

open Real Filter Topology Set

noncomputable section

namespace ContinuumMechanics.Fluids.OpenChannel

/-! ### Specific energy and critical depth -/

/-- Specific energy (head above the bed) `E(y) = y + q² / (2 g y²)` of a rectangular channel. -/
def specificEnergy (g q y : ℝ) : ℝ := y + q ^ 2 / (2 * g * y ^ 2)

/-- The critical depth `y_c = (q² / g)^{1/3}`. -/
def criticalDepth (g q : ℝ) : ℝ := (q ^ 2 / g) ^ (1 / 3 : ℝ)

/-- The Froude number `Fr = V / √(g y)` with `V = q / y`. -/
def froude (g q y : ℝ) : ℝ := q / y / √(g * y)

variable {g q : ℝ}

/-- The critical depth is positive. -/
theorem criticalDepth_pos (hg : 0 < g) (hq : 0 < q) : 0 < criticalDepth g q :=
  rpow_pos_of_pos (by positivity) _

/-- The defining property of the critical depth: `y_c³ = q² / g`. -/
theorem criticalDepth_pow_three (hg : 0 < g) : criticalDepth g q ^ 3 = q ^ 2 / g := by
  have h : 0 ≤ q ^ 2 / g := by positivity
  rw [criticalDepth, ← rpow_natCast, ← rpow_mul h]
  norm_num

/-- The specific energy written with the critical depth: `E(y) = y + y_c³ / (2 y²)`. -/
theorem specificEnergy_eq (hg : 0 < g) (y : ℝ) :
    specificEnergy g q y = y + criticalDepth g q ^ 3 / (2 * y ^ 2) := by
  rw [criticalDepth_pow_three hg, specificEnergy, div_div]
  ring

/-- `E` is continuous on `(0, ∞)`. -/
theorem continuousOn_specificEnergy (hg : 0 < g) : ContinuousOn (specificEnergy g q) (Ioi 0) := by
  unfold specificEnergy
  exact continuousOn_id.add (continuousOn_const.div (by fun_prop) fun y (hy : 0 < y) =>
    (mul_pos (mul_pos two_pos hg) (pow_pos hy 2)).ne')

/-- The specific energy is strictly convex on `(0, ∞)` (for `q ≠ 0`). -/
theorem strictConvexOn_specificEnergy (hg : 0 < g) (hq : q ≠ 0) :
    StrictConvexOn ℝ (Ioi 0) (specificEnergy g q) := by
  set K := criticalDepth g q ^ 3 / 2
  have hK : 0 < K := by
    have := criticalDepth_pow_three (q := q) hg
    have : 0 < q ^ 2 / g := by positivity
    simp only [K]; linarith
  have h2 : StrictConvexOn ℝ (Ioi 0) fun y : ℝ => K * y ^ (-2 : ℤ) := by
    refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (strictConvexOn_zpow (m := -2) (by norm_num) (by norm_num)).2 hx hy hxy ha hb hab
    calc K * (a • x + b • y) ^ (-2 : ℤ) < K * (a • x ^ (-2 : ℤ) + b • y ^ (-2 : ℤ)) :=
          mul_lt_mul_of_pos_left this hK
      _ = _ := by simp only [smul_eq_mul]; ring
  refine ((convexOn_id (convex_Ioi 0)).add_strictConvexOn h2).congr fun y _ => ?_
  simp only [Pi.add_apply, id, zpow_neg, zpow_ofNat, specificEnergy_eq hg, K]
  ring

/-- `E(y) → ∞` as `y → 0⁺` (for `q ≠ 0`). -/
theorem tendsto_specificEnergy_zero (hg : 0 < g) (hq : q ≠ 0) :
    Tendsto (specificEnergy g q) (𝓝[>] 0) atTop := by
  have hK : 0 < q ^ 2 / (2 * g) := by positivity
  have h := ((tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero).const_mul_atTop hK
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [Function.comp, specificEnergy, inv_pow]
  rw [← div_eq_mul_inv, div_div, mul_assoc]
  linarith

/-- `E(y) → ∞` as `y → ∞`. -/
theorem tendsto_specificEnergy_atTop (hg : 0 < g) :
    Tendsto (specificEnergy g q) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ tendsto_id
  filter_upwards [eventually_gt_atTop 0] with y hy
  simp only [id, specificEnergy]
  have : 0 ≤ q ^ 2 / (2 * g * y ^ 2) := by positivity
  linarith

/-- Factorization of the energy difference:
`E(b) - E(a) = (b - a)(2a²b² - y_c³(a + b)) / (2a²b²)`. -/
theorem specificEnergy_sub (hg : 0 < g) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    specificEnergy g q b - specificEnergy g q a =
      (b - a) * (2 * a ^ 2 * b ^ 2 - criticalDepth g q ^ 3 * (a + b)) / (2 * a ^ 2 * b ^ 2) := by
  rw [specificEnergy_eq hg, specificEnergy_eq hg]
  field_simp
  ring

/-- `E` is strictly decreasing on the supercritical branch `(0, y_c]`. -/
theorem strictAntiOn_specificEnergy (hg : 0 < g) :
    StrictAntiOn (specificEnergy g q) (Ioc 0 (criticalDepth g q)) := by
  intro a ⟨ha, _⟩ b ⟨hb, hbc⟩ hab
  rw [← sub_pos, specificEnergy_sub hg hb.ne' ha.ne']
  have h3 : b ^ 3 ≤ criticalDepth g q ^ 3 := pow_le_pow_left₀ hb.le hbc 3
  have h4 : b ^ 3 * (b + a) ≤ criticalDepth g q ^ 3 * (b + a) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : 0 < b ^ 2 * ((b - a) * (b + 2 * a)) := by
    have := sub_pos.2 hab
    positivity
  apply div_pos _ (by positivity)
  apply mul_pos_of_neg_of_neg (by linarith)
  nlinarith

/-- `E` is strictly increasing on the subcritical branch `[y_c, ∞)`. -/
theorem strictMonoOn_specificEnergy (hg : 0 < g) (hq : 0 < q) :
    StrictMonoOn (specificEnergy g q) (Ici (criticalDepth g q)) := by
  intro a (hca : _ ≤ a) b (_ : _ ≤ b) hab
  have hc := criticalDepth_pos hg hq
  have ha : 0 < a := hc.trans_le hca
  have hb : 0 < b := ha.trans hab
  rw [← sub_pos, specificEnergy_sub hg ha.ne' hb.ne']
  have h3 : criticalDepth g q ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hc.le hca 3
  have h4 : criticalDepth g q ^ 3 * (a + b) ≤ a ^ 3 * (a + b) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : 0 < a ^ 2 * ((b - a) * (a + 2 * b)) := by
    have := sub_pos.2 hab
    positivity
  apply div_pos _ (by positivity)
  apply mul_pos (by linarith)
  nlinarith

/-- The minimum specific energy `E_min = E(y_c) = (3/2) y_c`. -/
theorem specificEnergy_criticalDepth (hg : 0 < g) (hq : 0 < q) :
    specificEnergy g q (criticalDepth g q) = 3 / 2 * criticalDepth g q := by
  have := (criticalDepth_pos hg hq).ne'
  rw [specificEnergy_eq hg]
  field_simp
  ring

/-- The critical depth is the unique minimizer: `E(y_c) < E(y)` for every other `y > 0`. -/
theorem specificEnergy_lt_specificEnergy (hg : 0 < g) (hq : 0 < q) {y : ℝ} (hy : 0 < y)
    (hne : y ≠ criticalDepth g q) :
    specificEnergy g q (criticalDepth g q) < specificEnergy g q y := by
  have hc := criticalDepth_pos hg hq
  rcases hne.lt_or_gt with h | h
  · exact strictAntiOn_specificEnergy hg ⟨hy, h.le⟩ ⟨hc, le_rfl⟩ h
  · exact strictMonoOn_specificEnergy hg hq
      (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

/-- `y_c` minimizes `E` on `(0, ∞)`. -/
theorem isMinOn_specificEnergy (hg : 0 < g) (hq : 0 < q) :
    IsMinOn (specificEnergy g q) (Ioi 0) (criticalDepth g q) := by
  refine isMinOn_iff.2 fun y (hy : 0 < y) => ?_
  rcases eq_or_ne y (criticalDepth g q) with rfl | hne
  · exact le_rfl
  · exact (specificEnergy_lt_specificEnergy hg hq hy hne).le

/-- `Fr² = y_c³ / y³`. -/
theorem froude_sq (hg : 0 < g) {y : ℝ} (hy : 0 < y) :
    froude g q y ^ 2 = criticalDepth g q ^ 3 / y ^ 3 := by
  rw [froude, div_pow, sq_sqrt (by positivity), criticalDepth_pow_three hg]
  field_simp

/-- The Froude number is positive. -/
theorem froude_pos (hg : 0 < g) (hq : 0 < q) {y : ℝ} (hy : 0 < y) : 0 < froude g q y := by
  unfold froude
  positivity

/-- At the critical depth the flow is critical: `Fr = 1`. -/
theorem froude_criticalDepth (hg : 0 < g) (hq : 0 < q) : froude g q (criticalDepth g q) = 1 := by
  have hc := criticalDepth_pos hg hq
  have h := froude_sq (q := q) hg hc
  rw [div_self (pow_pos hc 3).ne'] at h
  exact (pow_eq_one_iff_of_nonneg (froude_pos hg hq hc).le two_ne_zero).1 h

/-- Comparison of the Froude number with `1` through its square. -/
theorem one_lt_froude_iff_aux (hg : 0 < g) (hq : 0 < q) {y : ℝ} (hy : 0 < y) :
    1 < froude g q y ↔ y ^ 3 < criticalDepth g q ^ 3 := by
  rw [← one_lt_sq_iff₀ (froude_pos hg hq hy).le, froude_sq hg hy, one_lt_div (pow_pos hy 3)]

/-- Supercritical flow: `Fr > 1` iff `y < y_c`. -/
theorem one_lt_froude_iff (hg : 0 < g) (hq : 0 < q) {y : ℝ} (hy : 0 < y) :
    1 < froude g q y ↔ y < criticalDepth g q := by
  rw [one_lt_froude_iff_aux hg hq hy,
    pow_lt_pow_iff_left₀ hy.le (criticalDepth_pos hg hq).le three_ne_zero]

/-- Subcritical flow: `Fr < 1` iff `y > y_c`. -/
theorem froude_lt_one_iff (hg : 0 < g) (hq : 0 < q) {y : ℝ} (hy : 0 < y) :
    froude g q y < 1 ↔ criticalDepth g q < y := by
  rw [← sq_lt_one_iff₀ (froude_pos hg hq hy).le, froude_sq hg hy, div_lt_one (pow_pos hy 3),
    pow_lt_pow_iff_left₀ (criticalDepth_pos hg hq).le hy.le three_ne_zero]

/-- **Alternate depths.** For a specific energy `E₀ > E_min` there are exactly two depths,
a supercritical one `y₁ < y_c` and a subcritical one `y₂ > y_c`, with `E(y) = E₀`. -/
theorem exists_alternate_depths (hg : 0 < g) (hq : 0 < q) {E₀ : ℝ}
    (hE : specificEnergy g q (criticalDepth g q) < E₀) :
    ∃ y₁ y₂, 0 < y₁ ∧ y₁ < criticalDepth g q ∧ criticalDepth g q < y₂ ∧
      ∀ y, 0 < y → (specificEnergy g q y = E₀ ↔ y = y₁ ∨ y = y₂) := by
  set c := criticalDepth g q with hcdef
  have hc : 0 < c := criticalDepth_pos hg hq
  have hcont := continuousOn_specificEnergy (q := q) hg
  -- the supercritical branch
  obtain ⟨y₀, hy₀E, hy₀⟩ := (((tendsto_specificEnergy_zero hg hq.ne').eventually_gt_atTop E₀).and
    (Ioo_mem_nhdsGT hc)).exists
  obtain ⟨y₁, ⟨hy₁0, hy₁c⟩, hy₁⟩ := intermediate_value_Icc' hy₀.2.le
    (hcont.mono fun y hy => hy₀.1.trans_le hy.1) ⟨hE.le, hy₀E.le⟩
  have hy₁c' : y₁ < c := hy₁c.lt_of_ne (by rintro rfl; exact hE.ne hy₁)
  -- the subcritical branch
  have hcE : c < E₀ := by rw [specificEnergy_criticalDepth hg hq] at hE; linarith
  have hEE : E₀ ≤ specificEnergy g q E₀ := by
    have : 0 ≤ q ^ 2 / (2 * g * E₀ ^ 2) := by positivity
    simp only [specificEnergy]; linarith
  obtain ⟨y₂, ⟨hy₂c, _⟩, hy₂⟩ := intermediate_value_Icc hcE.le
    (hcont.mono fun y hy => hc.trans_le hy.1) ⟨hE.le, hEE⟩
  have hy₂c' : c < y₂ := hy₂c.lt_of_ne (by rintro rfl; exact hE.ne hy₂)
  have hy₁pos : 0 < y₁ := hy₀.1.trans_le hy₁0
  refine ⟨y₁, y₂, hy₁pos, hy₁c', hy₂c', fun y hy => ⟨fun h => ?_, ?_⟩⟩
  · rcases lt_trichotomy y c with hlt | rfl | hgt
    · exact Or.inl ((strictAntiOn_specificEnergy hg).injOn ⟨hy, hlt.le⟩ ⟨hy₁pos, hy₁c'.le⟩
        (h.trans hy₁.symm))
    · exact absurd h hE.ne
    · exact Or.inr ((strictMonoOn_specificEnergy hg hq).injOn (le_of_lt hgt) (le_of_lt hy₂c')
        (h.trans hy₂.symm))
  · rintro (rfl | rfl)
    · exact hy₁
    · exact hy₂

/-! ### The hydraulic jump -/

/-- The momentum function (specific force per unit width) `M(y) = q² / (g y) + y² / 2`. -/
def momentumFunction (g q y : ℝ) : ℝ := q ^ 2 / (g * y) + y ^ 2 / 2

/-- Momentum flux plus hydrostatic thrust `ρ V² y + ρ g y² / 2` equals `ρ g M(y)` when
`V = q / y`. -/
theorem momentumFlux_eq (ρ : ℝ) (hg : 0 < g) {y : ℝ} (hy : 0 < y) :
    ρ * (q / y) ^ 2 * y + ρ * g * y ^ 2 / 2 = ρ * g * momentumFunction g q y := by
  unfold momentumFunction
  field_simp

/-- **Jump conditions.** With mass conservation `V₁ y₁ = V₂ y₂ = q`, the momentum balance
`ρ V₁² y₁ + ρ g y₁² / 2 = ρ V₂² y₂ + ρ g y₂² / 2` across a jump is `M(y₁) = M(y₂)`. -/
theorem momentum_balance_iff {ρ V₁ V₂ y₁ y₂ : ℝ} (hρ : 0 < ρ) (hg : 0 < g) (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) (h₁ : V₁ * y₁ = q) (h₂ : V₂ * y₂ = q) :
    ρ * V₁ ^ 2 * y₁ + ρ * g * y₁ ^ 2 / 2 = ρ * V₂ ^ 2 * y₂ + ρ * g * y₂ ^ 2 / 2 ↔
      momentumFunction g q y₁ = momentumFunction g q y₂ := by
  obtain rfl : V₁ = q / y₁ := eq_div_of_mul_eq hy₁.ne' h₁
  obtain rfl : V₂ = q / y₂ := eq_div_of_mul_eq hy₂.ne' h₂
  rw [momentumFlux_eq ρ hg hy₁, momentumFlux_eq ρ hg hy₂]
  exact mul_right_inj' (mul_pos hρ hg).ne'

/-- Sequent depths `y₁ ≠ y₂` with `M(y₁) = M(y₂)` satisfy `y₁ y₂ (y₁ + y₂) = 2 y_c³`. -/
theorem sequent_relation (hg : 0 < g) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hne : y₁ ≠ y₂) (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    y₁ * y₂ * (y₁ + y₂) = 2 * criticalDepth g q ^ 3 := by
  rw [criticalDepth_pow_three hg]
  set u := q ^ 2 / g
  unfold momentumFunction at hM
  rw [← div_div, ← div_div] at hM
  have ha : u / y₁ * y₁ = u := div_mul_cancel₀ u hy₁.ne'
  have hb : u / y₂ * y₂ = u := div_mul_cancel₀ u hy₂.ne'
  have key : (y₂ - y₁) * (y₁ * y₂ * (y₁ + y₂) - 2 * u) = 0 := by
    linear_combination (-2 * y₁ * y₂) * hM + (2 * y₂) * ha - (2 * y₁) * hb
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · linarith

/-- **Bélanger's equation.** Sequent depths of a hydraulic jump satisfy
`y₂ / y₁ = (√(1 + 8 Fr₁²) - 1) / 2`. -/
theorem belanger (hg : 0 < g) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hne : y₂ ≠ y₁)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    y₂ / y₁ = (√(1 + 8 * froude g q y₁ ^ 2) - 1) / 2 := by
  have hrel := sequent_relation hg hy₁ hy₂ hne.symm hM
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ y₂ = r * y₁ :=
    ⟨y₂ / y₁, div_pos hy₂ hy₁, (div_mul_cancel₀ _ hy₁.ne').symm⟩
  have hF : froude g q y₁ ^ 2 = r * (1 + r) / 2 := by
    rw [froude_sq hg hy₁, div_eq_iff (pow_pos hy₁ 3).ne']
    linear_combination (-1 / 2) * hrel
  rw [mul_div_cancel_right₀ _ hy₁.ne', hF,
    show 1 + 8 * (r * (1 + r) / 2) = (2 * r + 1) ^ 2 by ring, sqrt_sq (by positivity)]
  ring

/-- Sequent depths `y₁ < y₂` straddle the critical depth: `y₁ < y_c < y₂`. -/
theorem criticalDepth_mem_Ioo (hg : 0 < g) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hlt : y₁ < y₂)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    y₁ < criticalDepth g q ∧ criticalDepth g q < y₂ := by
  have hy₂ : 0 < y₂ := hy₁.trans hlt
  have hrel := sequent_relation hg hy₁ hy₂ hlt.ne hM
  have hc3 : 0 < criticalDepth g q ^ 3 := by nlinarith [mul_pos hy₁ hy₂]
  have hc : 0 ≤ criticalDepth g q := by
    by_contra h
    replace h := not_le.1 h
    nlinarith [pow_pos (neg_pos.2 h) 3]
  have h1 : y₁ * y₁ * (y₁ + y₁) < y₁ * y₂ * (y₁ + y₂) := by gcongr
  have h2 : y₁ * y₂ * (y₁ + y₂) < y₂ * y₂ * (y₂ + y₂) := by gcongr
  constructor
  · exact (pow_lt_pow_iff_left₀ hy₁.le hc three_ne_zero).1 (by nlinarith)
  · exact (pow_lt_pow_iff_left₀ hc hy₂.le three_ne_zero).1 (by nlinarith)

/-- A hydraulic jump from supercritical flow (`Fr₁ > 1`) increases the depth: `y₁ < y₂`. -/
theorem lt_of_supercritical (hg : 0 < g) (hq : 0 < q) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) (hne : y₂ ≠ y₁) (hFr : 1 < froude g q y₁)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) : y₁ < y₂ := by
  rw [one_lt_froude_iff hg hq hy₁] at hFr
  refine hne.symm.lt_or_gt.resolve_right fun h => ?_
  exact (criticalDepth_mem_Ioo hg hy₂ h hM.symm).2.not_gt hFr

/-- **Head loss in a hydraulic jump**: `E(y₁) - E(y₂) = (y₂ - y₁)³ / (4 y₁ y₂)`. -/
theorem jump_energy_loss (hg : 0 < g) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    specificEnergy g q y₁ - specificEnergy g q y₂ = (y₂ - y₁) ^ 3 / (4 * y₁ * y₂) := by
  rcases eq_or_ne y₁ y₂ with rfl | hne
  · simp
  have hrel := sequent_relation hg hy₁ hy₂ hne hM
  rw [specificEnergy_eq hg, specificEnergy_eq hg,
    show criticalDepth g q ^ 3 = y₁ * y₂ * (y₁ + y₂) / 2 by linarith]
  field_simp
  ring

/-- The head loss of a jump to a larger depth is nonnegative. -/
theorem jump_energy_loss_nonneg (hg : 0 < g) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hle : y₁ ≤ y₂)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    specificEnergy g q y₂ ≤ specificEnergy g q y₁ := by
  have hy₂ : 0 < y₂ := hy₁.trans_le hle
  have h := jump_energy_loss hg hy₁ hy₂ hM
  have : 0 ≤ (y₂ - y₁) ^ 3 / (4 * y₁ * y₂) := by
    have := sub_nonneg.2 hle
    positivity
  linarith

/-- A "jump" from subcritical flow (`Fr₁ < 1`) would have to create energy, so it cannot
occur. -/
theorem specificEnergy_lt_of_subcritical (hg : 0 < g) (hq : 0 < q) {y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hne : y₂ ≠ y₁) (hFr : froude g q y₁ < 1)
    (hM : momentumFunction g q y₁ = momentumFunction g q y₂) :
    specificEnergy g q y₁ < specificEnergy g q y₂ := by
  rw [froude_lt_one_iff hg hq hy₁] at hFr
  have hlt : y₂ < y₁ := hne.lt_or_gt.resolve_right fun h =>
    (criticalDepth_mem_Ioo hg hy₁ h hM).1.not_gt hFr
  have h := jump_energy_loss hg hy₁ hy₂ hM
  have : (y₂ - y₁) ^ 3 / (4 * y₁ * y₂) < 0 :=
    div_neg_of_neg_of_pos (Odd.pow_neg (by decide) (sub_neg.2 hlt)) (by positivity)
  linarith

/-! ### Uniform flow -/

/-- The hydraulic radius `R = A / P` (flow area over wetted perimeter). -/
def hydraulicRadius (A P : ℝ) : ℝ := A / P

/-- Hydraulic radius of a rectangular section of width `b` and depth `y`:
`R = b y / (b + 2 y)`. -/
def rectHydraulicRadius (b y : ℝ) : ℝ := hydraulicRadius (b * y) (b + 2 * y)

/-- Manning's formula `V = (1/n) R^{2/3} S^{1/2}` (roughness `n`, bed slope `S`). -/
def manningVelocity (n R S : ℝ) : ℝ := R ^ (2 / 3 : ℝ) * S ^ (1 / 2 : ℝ) / n

/-- Chézy's formula `V = C √(R S)`. -/
def chezyVelocity (C R S : ℝ) : ℝ := C * √(R * S)

/-- Manning's formula is Chézy's formula with `C = R^{1/6} / n`. -/
theorem manning_eq_chezy (n : ℝ) {R S : ℝ} (hR : 0 < R) (hS : 0 ≤ S) :
    manningVelocity n R S = chezyVelocity (R ^ (1 / 6 : ℝ) / n) R S := by
  unfold manningVelocity chezyVelocity
  rw [sqrt_eq_rpow, mul_rpow hR.le hS, ← mul_assoc, div_mul_eq_mul_div, ← rpow_add hR]
  norm_num
  ring

/-- **Wide channel**: `R = b y / (b + 2y) → y` as `b → ∞`. -/
theorem tendsto_rectHydraulicRadius {y : ℝ} (hy : 0 < y) :
    Tendsto (fun b => rectHydraulicRadius b y) atTop (𝓝 y) := by
  have h : Tendsto (fun b : ℝ => y - 2 * y ^ 2 / (b + 2 * y)) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_id))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  unfold rectHydraulicRadius hydraulicRadius
  field_simp
  ring

/-- In a wide channel the Manning velocity tends to `(1/n) y^{2/3} S^{1/2}`. -/
theorem tendsto_manningVelocity_wide (n S : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun b => manningVelocity n (rectHydraulicRadius b y) S) atTop
      (𝓝 (manningVelocity n y S)) :=
  (((continuousAt_rpow_const _ _ (Or.inl hy.ne')).tendsto.comp
    (tendsto_rectHydraulicRadius hy)).mul_const _).div_const _

/-- **Best hydraulic section.** Among rectangular sections of equal area `A = b y`, the one with
`b = 2y` has the smallest wetted perimeter `P = b + 2y`. -/
theorem perimeter_le_of_best {b y b' y' : ℝ} (hb' : 0 < b') (hy' : 0 < y') (hy : 0 < y)
    (hA : b' * y' = b * y) (hopt : b = 2 * y) : b + 2 * y ≤ b' + 2 * y' := by
  subst hopt
  nlinarith [sq_nonneg (b' - 2 * y')]

/-- The best section also has the largest hydraulic radius for its area. -/
theorem hydraulicRadius_le_of_best {b y b' y' : ℝ} (hb' : 0 < b') (hy' : 0 < y') (hy : 0 < y)
    (hA : b' * y' = b * y) (hopt : b = 2 * y) :
    rectHydraulicRadius b' y' ≤ rectHydraulicRadius b y := by
  unfold rectHydraulicRadius hydraulicRadius
  rw [hA]
  exact div_le_div_of_nonneg_left (by subst hopt; positivity) (by subst hopt; positivity)
    (perimeter_le_of_best hb' hy' hy hA hopt)

/-- The best rectangular section has hydraulic radius `R = y / 2`. -/
theorem rectHydraulicRadius_best {y : ℝ} (hy : 0 < y) : rectHydraulicRadius (2 * y) y = y / 2 := by
  unfold rectHydraulicRadius hydraulicRadius
  field_simp
  ring

/-! ### Sharp-crested weir -/

/-- Ideal discharge per unit width over a rectangular weir with head `H`:
`q = (2/3) √(2g) H^{3/2}`. -/
def weirDischarge (g H : ℝ) : ℝ := 2 / 3 * √(2 * g) * H ^ (3 / 2 : ℝ)

/-- **Weir formula**: integrating the Torricelli velocity `√(2 g h)` over the head gives
`∫₀ᴴ √(2 g h) dh = (2/3) √(2g) H^{3/2}`. -/
theorem integral_weir (hg : 0 ≤ g) (H : ℝ) :
    ∫ h in (0 : ℝ)..H, √(2 * g * h) = weirDischarge g H := by
  have : ∫ h in (0 : ℝ)..H, √(2 * g * h) = ∫ h in (0 : ℝ)..H, √(2 * g) * h ^ (1 / 2 : ℝ) := by
    refine intervalIntegral.integral_congr fun h _ => ?_
    simp only [sqrt_mul (by positivity : 0 ≤ 2 * g) h, sqrt_eq_rpow]
  rw [this, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
    zero_rpow (by norm_num), weirDischarge]
  norm_num
  ring

end ContinuumMechanics.Fluids.OpenChannel
