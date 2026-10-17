import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The von Mises truss and snap-through

The **von Mises truss** (two-bar shallow arch): two identical linear elastic bars of axial
stiffness `k = EA/L₀` are pinned at the supports `(±a, 0)` and meet at the apex, initially at
height `h` (the *rise*). A vertical force `P` acts **downward** at the apex. By symmetry the apex
moves vertically; its current height `w` is the generalized coordinate (`w = h` unloaded,
`w = -h` the mirror, *inverted* configuration). The current bar length is
`ℓ(w) = √(a² + w²)` (`barLength`), the initial one `ℓ₀ = ℓ(h)`.

* **Exact model.** The total potential energy is
  `Π(w) = 2 · ½ k (ℓ(w) - ℓ₀)² + P w` (`potential`; the load potential is `+P w` because `P`
  points down and `w` is measured up). Its derivative is
  `Π'(w) = 2k (ℓ - ℓ₀) w/ℓ + P` (`hasDerivAt_potential`), so equilibrium is
  `P = -2k (ℓ - ℓ₀) w/ℓ`, the vertical balance of the two bar forces
  (`potentialDeriv_eq_zero_iff`). The second derivative is
  `Π''(w) = 2k (1 - ℓ₀ a²/ℓ³)` (`hasDerivAt_potentialDeriv`). For `P = 0` the configurations
  `w = h`, `w = -h` (stable, `Π = 0` is the global minimum) and `w = 0` (unstable, both bars
  compressed, `Π''(0) < 0`) are equilibria.
* **Shallow model.** With `ℓ - ℓ₀ = (w² - h²)/(ℓ + ℓ₀) ≈ (w² - h²)/(2a)` (`barLength_sub`), the
  potential becomes `Π_s(w) = k/(4a²) (w² - h²)² + P w` (`shallowPotential`), with equilibrium
  path `P = (k/a²) w (h² - w²)` (`shallowLoad`, `shallowPotentialDeriv_eq_zero_iff`).
* **Limit points.** `dP/dw = (k/a²)(h² - 3w²)` vanishes at `w = ±h/√3` (`limitPoint`);
  the **snap-through load** is `P_cr = 2kh³/(3√3 a²)` (`critLoad`). One has the factorization
  `P(w) - P_cr = -(k/a²)(w - h/√3)²(w + 2h/√3)` (`shallowLoad_sub_critLoad`), hence
  `P(w) ≤ P_cr` for every `w ≥ -2h/√3`, in particular for all `w ≥ 0`, with equality only at
  `w = h/√3` (`shallowLoad_le_critLoad`, `shallowLoad_eq_critLoad_iff`). At `P = P_cr` the only
  other equilibrium is the inverted one `w = -2h/√3`: the apex **snaps through** to it.
* **Stability.** `Π_s''(w) = (k/a²)(3w² - h²)`; equilibria with `|w| > h/√3` are strict local
  minima of `Π_s` (stable), those with `|w| < h/√3` strict local maxima (unstable)
  (`isStrictLocalMin_shallowPotential`, `isStrictLocalMax_shallowPotential`).
* **Counting equilibria.** For `0 ≤ P < P_cr` there are three equilibria
  `w₁ ≤ -h < 0 ≤ w₂ < h/√3 < w₃ ≤ h` (`exists_three_equilibria`); for every `P ≥ 0` there is an
  inverted equilibrium `w ≤ -h` (`exists_inverted_equilibrium`); for `P > P_cr` the equilibrium
  is unique and inverted, `w < -2h/√3` (`existsUnique_equilibrium_of_critLoad_lt`).

## Main results

* `hasDerivAt_potential`, `potentialDeriv_eq_zero_iff`, `hasDerivAt_potentialDeriv`: the exact
  model; `potentialDeriv_rise`, `potentialDeriv_neg_rise`, `potentialDeriv_zero`,
  `potential_neg_rise`, `potentialSecondDeriv_zero_neg`, `potentialSecondDeriv_rise_pos`.
* `hasDerivAt_shallowPotential`, `shallowPotentialDeriv_eq_zero_iff`,
  `hasDerivAt_shallowPotentialDeriv`: the shallow model.
* `hasDerivAt_shallowLoad`, `shallowLoadDeriv_eq_zero_iff`, `critLoad_eq_shallowLoad`,
  `shallowLoad_sub_critLoad`, `shallowLoad_le_critLoad`, `shallowLoad_eq_critLoad_iff`,
  `shallowLoad_eq_critLoad_iff'`: limit points and the snap-through load.
* `shallowSecondDeriv_pos_iff`, `shallowSecondDeriv_neg_iff`,
  `isStrictLocalMin_shallowPotential`, `isStrictLocalMax_shallowPotential`: stability.
* `exists_three_equilibria`, `exists_inverted_equilibrium`,
  `existsUnique_equilibrium_of_critLoad_lt`: the number of equilibria.

## References

* [vonMises1923] R. von Mises, *Über die Stabilitätsprobleme der Elastizitätstheorie*,
  ZAMM 3 (1923) 406–422.
* [BazantCedolin] Z. P. Bažant, L. Cedolin, *Stability of Structures*, §2.7 and Ch. 4.
* [ThompsonHunt1973] J. M. T. Thompson, G. W. Hunt, *A General Theory of Elastic Stability*,
  Wiley (1973).
* [PignataroRizziLuongo] M. Pignataro, N. Rizzi, A. Luongo, *Stability, Bifurcation and
  Postcritical Behaviour of Elastic Structures*, Elsevier (1991).
-/

open Filter Topology Set

noncomputable section

namespace DiscreteMechanics

namespace VonMisesTruss

/-! ### The exact model -/

/-- The current bar length `ℓ(w) = √(a² + w²)` for apex height `w` and half-span `a`. -/
def barLength (a w : ℝ) : ℝ := √(a ^ 2 + w ^ 2)

/-- The **total potential energy** of the von Mises truss (two bars of stiffness `k`, rise `h`,
downward apex load `P`) at apex height `w`: `Π(w) = 2 · ½ k (ℓ(w) - ℓ₀)² + P w`. -/
def potential (k a h P w : ℝ) : ℝ := 2 * (1 / 2 * k * (barLength a w - barLength a h) ^ 2) + P * w

/-- The derivative `Π'(w) = 2k (ℓ(w) - ℓ₀) w / ℓ(w) + P` of the exact potential. -/
def potentialDeriv (k a h P w : ℝ) : ℝ :=
  2 * k * (barLength a w - barLength a h) * w / barLength a w + P

/-- The second derivative `Π''(w) = 2k (1 - ℓ₀ a² / ℓ(w)³)` of the exact potential. -/
def potentialSecondDeriv (k a h w : ℝ) : ℝ :=
  2 * k * (1 - barLength a h * a ^ 2 / barLength a w ^ 3)

/-- The square of the bar length: `ℓ(w)² = a² + w²`. -/
theorem barLength_sq (a w : ℝ) : barLength a w ^ 2 = a ^ 2 + w ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The bar length is nonnegative. -/
theorem barLength_nonneg (a w : ℝ) : 0 ≤ barLength a w := Real.sqrt_nonneg _

/-- The bar length is positive for a nondegenerate span `a ≠ 0`. -/
theorem barLength_pos {a : ℝ} (ha : a ≠ 0) (w : ℝ) : 0 < barLength a w :=
  Real.sqrt_pos.2 (by positivity)

/-- The bar length is even in the apex height: `ℓ(-w) = ℓ(w)`. -/
@[simp] theorem barLength_neg (a w : ℝ) : barLength a (-w) = barLength a w := by
  simp [barLength]

/-- In the flat configuration `w = 0` the bar length is the half-span `|a|`. -/
theorem barLength_zero (a : ℝ) : barLength a 0 = |a| := by
  simp [barLength, Real.sqrt_sq_eq_abs]

/-- Exact elongation: `ℓ(w) - ℓ₀ = (w² - h²)/(ℓ(w) + ℓ₀)`; for a shallow truss `ℓ + ℓ₀ ≈ 2a`,
which gives the shallow approximation `ℓ - ℓ₀ ≈ (w² - h²)/(2a)`. -/
theorem barLength_sub {a : ℝ} (ha : a ≠ 0) (h w : ℝ) :
    barLength a w - barLength a h = (w ^ 2 - h ^ 2) / (barLength a w + barLength a h) := by
  have h1 := barLength_pos ha w
  have h2 := barLength_pos ha h
  rw [eq_div_iff (by positivity)]
  linear_combination barLength_sq a w - barLength_sq a h

/-- Derivative of the bar length: `ℓ'(w) = w / ℓ(w)`. -/
theorem hasDerivAt_barLength {a : ℝ} (ha : a ≠ 0) (w : ℝ) :
    HasDerivAt (barLength a) (w / barLength a w) w := by
  have hpos : (0 : ℝ) < a ^ 2 + w ^ 2 := by positivity
  have := ((hasDerivAt_id' w).fun_pow 2).const_add (a ^ 2) |>.sqrt hpos.ne'
  change HasDerivAt (fun x => √(a ^ 2 + x ^ 2)) _ w
  convert this using 1
  rw [barLength]
  field_simp
  norm_num
  ring

/-- **Derivative of the exact potential**: `Π'(w) = 2k (ℓ - ℓ₀) w/ℓ + P`. -/
theorem hasDerivAt_potential (k : ℝ) {a : ℝ} (ha : a ≠ 0) (h P w : ℝ) :
    HasDerivAt (potential k a h P) (potentialDeriv k a h P w) w := by
  have hℓ := hasDerivAt_barLength ha w
  have := ((((hℓ.sub_const (barLength a h)).fun_pow 2).const_mul (1 / 2 * k)).const_mul 2).add
    ((hasDerivAt_id' w).const_mul P)
  change HasDerivAt (fun x => 2 * (1 / 2 * k * (barLength a x - barLength a h) ^ 2) + P * x) _ w
  convert this using 1
  simp only [potentialDeriv]
  norm_num
  ring

/-- **Equilibrium of the exact model**: `Π'(w) = 0` iff `P = -2k (ℓ(w) - ℓ₀) w/ℓ(w)`, the
vertical balance of the two bar forces `k (ℓ - ℓ₀)` with direction cosines `w/ℓ`. -/
theorem potentialDeriv_eq_zero_iff (k a h P w : ℝ) :
    potentialDeriv k a h P w = 0 ↔
      P = -(2 * k * (barLength a w - barLength a h) * w / barLength a w) := by
  unfold potentialDeriv
  constructor <;> intro H <;> linarith

/-- **Second derivative of the exact potential**: `Π''(w) = 2k (1 - ℓ₀ a²/ℓ(w)³)`. -/
theorem hasDerivAt_potentialDeriv (k : ℝ) {a : ℝ} (ha : a ≠ 0) (h P w : ℝ) :
    HasDerivAt (potentialDeriv k a h P) (potentialSecondDeriv k a h w) w := by
  have hℓ := hasDerivAt_barLength ha w
  have hpos := barLength_pos ha w
  have := ((((hℓ.sub_const (barLength a h)).const_mul (2 * k)).fun_mul (hasDerivAt_id' w)).div
    hℓ hpos.ne').add_const P
  change HasDerivAt
    (fun x => 2 * k * (barLength a x - barLength a h) * x / barLength a x + P) _ w
  convert this using 1
  simp only [potentialSecondDeriv]
  have hsq := barLength_sq a w
  field_simp
  linear_combination k * barLength a h * hsq

/-- In the unloaded configuration `w = h` the exact model is in equilibrium for `P = 0`. -/
theorem potentialDeriv_rise (k a h : ℝ) : potentialDeriv k a h 0 h = 0 := by
  simp [potentialDeriv]

/-- The mirror (inverted) configuration `w = -h` is an equilibrium for `P = 0`. -/
theorem potentialDeriv_neg_rise (k a h : ℝ) : potentialDeriv k a h 0 (-h) = 0 := by
  simp [potentialDeriv]

/-- The flat configuration `w = 0` (both bars compressed) is an equilibrium for `P = 0`. -/
theorem potentialDeriv_zero (k a h : ℝ) : potentialDeriv k a h 0 0 = 0 := by
  simp [potentialDeriv]

/-- For `P = 0` the unloaded and the inverted configurations have the same energy
`Π(h) = Π(-h) = 0`. -/
theorem potential_neg_rise (k a h : ℝ) :
    potential k a h 0 (-h) = potential k a h 0 h ∧ potential k a h 0 h = 0 := by
  simp [potential]

/-- For `P = 0` and `k ≥ 0` the energy is nonnegative, so `w = ±h` are global minima. -/
theorem potential_nonneg {k : ℝ} (hk : 0 ≤ k) (a h w : ℝ) : 0 ≤ potential k a h 0 w := by
  unfold potential
  simp only [zero_mul, add_zero]
  positivity

/-- The flat equilibrium `w = 0` (for `P = 0`) is **unstable**: `Π''(0) < 0` when `k > 0`,
`a ≠ 0`, `h ≠ 0`. -/
theorem potentialSecondDeriv_zero_neg {k a h : ℝ} (hk : 0 < k) (ha : a ≠ 0) (hh : h ≠ 0) :
    potentialSecondDeriv k a h 0 < 0 := by
  unfold potentialSecondDeriv
  rw [barLength_zero]
  have habs : 0 < |a| := abs_pos.2 ha
  have hlt : |a| < barLength a h := by
    rw [barLength, Real.lt_sqrt habs.le, sq_abs]
    have : 0 < h ^ 2 := by positivity
    linarith
  have h3 : |a| ^ 3 = |a| * a ^ 2 := by rw [← sq_abs a]; ring
  have ha2 : 0 < a ^ 2 := by positivity
  have : 1 < barLength a h * a ^ 2 / |a| ^ 3 := by
    rw [one_lt_div (by positivity), h3]
    exact mul_lt_mul_of_pos_right hlt ha2
  nlinarith

/-- The equilibria `w = ±h` (for `P = 0`) are **stable**: `Π''(±h) = 2k h²/ℓ₀² > 0`. -/
theorem potentialSecondDeriv_rise_pos {k a h : ℝ} (hk : 0 < k) (ha : a ≠ 0) (hh : h ≠ 0) :
    0 < potentialSecondDeriv k a h h ∧ 0 < potentialSecondDeriv k a h (-h) := by
  have hpos := barLength_pos ha h
  have hsq := barLength_sq a h
  have key : potentialSecondDeriv k a h h = 2 * k * h ^ 2 / barLength a h ^ 2 := by
    unfold potentialSecondDeriv
    rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination hsq
  have : 0 < potentialSecondDeriv k a h h := by rw [key]; positivity
  refine ⟨this, ?_⟩
  simpa [potentialSecondDeriv] using this

/-! ### The shallow-truss approximation -/

/-- The **shallow-truss potential** `Π_s(w) = k/(4a²) (w² - h²)² + P w`, obtained from the exact
one with `ℓ - ℓ₀ ≈ (w² - h²)/(2a)`. -/
def shallowPotential (k a h P w : ℝ) : ℝ := k / (4 * a ^ 2) * (w ^ 2 - h ^ 2) ^ 2 + P * w

/-- The derivative `Π_s'(w) = (k/a²) w (w² - h²) + P` of the shallow potential. -/
def shallowPotentialDeriv (k a h P w : ℝ) : ℝ := k / a ^ 2 * w * (w ^ 2 - h ^ 2) + P

/-- The **equilibrium path** of the shallow truss: the load `P(w) = (k/a²) w (h² - w²)` that holds
the apex at height `w`. -/
def shallowLoad (k a h w : ℝ) : ℝ := k / a ^ 2 * w * (h ^ 2 - w ^ 2)

/-- The apex height of the upper **limit point**, `w = h/√3`. -/
def limitPoint (h : ℝ) : ℝ := h / √3

/-- The **snap-through (limit) load** `P_cr = 2kh³/(3√3 a²)`. -/
def critLoad (k a h : ℝ) : ℝ := 2 * k * h ^ 3 / (3 * √3 * a ^ 2)

/-- **Derivative of the shallow potential**: `Π_s'(w) = (k/a²) w (w² - h²) + P`. -/
theorem hasDerivAt_shallowPotential (k a h P w : ℝ) :
    HasDerivAt (shallowPotential k a h P) (shallowPotentialDeriv k a h P w) w := by
  have := (((((hasDerivAt_id' w).fun_pow 2).sub_const (h ^ 2)).fun_pow 2).const_mul
    (k / (4 * a ^ 2))).add ((hasDerivAt_id' w).const_mul P)
  change HasDerivAt (fun x => k / (4 * a ^ 2) * (x ^ 2 - h ^ 2) ^ 2 + P * x) _ w
  convert this using 1
  simp only [shallowPotentialDeriv]
  norm_num
  ring

/-- **Equilibrium of the shallow truss**: `Π_s'(w) = 0 ↔ P = (k/a²) w (h² - w²)`. -/
theorem shallowPotentialDeriv_eq_zero_iff (k a h P w : ℝ) :
    shallowPotentialDeriv k a h P w = 0 ↔ P = shallowLoad k a h w := by
  unfold shallowPotentialDeriv shallowLoad
  constructor <;> intro H <;> linarith

/-- **Second derivative of the shallow potential**: `Π_s''(w) = (k/a²)(3w² - h²)`. -/
theorem hasDerivAt_shallowPotentialDeriv (k a h P w : ℝ) :
    HasDerivAt (shallowPotentialDeriv k a h P) (k / a ^ 2 * (3 * w ^ 2 - h ^ 2)) w := by
  have := ((((hasDerivAt_id' w).const_mul (k / a ^ 2)).fun_mul
    (((hasDerivAt_id' w).fun_pow 2).sub_const (h ^ 2))).add_const P)
  change HasDerivAt (fun x => k / a ^ 2 * x * (x ^ 2 - h ^ 2) + P) _ w
  convert this using 1
  norm_num
  ring

/-- **Slope of the equilibrium path**: `dP/dw = (k/a²)(h² - 3w²)`. -/
theorem hasDerivAt_shallowLoad (k a h w : ℝ) :
    HasDerivAt (shallowLoad k a h) (k / a ^ 2 * (h ^ 2 - 3 * w ^ 2)) w := by
  have := ((hasDerivAt_id' w).const_mul (k / a ^ 2)).fun_mul
    (((hasDerivAt_id' w).fun_pow 2).const_sub (h ^ 2))
  change HasDerivAt (fun x => k / a ^ 2 * x * (h ^ 2 - x ^ 2)) _ w
  convert this using 1
  norm_num
  ring

/-- The square of the limit point: `3 (h/√3)² = h²`. -/
theorem limitPoint_sq (h : ℝ) : 3 * limitPoint h ^ 2 = h ^ 2 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : (√3 : ℝ) ≠ 0 := by positivity
  unfold limitPoint
  field_simp
  rw [h3]
  ring

/-- The limit point is positive for a positive rise. -/
theorem limitPoint_pos {h : ℝ} (hh : 0 < h) : 0 < limitPoint h := by
  unfold limitPoint
  positivity

/-- The limit point is nonnegative for a nonnegative rise. -/
theorem limitPoint_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ limitPoint h := by
  unfold limitPoint
  positivity

/-- The limit point lies between the flat and unloaded configurations: `h/√3 < h`. -/
theorem limitPoint_lt {h : ℝ} (hh : 0 < h) : limitPoint h < h := by
  have := limitPoint_sq h
  have := limitPoint_pos hh
  nlinarith

/-- The inverted snap-through configuration lies beyond the mirror: `-2h/√3 < -h`. -/
theorem neg_two_limitPoint_lt {h : ℝ} (hh : 0 < h) : -(2 * limitPoint h) < -h := by
  have := limitPoint_sq h
  have := limitPoint_pos hh
  nlinarith

/-- **Limit points**: for `k ≠ 0`, `a ≠ 0`, the slope `dP/dw` of the equilibrium path vanishes
exactly at `w = ±h/√3`. -/
theorem shallowLoadDeriv_eq_zero_iff {k a : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) (h w : ℝ) :
    k / a ^ 2 * (h ^ 2 - 3 * w ^ 2) = 0 ↔ w = limitPoint h ∨ w = -limitPoint h := by
  have hc : k / a ^ 2 ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hc, ← limitPoint_sq h, ← sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> intro H <;> linarith

/-- The snap-through load in terms of the limit point: `P_cr = 2k (h/√3)³/a²`. -/
theorem critLoad_eq (k a h : ℝ) : critLoad k a h = 2 * k * limitPoint h ^ 3 / a ^ 2 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : (√3 : ℝ) ≠ 0 := by positivity
  unfold critLoad limitPoint
  rw [div_pow, show (√3 : ℝ) ^ 3 = 3 * √3 by rw [pow_succ, h3]]
  ring

/-- The snap-through load is the load at the upper limit point: `P_cr = P(h/√3)`. -/
theorem critLoad_eq_shallowLoad (k a h : ℝ) :
    critLoad k a h = shallowLoad k a h (limitPoint h) := by
  rw [critLoad_eq, shallowLoad, ← limitPoint_sq h]
  ring

/-- **Factorization at the limit load**:
`P(w) - P_cr = -(k/a²) (w - h/√3)² (w + 2h/√3)`. -/
theorem shallowLoad_sub_critLoad (k a h w : ℝ) :
    shallowLoad k a h w - critLoad k a h =
      -(k / a ^ 2 * (w - limitPoint h) ^ 2 * (w + 2 * limitPoint h)) := by
  rw [critLoad_eq, shallowLoad, ← limitPoint_sq h]
  ring

/-- **No equilibrium above the limit load**: for `k ≥ 0` and `w ≥ -2h/√3` (in particular for all
`w ≥ 0` when `h ≥ 0`), `P(w) ≤ P_cr`. -/
theorem shallowLoad_le_critLoad {k : ℝ} (hk : 0 ≤ k) (a h : ℝ) {w : ℝ}
    (hw : -(2 * limitPoint h) ≤ w) : shallowLoad k a h w ≤ critLoad k a h := by
  have := shallowLoad_sub_critLoad k a h w
  have : 0 ≤ k / a ^ 2 * (w - limitPoint h) ^ 2 * (w + 2 * limitPoint h) := by
    have : 0 ≤ w + 2 * limitPoint h := by linarith
    positivity
  linarith

/-- On the physical branch `w ≥ 0` (with `k, h ≥ 0`) the load never exceeds `P_cr`. -/
theorem shallowLoad_le_critLoad_of_nonneg {k h : ℝ} (hk : 0 ≤ k) (hh : 0 ≤ h) (a : ℝ) {w : ℝ}
    (hw : 0 ≤ w) : shallowLoad k a h w ≤ critLoad k a h :=
  shallowLoad_le_critLoad hk a h (by linarith [limitPoint_nonneg hh])

/-- **The limit load is attained only at the limit point**: for `k > 0`, `a ≠ 0` and
`w > -2h/√3`, `P(w) = P_cr ↔ w = h/√3`. -/
theorem shallowLoad_eq_critLoad_iff {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) (h : ℝ) {w : ℝ}
    (hw : -(2 * limitPoint h) < w) : shallowLoad k a h w = critLoad k a h ↔ w = limitPoint h := by
  have H := shallowLoad_sub_critLoad k a h w
  have hc : k / a ^ 2 ≠ 0 := by positivity
  have h2 : w + 2 * limitPoint h ≠ 0 := by linarith
  constructor
  · intro E
    rw [E, sub_self, eq_comm, neg_eq_zero] at H
    simpa [hc, h2, sub_eq_zero] using H
  · rintro rfl
    rw [critLoad_eq_shallowLoad]

/-- **Snap-through**: at `P = P_cr` the only equilibria are the limit point `w = h/√3` and the
inverted configuration `w = -2h/√3`, to which the apex jumps. -/
theorem shallowLoad_eq_critLoad_iff' {k : ℝ} (hk : k ≠ 0) {a : ℝ} (ha : a ≠ 0) (h w : ℝ) :
    shallowLoad k a h w = critLoad k a h ↔ w = limitPoint h ∨ w = -(2 * limitPoint h) := by
  have H := shallowLoad_sub_critLoad k a h w
  have hc : k / a ^ 2 ≠ 0 := by positivity
  rw [← sub_eq_zero, H, neg_eq_zero, mul_eq_zero, mul_eq_zero, or_iff_right hc, pow_eq_zero_iff
    two_ne_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-! ### Stability of the shallow truss -/

/-- **Stable branch**: `Π_s''(w) > 0 ↔ |w| > h/√3` (for `k > 0`, `a ≠ 0`, `h ≥ 0`). -/
theorem shallowSecondDeriv_pos_iff {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) {h : ℝ}
    (hh : 0 ≤ h) (w : ℝ) : 0 < k / a ^ 2 * (3 * w ^ 2 - h ^ 2) ↔ limitPoint h < |w| := by
  have hc : 0 < k / a ^ 2 := by positivity
  rw [mul_pos_iff_of_pos_left hc, ← limitPoint_sq h, sub_pos,
    ← abs_of_nonneg (limitPoint_nonneg hh), ← sq_lt_sq, abs_of_nonneg (limitPoint_nonneg hh)]
  constructor <;> intro H <;> linarith

/-- **Unstable branch**: `Π_s''(w) < 0 ↔ |w| < h/√3` (for `k > 0`, `a ≠ 0`, `h ≥ 0`). -/
theorem shallowSecondDeriv_neg_iff {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) {h : ℝ}
    (hh : 0 ≤ h) (w : ℝ) : k / a ^ 2 * (3 * w ^ 2 - h ^ 2) < 0 ↔ |w| < limitPoint h := by
  have hc : 0 < k / a ^ 2 := by positivity
  rw [mul_neg_iff, ← limitPoint_sq h, sub_neg, ← abs_of_nonneg (limitPoint_nonneg hh), ← sq_lt_sq,
    abs_of_nonneg (limitPoint_nonneg hh)]
  constructor
  · rintro (⟨-, H⟩ | ⟨H, -⟩)
    · linarith
    · linarith
  · intro H
    exact Or.inl ⟨hc, by linarith⟩

/-- Energy increment at an equilibrium of the shallow truss: if `P = P(w₀)` then
`Π_s(w) - Π_s(w₀) = (k/(4a²)) (w - w₀)² ((w + w₀)² + 2w₀² - 2h²)`. -/
theorem shallowPotential_sub (k a h w₀ w : ℝ) :
    shallowPotential k a h (shallowLoad k a h w₀) w -
        shallowPotential k a h (shallowLoad k a h w₀) w₀ =
      k / (4 * a ^ 2) * (w - w₀) ^ 2 * ((w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2) := by
  unfold shallowPotential shallowLoad
  ring

/-- **Stable equilibria are strict local minima**: if `P = P(w₀)` with `|w₀| > h/√3`, then
`Π_s(w₀) < Π_s(w)` for all `w ≠ w₀` near `w₀`. -/
theorem isStrictLocalMin_shallowPotential {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) {h : ℝ}
    (hh : 0 ≤ h) {w₀ : ℝ} (hw : limitPoint h < |w₀|) :
    ∀ᶠ w in 𝓝[≠] w₀, shallowPotential k a h (shallowLoad k a h w₀) w₀ <
      shallowPotential k a h (shallowLoad k a h w₀) w := by
  have h2 := (shallowSecondDeriv_pos_iff hk ha hh w₀).2 hw
  have hc : 0 < k / a ^ 2 := by positivity
  have hg : 0 < (w₀ + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 := by
    have : 0 < 3 * w₀ ^ 2 - h ^ 2 := pos_of_mul_pos_right h2 hc.le
    nlinarith
  have hcont : Continuous fun w : ℝ => (w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 := by fun_prop
  have hev : ∀ᶠ w in 𝓝 w₀, 0 < (w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 :=
    hcont.continuousAt.eventually (lt_mem_nhds hg)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with w hpos hne
  have hne' : w - w₀ ≠ 0 := sub_ne_zero.2 hne
  have := shallowPotential_sub k a h w₀ w
  have : 0 < k / (4 * a ^ 2) * (w - w₀) ^ 2 * ((w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2) := by
    positivity
  linarith

/-- **Unstable equilibria are strict local maxima**: if `P = P(w₀)` with `|w₀| < h/√3`, then
`Π_s(w) < Π_s(w₀)` for all `w ≠ w₀` near `w₀`. -/
theorem isStrictLocalMax_shallowPotential {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) {h : ℝ}
    (hh : 0 ≤ h) {w₀ : ℝ} (hw : |w₀| < limitPoint h) :
    ∀ᶠ w in 𝓝[≠] w₀, shallowPotential k a h (shallowLoad k a h w₀) w <
      shallowPotential k a h (shallowLoad k a h w₀) w₀ := by
  have h2 := (shallowSecondDeriv_neg_iff hk ha hh w₀).2 hw
  have hc : 0 < k / a ^ 2 := by positivity
  have hg : (w₀ + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 < 0 := by
    have : 3 * w₀ ^ 2 - h ^ 2 < 0 := by
      by_contra H
      push Not at H
      have := mul_nonneg hc.le H
      linarith
    nlinarith
  have hcont : Continuous fun w : ℝ => (w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 := by fun_prop
  have hev : ∀ᶠ w in 𝓝 w₀, (w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2 < 0 :=
    hcont.continuousAt.eventually (gt_mem_nhds hg)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with w hneg hne
  have hne' : w - w₀ ≠ 0 := sub_ne_zero.2 hne
  have := shallowPotential_sub k a h w₀ w
  have hq : 0 < k / (4 * a ^ 2) * (w - w₀) ^ 2 := by positivity
  have : k / (4 * a ^ 2) * (w - w₀) ^ 2 * ((w + w₀) ^ 2 + 2 * w₀ ^ 2 - 2 * h ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hq hneg
  linarith

/-! ### Number of equilibria -/

/-- The equilibrium path is continuous. -/
theorem continuous_shallowLoad (k a h : ℝ) : Continuous (shallowLoad k a h) := by
  unfold shallowLoad
  fun_prop

/-- The flat configuration carries no load: `P(0) = 0`. -/
@[simp] theorem shallowLoad_zero (k a h : ℝ) : shallowLoad k a h 0 = 0 := by
  simp [shallowLoad]

/-- The unloaded configuration carries no load: `P(h) = 0`. -/
@[simp] theorem shallowLoad_rise (k a h : ℝ) : shallowLoad k a h h = 0 := by
  simp [shallowLoad]

/-- The mirror configuration carries no load: `P(-h) = 0`. -/
@[simp] theorem shallowLoad_neg_rise (k a h : ℝ) : shallowLoad k a h (-h) = 0 := by
  simp [shallowLoad]

/-- The inverted snap-through configuration carries the limit load: `P(-2h/√3) = P_cr`. -/
theorem shallowLoad_neg_two_limitPoint (k a h : ℝ) :
    shallowLoad k a h (-(2 * limitPoint h)) = critLoad k a h := by
  rw [← sub_eq_zero, shallowLoad_sub_critLoad]
  ring

/-- **Three equilibria below the limit load**: for `0 ≤ P < P_cr` there are equilibria
`w₁ < w₂ < w₃` with `w₁ ≤ -h` (inverted), `0 ≤ w₂ < h/√3` (unstable) and `h/√3 < w₃ ≤ h`
(stable, on the loaded upper branch). -/
theorem exists_three_equilibria (k a : ℝ) {h : ℝ} (hh : 0 < h)
    {P : ℝ} (hP₀ : 0 ≤ P) (hP : P < critLoad k a h) :
    ∃ w₁ w₂ w₃, w₁ < w₂ ∧ w₂ < w₃ ∧ shallowLoad k a h w₁ = P ∧ shallowLoad k a h w₂ = P ∧
      shallowLoad k a h w₃ = P ∧ -(2 * limitPoint h) ≤ w₁ ∧ w₁ ≤ -h ∧ 0 ≤ w₂ ∧
      w₂ < limitPoint h ∧ limitPoint h < w₃ ∧ w₃ ≤ h := by
  have hs := limitPoint_pos hh
  have hsh := limitPoint_lt hh
  have h2s := neg_two_limitPoint_lt hh
  have hcont := (continuous_shallowLoad k a h).continuousOn (s := univ)
  obtain ⟨w₁, ⟨hw₁, hw₁'⟩, e₁⟩ := intermediate_value_Icc' h2s.le (hcont.mono (subset_univ _))
    (show P ∈ Icc (shallowLoad k a h (-h)) (shallowLoad k a h (-(2 * limitPoint h))) by
      rw [shallowLoad_neg_rise, shallowLoad_neg_two_limitPoint]; exact ⟨hP₀, hP.le⟩)
  obtain ⟨w₂, ⟨hw₂, hw₂'⟩, e₂⟩ := intermediate_value_Icc hs.le (hcont.mono (subset_univ _))
    (show P ∈ Icc (shallowLoad k a h 0) (shallowLoad k a h (limitPoint h)) by
      rw [shallowLoad_zero, ← critLoad_eq_shallowLoad]; exact ⟨hP₀, hP.le⟩)
  obtain ⟨w₃, ⟨hw₃, hw₃'⟩, e₃⟩ := intermediate_value_Icc' hsh.le (hcont.mono (subset_univ _))
    (show P ∈ Icc (shallowLoad k a h h) (shallowLoad k a h (limitPoint h)) by
      rw [shallowLoad_rise, ← critLoad_eq_shallowLoad]; exact ⟨hP₀, hP.le⟩)
  have hw₂s : w₂ ≠ limitPoint h := by
    rintro rfl
    rw [← critLoad_eq_shallowLoad] at e₂
    exact hP.ne' e₂
  have hw₃s : w₃ ≠ limitPoint h := by
    rintro rfl
    rw [← critLoad_eq_shallowLoad] at e₃
    exact hP.ne' e₃
  have hw₂lt : w₂ < limitPoint h := lt_of_le_of_ne hw₂' hw₂s
  have hw₃gt : limitPoint h < w₃ := lt_of_le_of_ne hw₃ (Ne.symm hw₃s)
  exact ⟨w₁, w₂, w₃, by linarith, by linarith, e₁, e₂, e₃, hw₁, hw₁', hw₂, hw₂lt, hw₃gt, hw₃'⟩

/-- **Existence of an inverted equilibrium**: for every load `P ≥ 0` there is an equilibrium
`w ≤ -h` below the mirror configuration. -/
theorem exists_inverted_equilibrium {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0) {h : ℝ}
    (hh : 0 < h) {P : ℝ} (hP : 0 ≤ P) : ∃ w ≤ -h, shallowLoad k a h w = P := by
  set c := k / a ^ 2 with hc_def
  have hc : 0 < c := by positivity
  set t := P / (c * h ^ 2) with ht_def
  have ht : 0 ≤ t := by positivity
  have hct : c * h ^ 2 * t = P := by rw [ht_def]; field_simp
  have hend : P ≤ shallowLoad k a h (-(h + t)) := by
    have e : shallowLoad k a h (-(h + t)) - P = c * t * (h ^ 2 + 3 * h * t + t ^ 2) := by
      rw [← hct, shallowLoad, ← hc_def]
      ring
    have : 0 ≤ c * t * (h ^ 2 + 3 * h * t + t ^ 2) := by positivity
    linarith
  have hle : -(h + t) ≤ -h := by linarith
  obtain ⟨w, ⟨_, hw⟩, e⟩ := intermediate_value_Icc' hle
    (continuous_shallowLoad k a h).continuousOn
    (show P ∈ Icc (shallowLoad k a h (-h)) (shallowLoad k a h (-(h + t))) by
      rw [shallowLoad_neg_rise]; exact ⟨hP, hend⟩)
  exact ⟨w, hw, e⟩

/-- Above the limit load every equilibrium is inverted beyond the snap-through configuration:
if `P(w) > P_cr` (with `k ≥ 0`) then `w < -2h/√3`. -/
theorem lt_neg_two_limitPoint_of_critLoad_lt {k : ℝ} (hk : 0 ≤ k) {a h w : ℝ}
    (hP : critLoad k a h < shallowLoad k a h w) : w < -(2 * limitPoint h) := by
  by_contra H
  push Not at H
  exact (shallowLoad_le_critLoad hk a h H).not_gt hP

/-- **A unique equilibrium above the limit load**: for `P > P_cr` (with `k > 0`, `a ≠ 0`,
`h > 0`) there is exactly one equilibrium, and it is inverted: `w < -2h/√3`. -/
theorem existsUnique_equilibrium_of_critLoad_lt {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : a ≠ 0)
    {h : ℝ} (hh : 0 < h) {P : ℝ} (hP : critLoad k a h < P) :
    ∃! w, shallowLoad k a h w = P ∧ w < -(2 * limitPoint h) := by
  have hcr : 0 < critLoad k a h := by
    rw [critLoad_eq]
    have := limitPoint_pos hh
    positivity
  obtain ⟨w, -, e⟩ := exists_inverted_equilibrium hk ha hh (hcr.le.trans hP.le)
  have hw : w < -(2 * limitPoint h) := lt_neg_two_limitPoint_of_critLoad_lt hk.le (e ▸ hP)
  refine ⟨w, ⟨e, hw⟩, ?_⟩
  rintro v ⟨ev, hv⟩
  have hc : 0 < k / a ^ 2 := by positivity
  have hs := limitPoint_pos hh
  have hsq := limitPoint_sq h
  -- the path is strictly decreasing on `(-∞, -2h/√3)`
  have key : ∀ x y, x < y → y < -(2 * limitPoint h) →
      shallowLoad k a h y < shallowLoad k a h x := by
    intro x y hxy hy
    have hx : x < -(2 * limitPoint h) := hxy.trans hy
    have e1 : shallowLoad k a h x - shallowLoad k a h y =
        k / a ^ 2 * ((y - x) * (x ^ 2 + x * y + y ^ 2 - h ^ 2)) := by
      unfold shallowLoad
      ring
    have hq : h ^ 2 < x ^ 2 + x * y + y ^ 2 := by nlinarith
    have : 0 < k / a ^ 2 * ((y - x) * (x ^ 2 + x * y + y ^ 2 - h ^ 2)) := by
      apply mul_pos hc
      apply mul_pos <;> linarith
    linarith
  rcases lt_trichotomy v w with hvw | hvw | hvw
  · exact absurd (ev.trans e.symm) (key v w hvw hw).ne'
  · exact hvw
  · exact absurd (ev.trans e.symm) (key w v hvw hv).ne

end VonMisesTruss

end DiscreteMechanics
