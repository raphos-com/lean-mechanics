import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Miura-ori: rigid folding and the in-plane Poisson's ratio

The Miura-ori unit cell is made of four identical parallelogram facets with sides `a`, `b` and
angle `α ∈ (0, π/2)`. It folds rigidly with one degree of freedom, the angle `θ ∈ (0, π/2)` between
the facets and the horizontal plane. Following [SchenkGuest2013], with
`r(θ) = √(1 - sin²θ sin²α)` the cell dimensions are

* `H = a sin θ sin α` (height), `L = a r` (half length along the zig-zag),
* `S = b cos θ sin α / r` (half width), `V = b cos α / r` (offset of the slanted edge).

The facet spanned by `(0, L, H)` and `(S, V, 0)` keeps its side lengths `a`, `b` and its angle `α`
for every `θ` (`facet_isometry`): the parametrization is a rigid folding motion.

**Poisson's ratio.** `S` and `L` both decrease as the sheet folds (`θ` increases), so the in-plane
Poisson's ratio `ν_SL = -(dL/L)/(dS/S)` is negative: `ν_SL = -cos²θ tan²α` (`poisson_SL`,
[SchenkGuest2013]; also [Wei2013]).

**Finite patterns.** For a pattern of `n` cells along the zig-zag, the length is `2nL + V` (the
slanted edges add `V` once). Its Poisson's ratio `ν_n` (with `2nL + V` in place of `L`) is
**positive exactly when** `b cos α > 2 n a (1 - sin²θ sin²α)` (`poisson_pattern_pos_iff`), and
tends to `ν_SL` as `n → ∞` (`tendsto_poisson_pattern`). This makes precise the observation of
[Lv2014] that the in-plane Poisson's ratio of a finite Miura pattern can be positive.

## References

* [SchenkGuest2013] M. Schenk, S. D. Guest, *Geometry of Miura-folded metamaterials*,
  PNAS 110(9) (2013).
* [Wei2013] Z. Y. Wei, Z. V. Guo, L. Dudte, H. Y. Liang, L. Mahadevan, *Geometric mechanics of
  periodic pleated origami*, Phys. Rev. Lett. 110 (2013).
* [Lv2014] C. Lv, D. Krishnaraju, G. Konjevod, H. Yu, H. Jiang, *Origami based mechanical
  metamaterials*, Sci. Rep. 4 (2014).
-/

open Real Filter Topology

noncomputable section

namespace ContinuumMechanics.Miura

/-- Miura-ori facet: sides `a`, `b`, angle `α ∈ (0, π/2)`. -/
structure Facet where
  a : ℝ
  b : ℝ
  α : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  α_pos : 0 < α
  α_lt : α < π / 2

namespace Facet

variable (F : Facet)

/-- `r(θ)² = 1 - sin²θ sin²α`. -/
def r2 (θ : ℝ) : ℝ := 1 - sin θ ^ 2 * sin F.α ^ 2

def r (θ : ℝ) : ℝ := √(F.r2 θ)

def H (θ : ℝ) : ℝ := F.a * sin θ * sin F.α
def L (θ : ℝ) : ℝ := F.a * F.r θ
def S (θ : ℝ) : ℝ := F.b * cos θ * sin F.α / F.r θ
def V (θ : ℝ) : ℝ := F.b * cos F.α / F.r θ

theorem sin_α_pos : 0 < sin F.α := sin_pos_of_pos_of_lt_pi F.α_pos (by linarith [F.α_lt, pi_pos])
theorem cos_α_pos : 0 < cos F.α := cos_pos_of_mem_Ioo ⟨by linarith [F.α_pos, pi_pos], F.α_lt⟩

/-- `r² = cos²α + cos²θ sin²α ≥ cos²α > 0`. -/
theorem r2_eq (θ : ℝ) : F.r2 θ = cos F.α ^ 2 + cos θ ^ 2 * sin F.α ^ 2 := by
  have h1 := sin_sq_add_cos_sq θ; have h2 := sin_sq_add_cos_sq F.α
  simp only [r2]; nlinarith

theorem r2_pos (θ : ℝ) : 0 < F.r2 θ := by
  rw [r2_eq]; have := F.cos_α_pos; positivity

theorem r_pos (θ : ℝ) : 0 < F.r θ := sqrt_pos.2 (F.r2_pos θ)

theorem r_sq (θ : ℝ) : F.r θ ^ 2 = F.r2 θ := sq_sqrt (F.r2_pos θ).le

/-- **Rigid folding**: the facet spanned by `(0, L, H)` and `(S, V, 0)` has sides `a`, `b` and
angle `α` for every fold angle `θ`. -/
theorem facet_isometry (θ : ℝ) :
    F.L θ ^ 2 + F.H θ ^ 2 = F.a ^ 2 ∧ F.S θ ^ 2 + F.V θ ^ 2 = F.b ^ 2 ∧
      F.L θ * F.V θ = F.a * F.b * cos F.α := by
  have hr := F.r_pos θ; have hr2 := F.r_sq θ
  have h1 := sin_sq_add_cos_sq θ; have h2 := sin_sq_add_cos_sq F.α
  refine ⟨?_, ?_, ?_⟩
  · simp only [L, H]; rw [mul_pow, hr2, r2]; ring
  · simp only [S, V]
    rw [div_pow, div_pow, ← add_div, hr2, div_eq_iff (F.r2_pos θ).ne', r2_eq]
    ring
  · simp only [L, V]; field_simp

/-! ### Derivatives -/

theorem hasDerivAt_r2 (θ : ℝ) :
    HasDerivAt F.r2 (-(2 * sin θ * cos θ * sin F.α ^ 2)) θ := by
  change HasDerivAt (fun x => 1 - sin x ^ 2 * sin F.α ^ 2) _ θ
  have := (((hasDerivAt_sin θ).pow 2).mul_const (sin F.α ^ 2)).const_sub 1
  convert this using 1
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]

theorem hasDerivAt_r (θ : ℝ) :
    HasDerivAt F.r (-(sin θ * cos θ * sin F.α ^ 2) / F.r θ) θ := by
  change HasDerivAt (fun x => √(F.r2 x)) _ θ
  have := (F.hasDerivAt_r2 θ).sqrt (F.r2_pos θ).ne'
  convert this using 1
  rw [show F.r θ = √(F.r2 θ) from rfl]
  have := sqrt_pos.2 (F.r2_pos θ)
  field_simp

theorem hasDerivAt_L (θ : ℝ) :
    HasDerivAt F.L (F.a * (-(sin θ * cos θ * sin F.α ^ 2) / F.r θ)) θ :=
  (F.hasDerivAt_r θ).const_mul F.a

theorem hasDerivAt_S (θ : ℝ) :
    HasDerivAt F.S (-(F.b * sin θ * sin F.α * cos F.α ^ 2) / F.r θ ^ 3) θ := by
  have hr := (F.r_pos θ).ne'
  change HasDerivAt (fun y => F.b * cos y * sin F.α / F.r y) _ θ
  have := (((hasDerivAt_cos θ).const_mul F.b).mul_const (sin F.α)).div (F.hasDerivAt_r θ) hr
  convert this using 1
  have h1 := sin_sq_add_cos_sq θ; have h2 := sin_sq_add_cos_sq F.α
  have hr2 := F.r_sq θ
  field_simp
  rw [hr2, r2_eq]
  ring

theorem hasDerivAt_V (θ : ℝ) :
    HasDerivAt F.V (F.b * cos F.α * (sin θ * cos θ * sin F.α ^ 2) / F.r θ ^ 3) θ := by
  have hr := (F.r_pos θ).ne'
  change HasDerivAt (fun y => F.b * cos F.α / F.r y) _ θ
  have := (hasDerivAt_const θ (F.b * cos F.α)).div (F.hasDerivAt_r θ) hr
  convert this using 1
  field_simp
  ring

/-! ### Poisson's ratios -/

/-- The in-plane Poisson's ratio `ν_SL = -(dL/L)/(dS/S)` of the unit cell. -/
def poissonSL (θ : ℝ) : ℝ := -((deriv F.L θ / F.L θ) / (deriv F.S θ / F.S θ))

theorem sin_cos_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : 0 < sin θ ∧ 0 < cos θ :=
  ⟨sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩⟩

/-- **Schenk–Guest**: `ν_SL = -cos²θ tan²α`; in particular it is negative. -/
theorem poisson_SL {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    F.poissonSL θ = -(cos θ ^ 2 * tan F.α ^ 2) := by
  obtain ⟨hs, hc⟩ := sin_cos_pos h0 h1
  have hr := F.r_pos θ
  have ha := F.a_pos; have hb := F.b_pos; have hsa := F.sin_α_pos; have hca := F.cos_α_pos
  rw [poissonSL, (F.hasDerivAt_L θ).deriv, (F.hasDerivAt_S θ).deriv, tan_eq_sin_div_cos]
  simp only [L, S]
  field_simp

theorem poisson_SL_neg {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : F.poissonSL θ < 0 := by
  rw [F.poisson_SL h0 h1]
  obtain ⟨_, hc⟩ := sin_cos_pos h0 h1
  have : 0 < tan F.α := tan_pos_of_pos_of_lt_pi_div_two F.α_pos F.α_lt
  have : 0 < cos θ ^ 2 * tan F.α ^ 2 := by positivity
  linarith

/-- Length `2nL + V` of a pattern of `n` cells along the zig-zag. -/
def patternL (n : ℕ) (θ : ℝ) : ℝ := 2 * n * F.L θ + F.V θ

/-- The Poisson's ratio of the finite pattern. -/
def poissonPattern (n : ℕ) (θ : ℝ) : ℝ :=
  -((deriv (F.patternL n) θ / F.patternL n θ) / (deriv F.S θ / F.S θ))

theorem hasDerivAt_patternL (n : ℕ) (θ : ℝ) :
    HasDerivAt (F.patternL n)
      (sin θ * cos θ * sin F.α ^ 2 / F.r θ * (F.b * cos F.α / F.r θ ^ 2 - 2 * n * F.a)) θ := by
  have := ((F.hasDerivAt_L θ).const_mul (2 * (n : ℝ))).add (F.hasDerivAt_V θ)
  have hr := (F.r_pos θ).ne'
  refine this.congr_deriv ?_
  field_simp
  ring

/-- Closed form of the pattern Poisson's ratio. -/
theorem poissonPattern_eq (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    F.poissonPattern n θ =
      cos θ ^ 2 * sin F.α ^ 2 * (F.b * cos F.α - 2 * n * F.a * F.r θ ^ 2) /
        (cos F.α ^ 2 * (2 * n * F.a * F.r θ ^ 2 + F.b * cos F.α)) := by
  obtain ⟨hs, hc⟩ := sin_cos_pos h0 h1
  have hr := F.r_pos θ
  have ha := F.a_pos; have hb := F.b_pos; have hsa := F.sin_α_pos; have hca := F.cos_α_pos
  have hP : 0 < 2 * n * F.a * F.r θ ^ 2 + F.b * cos F.α := by positivity
  rw [poissonPattern, (F.hasDerivAt_patternL n θ).deriv, (F.hasDerivAt_S θ).deriv]
  simp only [patternL, L, V, S]
  field_simp

/-- **Lv et al.**: the Poisson's ratio of a pattern of `n` cells is positive exactly when
`b cos α > 2 n a (1 - sin²θ sin²α)`. -/
theorem poisson_pattern_pos_iff (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    0 < F.poissonPattern n θ ↔ 2 * n * F.a * F.r2 θ < F.b * cos F.α := by
  obtain ⟨hs, hc⟩ := sin_cos_pos h0 h1
  have hr := F.r_pos θ
  have ha := F.a_pos; have hb := F.b_pos; have hsa := F.sin_α_pos; have hca := F.cos_α_pos
  have hP : 0 < 2 * n * F.a * F.r θ ^ 2 + F.b * cos F.α := by positivity
  have hK : 0 < cos θ ^ 2 * sin F.α ^ 2 := by positivity
  rw [F.poissonPattern_eq n h0 h1, ← F.r_sq θ, div_pos_iff_of_pos_right (by positivity),
    mul_pos_iff_of_pos_left hK, sub_pos]

/-- As the pattern grows, its Poisson's ratio tends to the unit-cell value `-cos²θ tan²α`. -/
theorem tendsto_poisson_pattern {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    Tendsto (fun n : ℕ => F.poissonPattern n θ) atTop (𝓝 (F.poissonSL θ)) := by
  obtain ⟨hs, hc⟩ := sin_cos_pos h0 h1
  have hr := F.r_pos θ
  have ha := F.a_pos; have hb := F.b_pos; have hsa := F.sin_α_pos; have hca := F.cos_α_pos
  have hr2 : 0 < F.r θ ^ 2 := by positivity
  -- divide numerator and denominator by `n`
  set c := cos θ ^ 2 * sin F.α ^ 2
  set p := F.b * cos F.α
  set q := 2 * F.a * F.r θ ^ 2
  have hq : 0 < q := by positivity
  have key : ∀ n : ℕ, 0 < n → F.poissonPattern n θ =
      c * (p / n - q) / (cos F.α ^ 2 * (q + p / n)) := fun n hn => by
    rw [F.poissonPattern_eq n h0 h1]
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [c, p, q]
    field_simp
  have hinv : Tendsto (fun n : ℕ => p / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := ((hinv.sub_const q).const_mul c).div
    (((tendsto_const_nhds (x := q)).add hinv).const_mul (cos F.α ^ 2)) (by positivity)
  rw [F.poisson_SL h0 h1]
  refine (hlim.congr' ?_).trans (le_of_eq ?_)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Pi.div_apply]
    exact (key n hn).symm
  · rw [tan_eq_sin_div_cos]
    simp only [c, q, zero_sub, add_zero]
    field_simp

end Facet

end ContinuumMechanics.Miura
