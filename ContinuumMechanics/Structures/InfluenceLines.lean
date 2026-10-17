import ContinuumMechanics.Constitutive.Plasticity
import ContinuumMechanics.Structures.Cables

/-!
# Influence lines and moving loads on a simply supported beam

A simply supported beam of span `L > 0` (pin at `A`, `x = 0`; roller at `B`, `x = L`) carries a
**unit load** at position `a ∈ [0, L]`. Statics gives the reactions `R_A(a) = 1 - a / L`,
`R_B(a) = a / L`, and the bending moment at a section `x` is

`M(x; a) = x (L - a) / L` for `x ≤ a`,  `M(x; a) = a (L - x) / L` for `a ≤ x`,

compactly `M(x; a) = min(x, a) (L - max(x, a)) / L`. Read as a function of the load position
`a` for a fixed section `x`, this is the **influence line** for the moment at `x`: a triangle
with peak `x (L - x) / L` under the section. It is symmetric, `M(x; a) = M(a; x)`, an instance of
**Maxwell's reciprocal theorem** (`Castigliano.maxwell_betti`) for the moment influence function
([TimoshenkoYoung1965], Ch. 4; [Hibbeler2012], Ch. 6).

By **superposition** the moment due to a distributed load `q(a)` is `∫₀ᴸ q(a) M(x; a) da`, which
for a uniform load is `q x (L - x) / 2`; for point loads `Pᵢ` at `aᵢ` it is `Σ Pᵢ M(x; aᵢ)`.

## Main results

**(a) Statics and the influence line**
* `ilReacA_add_ilReacB`, `ilReacB_moment`: vertical and moment equilibrium of the reactions.
* `ilMoment_eq_statics`: `M(x; a) = R_A(a) x - max(x - a, 0)` (free body left of `x`).
* `ilMoment_of_le`, `ilMoment_of_ge`: the two branches of the triangular influence line;
  `ilMoment_self`: the peak value `x (L - x) / L`.
* `ilMoment_symm`: **Maxwell reciprocity** `M(x; a) = M(a; x)`.
* `ilMoment_nonneg`, `ilMoment_le_peak`: `0 ≤ M(x; a) ≤ M(x; x)`.
* `hasDerivAt_ilMoment_left`, `hasDerivAt_ilMoment_right`: `∂M/∂x` is the shear `ilShear`.
* `ssMoment_eq_ilMoment`: the central point load moment `ssMoment` is `P M(x; L/2)`.

**(b) Superposition**
* `integral_ilMoment_uniform`: `∫₀ᴸ q M(x; a) da = q x (L - x) / 2 = beamMomentUniform q L x`,
  also `= ffMoment q 0 0 L x` (`integral_ilMoment_eq_ffMoment`).
* `pointLoadsMoment_eq_statics`: `Σ Pᵢ M(x; aᵢ) = (Σ Pᵢ R_A(aᵢ)) x - Σ Pᵢ max(x - aᵢ, 0)`.

**(c) A single moving load**
* `ilMoment_le_quarter`: `M(x; a) ≤ L / 4` for `x` on the beam;
  `ilMoment_eq_quarter_iff`: equality iff `x = a = L / 2`.
* `isGreatest_singleLoad`: the absolute maximum moment of a moving load `P ≥ 0` is `P L / 4`.

**(d) Two equal moving loads at spacing `s`**
* `twoLoadMoment_eq`: the moment under the leading load is `P a (2L - 2a - s) / L`.
* `hasDerivAt_twoLoadMoment`, `twoLoadMoment_le`: it is maximal at `a = L / 2 - s / 4`
  (midspan bisects the load and the resultant), with value `P (2L - s)² / (8L)`.
* `isGreatest_twoLoad`: for `s ≤ 2L / 3` this is the maximum over admissible positions.
* `twoLoad_ge_single_iff`: `(2L - s)² / (8L) ≥ L / 4 ↔ s ≤ (2 - √2) L`.

**(e) Müller-Breslau principle** (statically determinate form)
* `mullerBreslau_reacA`: the influence line of `R_A` is the rigid rotation about `B` with unit
  displacement at `A`.
* `mullerBreslau_moment`: the influence line of `M(x)` is the mechanism with a hinge at `x`
  and unit relative rotation (slope jump `1`).

## References

* [TimoshenkoYoung1965] S. P. Timoshenko, D. H. Young, *Theory of Structures*, 2nd ed., Ch. 4.
* [Hibbeler2012] R. C. Hibbeler, *Structural Analysis*, 8th ed., Ch. 6.
* [MullerBreslau1887] H. Müller-Breslau, *Die neueren Methoden der Festigkeitslehre* (1887).
-/

open Real Set intervalIntegral

namespace ContinuumMechanics.Structures

/-! ### (a) Statics of a unit load -/

/-- Reaction at the left support `A` due to a unit load at `a`: `R_A = 1 - a / L`. -/
noncomputable def ilReacA (L a : ℝ) : ℝ := 1 - a / L

/-- Reaction at the right support `B` due to a unit load at `a`: `R_B = a / L`. -/
noncomputable def ilReacB (L a : ℝ) : ℝ := a / L

/-- Vertical equilibrium: `R_A + R_B = 1`. -/
theorem ilReacA_add_ilReacB (L a : ℝ) : ilReacA L a + ilReacB L a = 1 := by
  unfold ilReacA ilReacB; ring

/-- Moment equilibrium about `A`: `R_B L = 1 · a`. -/
theorem ilReacB_moment {L : ℝ} (hL : L ≠ 0) (a : ℝ) : ilReacB L a * L = a := by
  unfold ilReacB; field_simp

/-- The **influence function** for the bending moment: the moment at section `x` due to a unit
load at `a`, `M(x; a) = min(x, a) (L - max(x, a)) / L`. -/
noncomputable def ilMoment (L x a : ℝ) : ℝ := min x a * (L - max x a) / L

/-- The shear force at section `x` due to a unit load at `a`: `R_A` left of the load, `-R_B`
right of it. -/
noncomputable def ilShear (L x a : ℝ) : ℝ := if x < a then ilReacA L a else -ilReacB L a

/-- Branch of the influence line with the section left of the load: `M = x (L - a) / L`. -/
theorem ilMoment_of_le {L x a : ℝ} (h : x ≤ a) : ilMoment L x a = x * (L - a) / L := by
  rw [ilMoment, min_eq_left h, max_eq_right h]

/-- Branch of the influence line with the section right of the load: `M = a (L - x) / L`. -/
theorem ilMoment_of_ge {L x a : ℝ} (h : a ≤ x) : ilMoment L x a = a * (L - x) / L := by
  rw [ilMoment, min_eq_right h, max_eq_left h]

/-- **Maxwell reciprocity** of the moment influence function: `M(x; a) = M(a; x)`. -/
theorem ilMoment_symm (L x a : ℝ) : ilMoment L x a = ilMoment L a x := by
  rw [ilMoment, ilMoment, min_comm, max_comm]

/-- Peak of the influence line, attained with the load at the section: `x (L - x) / L`. -/
theorem ilMoment_self (L x : ℝ) : ilMoment L x x = x * (L - x) / L := ilMoment_of_le le_rfl

/-- Statics: the moment at `x` from the free body left of the section,
`M(x; a) = R_A(a) x - 1 · max(x - a, 0)`. -/
theorem ilMoment_eq_statics {L : ℝ} (hL : L ≠ 0) (x a : ℝ) :
    ilMoment L x a = ilReacA L a * x - max (x - a) 0 := by
  unfold ilReacA
  rcases le_total x a with h | h
  · rw [ilMoment_of_le h, max_eq_right (by linarith)]; field_simp; ring
  · rw [ilMoment_of_ge h, max_eq_left (by linarith)]; field_simp; ring

/-- The influence function is continuous in the load position. -/
theorem continuous_ilMoment (L x : ℝ) : Continuous (ilMoment L x) := by
  unfold ilMoment; fun_prop

/-- The influence line is nonnegative on the beam. -/
theorem ilMoment_nonneg {L x a : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) (ha : a ∈ Icc 0 L) :
    0 ≤ ilMoment L x a := by
  unfold ilMoment
  have h1 : 0 ≤ min x a := le_min hx.1 ha.1
  have h2 : 0 ≤ L - max x a := by linarith [max_le hx.2 ha.2]
  positivity

/-- The influence line for `M(x)` is maximal with the load at the section. -/
theorem ilMoment_le_peak {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) (a : ℝ) :
    ilMoment L x a ≤ ilMoment L x x := by
  rw [ilMoment_self]
  rcases le_total x a with h | h
  · rw [ilMoment_of_le h]; gcongr; linarith [hx.1]
  · rw [ilMoment_of_ge h]; gcongr; linarith [hx.2]

/-- Left of the load the moment has slope `∂M/∂x = R_A`, the shear. -/
theorem hasDerivAt_ilMoment_left {L : ℝ} (hL : L ≠ 0) (a : ℝ) {x : ℝ} (hx : x < a) :
    HasDerivAt (fun y => ilMoment L y a) (ilShear L x a) x := by
  have heq : (fun y => ilMoment L y a) =ᶠ[nhds x] fun y => y * (L - a) / L := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact ilMoment_of_le hy.le
  simp only [ilShear, hx, ↓reduceIte, ilReacA]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  exact (((hasDerivAt_id x).mul_const (L - a)).div_const L).congr_deriv (by field_simp)

/-- Right of the load the moment has slope `∂M/∂x = -R_B`, the shear. -/
theorem hasDerivAt_ilMoment_right (L a : ℝ) {x : ℝ} (hx : a < x) :
    HasDerivAt (fun y => ilMoment L y a) (ilShear L x a) x := by
  have heq : (fun y => ilMoment L y a) =ᶠ[nhds x] fun y => a * (L - y) / L := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact ilMoment_of_ge hy.le
  simp only [ilShear, not_lt.mpr hx.le, ↓reduceIte, ilReacB]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  exact ((((hasDerivAt_id x).const_sub L).const_mul a).div_const L).congr_deriv (by ring)

/-- The moment of a central point load `P` (`Plasticity.ssMoment`) is `P M(x; L / 2)`. -/
theorem ssMoment_eq_ilMoment {L : ℝ} (hL : L ≠ 0) (P x : ℝ) :
    Plasticity.ssMoment P L x = P * ilMoment L x (L / 2) := by
  unfold Plasticity.ssMoment
  split_ifs with h
  · rw [ilMoment_of_le h]; field_simp; ring
  · rw [ilMoment_of_ge (not_le.mp h).le]; field_simp

/-! ### (b) Superposition -/

/-- **Superposition** for a uniform load `q`: `∫₀ᴸ q M(x; a) da = q x (L - x) / 2`. -/
theorem integral_ilMoment_uniform {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) (q : ℝ) :
    ∫ a in (0 : ℝ)..L, q * ilMoment L x a = beamMomentUniform q L x := by
  have hint : ∀ u v : ℝ,
      IntervalIntegrable (fun a => q * ilMoment L x a) MeasureTheory.volume u v :=
    fun u v => ((continuous_ilMoment L x).const_mul q).intervalIntegrable u v
  rw [← integral_add_adjacent_intervals (hint 0 x) (hint x L)]
  have h1 : ∫ a in (0 : ℝ)..x, q * ilMoment L x a = ∫ a in (0 : ℝ)..x, q * (L - x) / L * a := by
    refine integral_congr fun a ha => ?_
    rw [uIcc_of_le hx.1] at ha
    rw [ilMoment_of_ge ha.2]; ring
  have h2 : ∫ a in x..L, q * ilMoment L x a = ∫ a in x..L, q * x / L * (L - a) := by
    refine integral_congr fun a ha => ?_
    rw [uIcc_of_le hx.2] at ha
    rw [ilMoment_of_le ha.1]; ring
  rw [h1, h2, integral_const_mul, integral_const_mul, integral_id, integral_sub, integral_const,
    integral_id]
  · unfold beamMomentUniform; simp only [smul_eq_mul]; field_simp; ring
  · exact intervalIntegrable_const
  · exact intervalIntegral.intervalIntegrable_id

/-- The uniform-load superposition agrees with `Plasticity.ffMoment` with zero end moments. -/
theorem integral_ilMoment_eq_ffMoment {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) (q : ℝ) :
    ∫ a in (0 : ℝ)..L, q * ilMoment L x a = Plasticity.ffMoment q 0 0 L x := by
  rw [integral_ilMoment_uniform hL hx, beamMomentUniform, Plasticity.ffMoment]; ring

/-- The moment at `x` due to point loads `P i` at positions `a i`, by superposition. -/
noncomputable def pointLoadsMoment {ι : Type*} (s : Finset ι) (P a : ι → ℝ) (L x : ℝ) : ℝ :=
  ∑ i ∈ s, P i * ilMoment L x (a i)

/-- Superposition of point loads agrees with statics of the whole load system:
`Σ Pᵢ M(x; aᵢ) = R_A x - Σ Pᵢ max(x - aᵢ, 0)` with `R_A = Σ Pᵢ (1 - aᵢ / L)`. -/
theorem pointLoadsMoment_eq_statics {ι : Type*} (s : Finset ι) (P a : ι → ℝ) {L : ℝ}
    (hL : L ≠ 0) (x : ℝ) :
    pointLoadsMoment s P a L x =
      (∑ i ∈ s, P i * ilReacA L (a i)) * x - ∑ i ∈ s, P i * max (x - a i) 0 := by
  unfold pointLoadsMoment
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ilMoment_eq_statics hL]; ring

/-! ### (c) Maximum moment under a single moving load -/

/-- The moment under a single unit load never exceeds `L / 4`. -/
theorem ilMoment_le_quarter {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) (a : ℝ) :
    ilMoment L x a ≤ L / 4 := by
  refine (ilMoment_le_peak hL hx a).trans ?_
  rw [ilMoment_self, div_le_div_iff₀ hL (by norm_num)]
  nlinarith [sq_nonneg (x - L / 2)]

/-- The bound `M(x; a) ≤ L / 4` is attained exactly at midspan with the load at midspan. -/
theorem ilMoment_eq_quarter_iff {L x a : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L)
    (ha : a ∈ Icc 0 L) : ilMoment L x a = L / 4 ↔ x = L / 2 ∧ a = L / 2 := by
  constructor
  · intro h
    rcases le_total x a with hxa | hxa
    · rw [ilMoment_of_le hxa, div_eq_iff hL.ne'] at h
      have h1 : x * (L - a) ≤ a * (L - a) := by nlinarith [ha.2]
      have h2 : (a - L / 2) ^ 2 = 0 := by nlinarith
      have ha' : a = L / 2 := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h2]
      subst ha'
      exact ⟨by nlinarith, rfl⟩
    · rw [ilMoment_of_ge hxa, div_eq_iff hL.ne'] at h
      have h1 : a * (L - x) ≤ x * (L - x) := by nlinarith [hx.2]
      have h2 : (x - L / 2) ^ 2 = 0 := by nlinarith
      have hx' : x = L / 2 := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h2]
      subst hx'
      exact ⟨rfl, by nlinarith⟩
  · rintro ⟨rfl, rfl⟩
    rw [ilMoment_self]; field_simp; ring

/-- **Absolute maximum moment of a single moving load** `P ≥ 0`: over all sections and load
positions, `max P M(x; a) = P L / 4`, at midspan. -/
theorem isGreatest_singleLoad {L P : ℝ} (hL : 0 < L) (hP : 0 ≤ P) :
    IsGreatest {m | ∃ x ∈ Icc 0 L, ∃ a ∈ Icc 0 L, m = P * ilMoment L x a} (P * L / 4) := by
  have hmid : L / 2 ∈ Icc 0 L := ⟨by linarith, by linarith⟩
  refine ⟨⟨L / 2, hmid, L / 2, hmid, ?_⟩, ?_⟩
  · rw [(ilMoment_eq_quarter_iff hL hmid hmid).mpr ⟨rfl, rfl⟩]; ring
  · rintro m ⟨x, hx, a, ha, rfl⟩
    have := mul_le_mul_of_nonneg_left (ilMoment_le_quarter hL hx a) hP
    linarith

/-! ### (d) Two equal moving loads at spacing `s` -/

/-- The bending moment under the leading load (at `a`) of two equal loads `P` at `a` and
`a + s`, by superposition of influence lines. -/
noncomputable def twoLoadMoment (P L s a : ℝ) : ℝ := P * ilMoment L a a + P * ilMoment L a (a + s)

/-- With both loads on the span, the moment under the first load is `P a (2L - 2a - s) / L`. -/
theorem twoLoadMoment_eq {P L s a : ℝ} (hs : 0 ≤ s) :
    twoLoadMoment P L s a = P * a * (2 * L - 2 * a - s) / L := by
  rw [twoLoadMoment, ilMoment_self, ilMoment_of_le (by linarith)]; ring

/-- The moment under the first load is stationary at `a = (2L - s) / 4 = L / 2 - s / 4`, the
position at which midspan bisects the distance between the load and the resultant (at
`a + s / 2`). -/
theorem hasDerivAt_twoLoadMoment {P L s : ℝ} (hL : L ≠ 0) (hs : 0 ≤ s) :
    HasDerivAt (twoLoadMoment P L s) 0 ((2 * L - s) / 4) := by
  have heq : twoLoadMoment P L s = fun a => P / L * (a * (2 * L - s) - 2 * a ^ 2) := by
    funext a; rw [twoLoadMoment_eq hs]; field_simp; ring
  rw [heq]
  have := (((hasDerivAt_id ((2 * L - s) / 4)).mul_const (2 * L - s)).sub
    (((hasDerivAt_pow 2 ((2 * L - s) / 4))).const_mul 2)).const_mul (P / L)
  exact this.congr_deriv (by push_cast; ring)

/-- The moment under the first load is at most `P (2L - s)² / (8L)` for `P ≥ 0`. -/
theorem twoLoadMoment_le {P L s : ℝ} (hP : 0 ≤ P) (hL : 0 < L) (hs : 0 ≤ s) (a : ℝ) :
    twoLoadMoment P L s a ≤ P * (2 * L - s) ^ 2 / (8 * L) := by
  rw [twoLoadMoment_eq hs, div_le_div_iff₀ hL (by positivity)]
  have hq : a * (2 * L - 2 * a - s) * 8 ≤ (2 * L - s) ^ 2 := by
    nlinarith [sq_nonneg (4 * a - (2 * L - s))]
  nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hP hL.le)]

/-- The bound is attained at `a = (2L - s) / 4`. -/
theorem twoLoadMoment_opt {P L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) :
    twoLoadMoment P L s ((2 * L - s) / 4) = P * (2 * L - s) ^ 2 / (8 * L) := by
  rw [twoLoadMoment_eq hs]; field_simp; ring

/-- **Two moving loads**: if `s ≤ 2L / 3` (so the optimal position keeps both loads on the span,
`0 ≤ a` and `a + s ≤ L`), the greatest moment under the first load is `P (2L - s)² / (8L)`. -/
theorem isGreatest_twoLoad {P L s : ℝ} (hP : 0 ≤ P) (hL : 0 < L) (hs : 0 ≤ s)
    (hs' : s ≤ 2 * L / 3) :
    IsGreatest (twoLoadMoment P L s '' Icc 0 (L - s)) (P * (2 * L - s) ^ 2 / (8 * L)) := by
  refine ⟨⟨(2 * L - s) / 4, ⟨by linarith, by linarith⟩, twoLoadMoment_opt hL hs⟩, ?_⟩
  rintro m ⟨a, -, rfl⟩
  exact twoLoadMoment_le hP hL hs a

/-- **Which load case governs**: the two-load maximum `(2L - s)² / (8L)` (per unit `P`) is at
least the single-load maximum `L / 4` iff `s ≤ (2 - √2) L`. -/
theorem twoLoad_ge_single_iff {L s : ℝ} (hL : 0 < L) (hs : s ≤ L) :
    L / 4 ≤ (2 * L - s) ^ 2 / (8 * L) ↔ s ≤ (2 - √2) * L := by
  have ht : 0 ≤ 2 * L - s := by linarith
  have h2 : (√2 * L) ^ 2 = 2 * L ^ 2 := by
    rw [mul_pow, sq_sqrt (by norm_num)]
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  calc L * (8 * L) ≤ (2 * L - s) ^ 2 * 4 ↔ (√2 * L) ^ 2 ≤ (2 * L - s) ^ 2 := by
        rw [h2]; constructor <;> intro h <;> nlinarith
    _ ↔ √2 * L ≤ 2 * L - s := pow_le_pow_iff_left₀ (by positivity) ht two_ne_zero
    _ ↔ s ≤ (2 - √2) * L := by constructor <;> intro h <;> linarith

/-! ### (e) Müller-Breslau principle -/

/-- **Müller-Breslau principle** for `R_A`: the influence line of the reaction at `A` is the
deflected shape `v` of the beam when support `A` is given a unit displacement and the beam
rotates rigidly about `B`, i.e. the affine function with `v(0) = 1`, `v(L) = 0`. -/
theorem mullerBreslau_reacA {L : ℝ} (hL : L ≠ 0) :
    ilReacA L 0 = 1 ∧ ilReacA L L = 0 ∧
      ∀ a, ilReacA L a = (1 - a / L) * 1 + (a / L) * 0 := by
  refine ⟨by simp [ilReacA], by simp [ilReacA, hL], fun a => by simp [ilReacA]⟩

/-- **Müller-Breslau principle** for the moment at `x ∈ (0, L)`: the influence line `M(x; ·)`
is the mechanism obtained by inserting a hinge at `x` and imposing a unit relative rotation —
it vanishes at the supports, is linear on each side of `x`, and its slope jumps by `-1` across
the hinge (left slope `(L - x) / L`, right slope `-x / L`). -/
theorem mullerBreslau_moment {L x : ℝ} (hL : L ≠ 0) (hx0 : 0 < x) (hxL : x < L) :
    ilMoment L x 0 = 0 ∧ ilMoment L x L = 0 ∧
      HasDerivAt (ilMoment L x) ((L - x) / L) (x / 2) ∧
      HasDerivAt (ilMoment L x) (-(x / L)) ((x + L) / 2) ∧
      (L - x) / L - (-(x / L)) = 1 := by
  refine ⟨by rw [ilMoment_of_ge hx0.le]; simp, by rw [ilMoment_of_le hxL.le]; simp, ?_, ?_, ?_⟩
  · have h := hasDerivAt_ilMoment_left hL x (x := x / 2) (by linarith)
    simp only [ilShear, show x / 2 < x by linarith, ↓reduceIte, ilReacA] at h
    rw [show ilMoment L x = fun y => ilMoment L y x from funext (ilMoment_symm L x)]
    exact h.congr_deriv (by field_simp)
  · have h := hasDerivAt_ilMoment_right L x (x := (x + L) / 2) (by linarith)
    simp only [ilShear, show ¬((x + L) / 2 < x) by linarith, ↓reduceIte, ilReacB] at h
    rw [show ilMoment L x = fun y => ilMoment L y x from funext (ilMoment_symm L x)]
    exact h
  · field_simp; ring

end ContinuumMechanics.Structures
