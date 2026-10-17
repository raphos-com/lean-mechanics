import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Optimality-criteria update and filters in SIMP topology optimization

We formalize, abstractly in terms of element sensitivities, the density update and the
mesh-independence filters of the classical SIMP compliance-minimization algorithm, in the form
of Sigmund's "99 line" code [Sigmund2001] (see also [BendsoeSigmund2003, §1.2]).

The design is a family of element densities `x : ι → ℝ` over a finite set of elements `ι`, with
box bounds `xmin ≤ x e ≤ 1` (`0 < xmin < 1`). Given compliance sensitivities `dc e ≤ 0`, a move
limit `m > 0`, a damping exponent `η > 0` (`η = 1/2` in the 99-line code) and a Lagrange
multiplier `λ > 0` for the volume constraint, the *optimality-criteria (OC) update* is
`xnew e = max xmin (max (x e - m) (min 1 (min (x e + m) (x e * B e ^ η))))`,
`B e = -dc e / λ`. The multiplier is found by bisection on the volume `∑ e, xnew e`.

## Main results

* `ocUpdate_mem_box`, `abs_ocUpdate_sub_le`: the OC update respects the box bounds and the move
  limit;
* `ocUpdate_antitoneOn`, `ocVolume_antitoneOn`, `ocVolume_continuousOn`: the update and the total
  volume are antitone and continuous in the multiplier on `(0, ∞)`;
* `exists_ocVolume_eq`: bisection well-posedness, by the intermediate value theorem;
  `exists_ocVolume_eq_of_bounds`: a multiplier exists for every target volume between
  `∑ max xmin (x e - m)` and `∑ min 1 (x e + m)` (strictly negative sensitivities);
* `ocUpdate_fixed_iff_kkt`: fixed points of the OC update are exactly the KKT points of the
  box-constrained problem (`B e = 1` in the interior, the "constant strain energy density"
  condition `-dc e = λ`; `B e ≤ 1` at the lower bound; `B e ≥ 1` at the upper bound);
* `filterDensity_mem_Icc`, `filterDensity_const`, `filterLinear`: the density filter
  [Bourdin2001] is a linear averaging operator, preserving constants and the box;
* `coneWeight_nonneg`, `coneWeight_sum_pos`: the cone weights `max 0 (rmin - dist e f)` are
  admissible filter weights;
* `filterSens_nonpos`: the heuristic sensitivity filter of [Sigmund2001, Sigmund2000] preserves
  the sign of compliance sensitivities;
* `fderiv_comp_filterDensity`: chain rule through the density filter,
  `∂(g ∘ x̃)/∂x_f = ∑ e, ∂g/∂x̃_e · H e f / ∑ k, H e k`.

## References

* [Sigmund2001] O. Sigmund, *A 99 line topology optimization code written in Matlab*,
  Struct. Multidisc. Optim. 21 (2001) 120–127.
* [BendsoeSigmund2003] M. P. Bendsøe, O. Sigmund, *Topology Optimization: Theory, Methods and
  Applications*, Springer, 2003, §1.2.
* [Sigmund2000] O. Sigmund, *Topology optimization: a tool for the tailoring of structures and
  materials*, Phil. Trans. R. Soc. A 358 (2000) 211–227.
* [Bourdin2001] B. Bourdin, *Filters in topology optimization*, Int. J. Numer. Meth. Engng. 50
  (2001) 2143–2158.
-/

open Filter Topology Set

namespace TopologyOptimization

variable {ι : Type*}

/-! ### The OC update -/

/-- The optimality ratio `B e = -dc e / λ` of the OC method. -/
noncomputable def ocRatio (dc : ι → ℝ) (lam : ℝ) (e : ι) : ℝ := -dc e / lam

/-- The OC density update of the 99-line code with lower bound `xmin`, move limit `m` and
damping exponent `η`, at Lagrange multiplier `lam`. -/
noncomputable def ocUpdate (xmin m η : ℝ) (x dc : ι → ℝ) (lam : ℝ) (e : ι) : ℝ :=
  max xmin (max (x e - m) (min 1 (min (x e + m) (x e * ocRatio dc lam e ^ η))))

/-- The total volume `∑ e, xnew e` of the OC update at multiplier `lam`. -/
noncomputable def ocVolume [Fintype ι] (xmin m η : ℝ) (x dc : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ e, ocUpdate xmin m η x dc lam e

/-- The OC ratio is nonnegative for nonpositive sensitivities and positive multiplier. -/
theorem ocRatio_nonneg {dc : ι → ℝ} {lam : ℝ} (hdc : ∀ e, dc e ≤ 0) (hlam : 0 < lam) (e : ι) :
    0 ≤ ocRatio dc lam e :=
  div_nonneg (neg_nonneg.mpr (hdc e)) hlam.le

/-- The OC update respects the lower bound `xmin`. -/
theorem le_ocUpdate (xmin m η : ℝ) (x dc : ι → ℝ) (lam : ℝ) (e : ι) :
    xmin ≤ ocUpdate xmin m η x dc lam e :=
  le_max_left _ _

/-- The OC update respects the upper bound `1` when `xmin ≤ 1`, `m ≥ 0` and `x e ≤ 1`. -/
theorem ocUpdate_le_one {xmin m η : ℝ} {x : ι → ℝ} (dc : ι → ℝ) (lam : ℝ) {e : ι}
    (hxmin : xmin ≤ 1) (hm : 0 ≤ m) (hx : x e ≤ 1) :
    ocUpdate xmin m η x dc lam e ≤ 1 :=
  max_le hxmin (max_le (by linarith) (min_le_left _ _))

/-- Box bounds: for `x` in the box, `xmin ≤ xnew e ≤ 1`. -/
theorem ocUpdate_mem_box {xmin m η : ℝ} {x : ι → ℝ} (dc : ι → ℝ) (lam : ℝ)
    (hxmin : xmin ≤ 1) (hm : 0 ≤ m) (hx : ∀ e, x e ≤ 1) (e : ι) :
    ocUpdate xmin m η x dc lam e ∈ Icc xmin 1 :=
  ⟨le_ocUpdate _ _ _ _ _ _ _, ocUpdate_le_one dc lam hxmin hm (hx e)⟩

/-- Move limit: for `xmin ≤ x e` and `m ≥ 0`, `|xnew e - x e| ≤ m`. -/
theorem abs_ocUpdate_sub_le {xmin m η : ℝ} {x : ι → ℝ} (dc : ι → ℝ) (lam : ℝ) {e : ι}
    (hm : 0 ≤ m) (hx : xmin ≤ x e) :
    |ocUpdate xmin m η x dc lam e - x e| ≤ m := by
  have h1 : x e - m ≤ ocUpdate xmin m η x dc lam e :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : ocUpdate xmin m η x dc lam e ≤ x e + m :=
    max_le (by linarith) (max_le (by linarith)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  rw [abs_le]
  constructor <;> linarith

/-- For fixed `e`, the OC update is antitone in the multiplier on `(0, ∞)`. -/
theorem ocUpdate_antitoneOn {xmin m η : ℝ} {x dc : ι → ℝ} (hη : 0 ≤ η)
    (hx : ∀ e, 0 ≤ x e) (hdc : ∀ e, dc e ≤ 0) (e : ι) :
    AntitoneOn (fun lam => ocUpdate xmin m η x dc lam e) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have hB : ocRatio dc b e ≤ ocRatio dc a e :=
    div_le_div_of_nonneg_left (neg_nonneg.mpr (hdc e)) ha hab
  have hpow : ocRatio dc b e ^ η ≤ ocRatio dc a e ^ η :=
    Real.rpow_le_rpow (ocRatio_nonneg hdc hb e) hB hη
  have hmul : x e * ocRatio dc b e ^ η ≤ x e * ocRatio dc a e ^ η :=
    mul_le_mul_of_nonneg_left hpow (hx e)
  simp only [ocUpdate]
  gcongr

/-- The OC volume is antitone in the multiplier on `(0, ∞)`. -/
theorem ocVolume_antitoneOn [Fintype ι] {xmin m η : ℝ} {x dc : ι → ℝ} (hη : 0 ≤ η)
    (hx : ∀ e, 0 ≤ x e) (hdc : ∀ e, dc e ≤ 0) :
    AntitoneOn (ocVolume xmin m η x dc) (Ioi 0) := by
  intro a ha b hb hab
  exact Finset.sum_le_sum fun e _ => ocUpdate_antitoneOn hη hx hdc e ha hb hab

/-- For fixed `e`, the OC update is continuous in the multiplier on `(0, ∞)`. -/
theorem ocUpdate_continuousOn {xmin m η : ℝ} {x dc : ι → ℝ} (hη : 0 ≤ η) (e : ι) :
    ContinuousOn (fun lam => ocUpdate xmin m η x dc lam e) (Ioi 0) := by
  have hB : ContinuousOn (fun lam => ocRatio dc lam e) (Ioi 0) :=
    continuousOn_const.div continuousOn_id fun lam hlam => (ne_of_gt (mem_Ioi.mp hlam))
  have hP : ContinuousOn (fun lam => ocRatio dc lam e ^ η) (Ioi 0) :=
    hB.rpow_const fun _ _ => Or.inr hη
  unfold ocUpdate
  exact ContinuousOn.sup continuousOn_const (ContinuousOn.sup continuousOn_const
    (ContinuousOn.inf continuousOn_const (ContinuousOn.inf continuousOn_const
      (continuousOn_const.mul hP))))

/-- The OC volume is continuous in the multiplier on `(0, ∞)`. -/
theorem ocVolume_continuousOn [Fintype ι] {xmin m η : ℝ} {x dc : ι → ℝ} (hη : 0 ≤ η) :
    ContinuousOn (ocVolume xmin m η x dc) (Ioi 0) := by
  unfold ocVolume
  exact continuousOn_finsetSum _ fun e _ => ocUpdate_continuousOn hη e

/-- **Bisection well-posedness.** If `0 < λ₁ ≤ λ₂` bracket the target volume,
`volume λ₂ ≤ V ≤ volume λ₁`, then some multiplier `λ ∈ [λ₁, λ₂]` realizes `volume λ = V`. -/
theorem exists_ocVolume_eq [Fintype ι] {xmin m η : ℝ} {x dc : ι → ℝ} (hη : 0 ≤ η) {l₁ l₂ V : ℝ}
    (hl₁ : 0 < l₁) (hl : l₁ ≤ l₂) (h₂ : ocVolume xmin m η x dc l₂ ≤ V)
    (h₁ : V ≤ ocVolume xmin m η x dc l₁) :
    ∃ lam ∈ Icc l₁ l₂, ocVolume xmin m η x dc lam = V := by
  have hc : ContinuousOn (ocVolume xmin m η x dc) (Icc l₁ l₂) :=
    (ocVolume_continuousOn hη).mono fun t ht => lt_of_lt_of_le hl₁ ht.1
  exact intermediate_value_Icc' hl hc ⟨h₂, h₁⟩

/-- For large multipliers the OC update sits at its lower clamp `max xmin (x e - m)`. -/
theorem eventually_ocUpdate_eq_lower [Finite ι] {xmin m η : ℝ} {x dc : ι → ℝ} (hxmin : 0 < xmin)
    (hη : 0 < η) :
    ∀ᶠ lam in atTop, ∀ e, ocUpdate xmin m η x dc lam e = max xmin (x e - m) := by
  rw [eventually_all]
  intro e
  have hB : Tendsto (fun lam => ocRatio dc lam e) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hP : Tendsto (fun lam => x e * ocRatio dc lam e ^ η) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 η (Or.inr hη.le)).tendsto.comp hB).const_mul
      (x e)
    simpa [Real.zero_rpow hη.ne'] using h
  filter_upwards [hP.eventually_lt_const hxmin] with lam hlam
  have hs : min 1 (min (x e + m) (x e * ocRatio dc lam e ^ η)) < xmin :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hlam
  unfold ocUpdate
  rw [max_comm (x e - m), ← max_assoc, max_eq_left hs.le]

/-- For small positive multipliers and strictly negative sensitivities, the OC update sits at
its upper clamp `min 1 (x e + m)`. -/
theorem eventually_ocUpdate_eq_upper [Finite ι] {xmin m η : ℝ} {x dc : ι → ℝ} (hxmin : 0 < xmin)
    (hm : 0 ≤ m) (hη : 0 < η) (hxl : ∀ e, xmin ≤ x e) (hxu : ∀ e, x e ≤ 1)
    (hdc : ∀ e, dc e < 0) :
    ∀ᶠ lam in 𝓝[>] 0, ∀ e, ocUpdate xmin m η x dc lam e = min 1 (x e + m) := by
  rw [eventually_all]
  intro e
  have hxe : 0 < x e := lt_of_lt_of_le hxmin (hxl e)
  have hB : Tendsto (fun lam => ocRatio dc lam e) (𝓝[>] 0) atTop := by
    have h := tendsto_inv_nhdsGT_zero.const_mul_atTop (neg_pos.mpr (hdc e))
    refine h.congr fun lam => ?_
    simp [ocRatio, div_eq_mul_inv]
  have hP : Tendsto (fun lam => x e * ocRatio dc lam e ^ η) (𝓝[>] 0) atTop :=
    ((tendsto_rpow_atTop hη).comp hB).const_mul_atTop hxe
  filter_upwards [hP.eventually_ge_atTop (min 1 (x e + m))] with lam hlam
  have hs : min 1 (min (x e + m) (x e * ocRatio dc lam e ^ η)) = min 1 (x e + m) := by
    rw [← min_assoc, min_eq_left hlam]
  have h1 : xmin ≤ min 1 (x e + m) := le_min (le_trans (hxl e) (hxu e)) (by linarith [hxl e])
  have h2 : x e - m ≤ min 1 (x e + m) := le_min (by linarith [hxu e]) (by linarith)
  unfold ocUpdate
  rw [hs, max_eq_right h2, max_eq_right h1]

/-- **Existence of the OC multiplier.** For strictly negative sensitivities and a target volume
between the clamped volumes `∑ max xmin (x e - m) ≤ V ≤ ∑ min 1 (x e + m)`, there is a
multiplier `λ > 0` with `∑ e, xnew e (λ) = V`. -/
theorem exists_ocVolume_eq_of_bounds [Fintype ι] {xmin m η : ℝ} {x dc : ι → ℝ} {V : ℝ}
    (hxmin : 0 < xmin) (hm : 0 ≤ m) (hη : 0 < η) (hxl : ∀ e, xmin ≤ x e) (hxu : ∀ e, x e ≤ 1)
    (hdc : ∀ e, dc e < 0) (hVl : ∑ e, max xmin (x e - m) ≤ V)
    (hVu : V ≤ ∑ e, min 1 (x e + m)) :
    ∃ lam, 0 < lam ∧ ocVolume xmin m η x dc lam = V := by
  obtain ⟨l₁, hl₁, hl₁pos⟩ :=
    ((eventually_ocUpdate_eq_upper (η := η) hxmin hm hη hxl hxu hdc).and
      self_mem_nhdsWithin).exists
  obtain ⟨l₂, hl₂, hl₁₂⟩ :=
    ((eventually_ocUpdate_eq_lower (m := m) (x := x) (dc := dc) hxmin hη).and
      (eventually_ge_atTop l₁)).exists
  have hv₁ : ocVolume xmin m η x dc l₁ = ∑ e, min 1 (x e + m) :=
    Finset.sum_congr rfl fun e _ => hl₁ e
  have hv₂ : ocVolume xmin m η x dc l₂ = ∑ e, max xmin (x e - m) :=
    Finset.sum_congr rfl fun e _ => hl₂ e
  obtain ⟨lam, hlam, hv⟩ := exists_ocVolume_eq hη.le (mem_Ioi.mp hl₁pos) hl₁₂
    (hv₂ ▸ hVl) (hv₁ ▸ hVu)
  exact ⟨lam, lt_of_lt_of_le (mem_Ioi.mp hl₁pos) hlam.1, hv⟩

/-! ### Fixed points of the OC update are KKT points -/

/-- For `B ≥ 0` and `η > 0`: `B ^ η ≤ 1 ↔ B ≤ 1`. -/
theorem rpow_le_one_iff_of_nonneg {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    B ^ η ≤ 1 ↔ B ≤ 1 := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_le.mpr (Real.one_lt_rpow (lt_of_not_ge h') hη))
  · intro h
    exact Real.rpow_le_one hB h hη.le

/-- For `B ≥ 0` and `η > 0`: `1 ≤ B ^ η ↔ 1 ≤ B`. -/
theorem one_le_rpow_iff_of_nonneg {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    1 ≤ B ^ η ↔ 1 ≤ B := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_le.mpr (Real.rpow_lt_one hB (lt_of_not_ge h') hη))
  · intro h
    exact Real.one_le_rpow h hη.le

/-- The clamp of the OC update at an interior density `xmin < a < 1` returns `a` iff the
unclamped value `t` equals `a`. -/
theorem clamp_eq_iff_of_interior {xmin m a t : ℝ} (hl : xmin < a) (hu : a < 1) (hm : 0 < m) :
    max xmin (max (a - m) (min 1 (min (a + m) t))) = a ↔ t = a := by
  constructor
  · intro h
    rcases lt_trichotomy t a with ht | ht | ht
    · have : max xmin (max (a - m) (min 1 (min (a + m) t))) < a :=
        max_lt hl (max_lt (by linarith) (lt_of_le_of_lt
          (le_trans (min_le_right _ _) (min_le_right _ _)) ht))
      linarith
    · exact ht
    · have : a < max xmin (max (a - m) (min 1 (min (a + m) t))) :=
        lt_of_lt_of_le (lt_min hu (lt_min (by linarith) ht))
          (le_trans (le_max_right _ _) (le_max_right _ _))
      linarith
  · rintro rfl
    rw [min_eq_right (by linarith : t ≤ t + m), min_eq_right hu.le,
      max_eq_right (by linarith : t - m ≤ t), max_eq_right hl.le]

/-- The clamp of the OC update at the lower bound `a = xmin < 1` returns `a` iff `t ≤ a`. -/
theorem clamp_eq_iff_of_lower {m a t : ℝ} (hu : a < 1) (hm : 0 < m) :
    max a (max (a - m) (min 1 (min (a + m) t))) = a ↔ t ≤ a := by
  constructor
  · intro h
    by_contra ht
    have : a < max a (max (a - m) (min 1 (min (a + m) t))) :=
      lt_of_lt_of_le (lt_min hu (lt_min (by linarith) (lt_of_not_ge ht)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith
  · intro ht
    exact le_antisymm (max_le le_rfl (max_le (by linarith)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ht)))) (le_max_left _ _)

/-- The clamp of the OC update at the upper bound `a = 1 > xmin` returns `a` iff `1 ≤ t`. -/
theorem clamp_eq_iff_of_upper {xmin m t : ℝ} (hxmin : xmin < 1) (hm : 0 < m) :
    max xmin (max (1 - m) (min 1 (min (1 + m) t))) = 1 ↔ 1 ≤ t := by
  constructor
  · intro h
    by_contra ht
    have : max xmin (max (1 - m) (min 1 (min (1 + m) t))) < 1 :=
      max_lt hxmin (max_lt (by linarith) (lt_of_le_of_lt
        (le_trans (min_le_right _ _) (min_le_right _ _)) (lt_of_not_ge ht)))
    linarith
  · intro ht
    exact le_antisymm (max_le hxmin.le (max_le (by linarith) (min_le_left _ _)))
      (le_trans (le_min le_rfl (le_min (by linarith) ht))
        (le_trans (le_max_right _ _) (le_max_right _ _)))

/-- **Fixed points are KKT points.** For `x` in the box (`0 < xmin < 1`), a positive move limit
and damping, `λ > 0` and `dc ≤ 0`, the density `x e` is a fixed point of the OC update iff
either `xmin < x e < 1` and `B e = 1`, or `x e = xmin` and `B e ≤ 1`, or `x e = 1` and
`B e ≥ 1`. In particular no assumption on the move limit being inactive is needed. -/
theorem ocUpdate_fixed_iff_kkt {xmin m η lam : ℝ} {x dc : ι → ℝ} (hxmin : 0 < xmin)
    (hxmin1 : xmin < 1) (hm : 0 < m) (hη : 0 < η) (hlam : 0 < lam) (hdc : ∀ e, dc e ≤ 0)
    {e : ι} (hxl : xmin ≤ x e) (hxu : x e ≤ 1) :
    ocUpdate xmin m η x dc lam e = x e ↔
      (xmin < x e ∧ x e < 1 ∧ ocRatio dc lam e = 1) ∨
      (x e = xmin ∧ ocRatio dc lam e ≤ 1) ∨ (x e = 1 ∧ 1 ≤ ocRatio dc lam e) := by
  have hxe : 0 < x e := lt_of_lt_of_le hxmin hxl
  have hB := ocRatio_nonneg hdc hlam e
  have hle : x e * ocRatio dc lam e ^ η ≤ x e ↔ ocRatio dc lam e ≤ 1 := by
    rw [← rpow_le_one_iff_of_nonneg hB hη]
    conv_lhs => rhs; rw [← mul_one (x e)]
    exact mul_le_mul_iff_right₀ hxe
  have hge : x e ≤ x e * ocRatio dc lam e ^ η ↔ 1 ≤ ocRatio dc lam e := by
    rw [← one_le_rpow_iff_of_nonneg hB hη]
    conv_lhs => lhs; rw [← mul_one (x e)]
    exact mul_le_mul_iff_right₀ hxe
  unfold ocUpdate
  rcases lt_or_eq_of_le hxl with hl | hl
  · rcases lt_or_eq_of_le hxu with hu | hu
    · rw [clamp_eq_iff_of_interior hl hu hm, le_antisymm_iff, hle, hge, ← le_antisymm_iff]
      constructor
      · intro h; exact Or.inl ⟨hl, hu, h⟩
      · rintro (⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h
        · exact absurd h (ne_of_gt hl)
        · exact absurd h (ne_of_lt hu)
    · have hge' := hge
      rw [hu] at hge' ⊢
      rw [clamp_eq_iff_of_upper hxmin1 hm, hge']
      constructor
      · intro h; exact Or.inr (Or.inr ⟨rfl, h⟩)
      · rintro (⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h (lt_irrefl 1)
        · exact absurd h (ne_of_gt hxmin1)
        · exact h
  · have hle' := hle
    rw [← hl] at hle' ⊢
    have hu : xmin < 1 := hxmin1
    rw [clamp_eq_iff_of_lower hu hm, hle']
    constructor
    · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rintro (⟨h, _, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (lt_irrefl _)
      · exact h
      · exact absurd h (ne_of_lt hxmin1)

/-- In the interior of the box, a fixed point of the OC update satisfies the optimality
condition `-dc e = λ` (constant strain energy density). -/
theorem neg_dc_eq_of_fixed {xmin m η lam : ℝ} {x dc : ι → ℝ} (hxmin : 0 < xmin)
    (hxmin1 : xmin < 1) (hm : 0 < m) (hη : 0 < η) (hlam : 0 < lam) (hdc : ∀ e, dc e ≤ 0)
    {e : ι} (hxl : xmin < x e) (hxu : x e < 1) (hfix : ocUpdate xmin m η x dc lam e = x e) :
    -dc e = lam := by
  rcases (ocUpdate_fixed_iff_kkt hxmin hxmin1 hm hη hlam hdc hxl.le hxu.le).mp hfix with
    ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · unfold ocRatio at h
    rwa [div_eq_one_iff_eq hlam.ne'] at h
  · exact absurd h (ne_of_gt hxl)
  · exact absurd h (ne_of_lt hxu)

/-! ### The density filter -/

/-- The density filter `x̃ e = (∑ f, H e f * x f) / ∑ f, H e f` with weights `H`. -/
noncomputable def filterDensity [Fintype ι] (H : ι → ι → ℝ) (x : ι → ℝ) (e : ι) : ℝ :=
  (∑ f, H e f * x f) / ∑ f, H e f

/-- The filtered density is a convex combination: if `a ≤ x f ≤ b` for all `f`, nonnegative
weights with positive row sums give `a ≤ x̃ e ≤ b`. -/
theorem filterDensity_mem_Icc [Fintype ι] {H : ι → ι → ℝ} {x : ι → ℝ} {a b : ℝ}
    (hH : ∀ e f, 0 ≤ H e f) (hpos : ∀ e, 0 < ∑ f, H e f) (hx : ∀ f, x f ∈ Icc a b) (e : ι) :
    filterDensity H x e ∈ Icc a b := by
  unfold filterDensity
  constructor
  · rw [le_div_iff₀ (hpos e), Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hx f).1 (hH e f)
  · rw [div_le_iff₀ (hpos e), Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => by
      rw [mul_comm b]; exact mul_le_mul_of_nonneg_left (hx f).2 (hH e f)

/-- In particular the density filter preserves the box `xmin ≤ x ≤ 1`. -/
theorem filterDensity_mem_box [Fintype ι] {H : ι → ι → ℝ} {x : ι → ℝ} {xmin : ℝ}
    (hH : ∀ e f, 0 ≤ H e f) (hpos : ∀ e, 0 < ∑ f, H e f) (hx : ∀ f, x f ∈ Icc xmin 1)
    (e : ι) : filterDensity H x e ∈ Icc xmin 1 :=
  filterDensity_mem_Icc hH hpos hx e

/-- The density filter preserves constant fields. -/
theorem filterDensity_const [Fintype ι] {H : ι → ι → ℝ} (hpos : ∀ e, 0 < ∑ f, H e f)
    (c : ℝ) (e : ι) : filterDensity H (fun _ => c) e = c := by
  change (∑ f, H e f * c) / _ = c
  rw [← Finset.sum_mul, mul_div_right_comm, div_self (hpos e).ne', one_mul]

/-- The density filter as a linear map on density fields. -/
noncomputable def filterLinear [Fintype ι] (H : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := filterDensity H
  map_add' x y := by
    funext e
    simp only [filterDensity, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' c x := by
    funext e
    simp only [filterDensity, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun f _ => by ring

/-- The linear map `filterLinear H` computes the density filter. -/
theorem filterLinear_apply [Fintype ι] (H : ι → ι → ℝ) (x : ι → ℝ) :
    filterLinear H x = filterDensity H x := rfl

/-- Linearity of the density filter: `x̃(a x + b y) = a x̃(x) + b x̃(y)`. -/
theorem filterDensity_linear [Fintype ι] (H : ι → ι → ℝ) (a b : ℝ) (x y : ι → ℝ) :
    filterDensity H (a • x + b • y) = a • filterDensity H x + b • filterDensity H y := by
  rw [← filterLinear_apply, map_add, map_smul, map_smul]
  rfl

/-- The density filter applied to a unit density at element `f` gives the normalized weights
`H e f / ∑ k, H e k`. -/
theorem filterDensity_single [Fintype ι] (H : ι → ι → ℝ) [DecidableEq ι] (f e : ι) :
    filterDensity H (Pi.single f 1) e = H e f / ∑ k, H e k := by
  unfold filterDensity
  congr 1
  rw [Finset.sum_eq_single f]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ f) h

/-! ### Cone weights -/

/-- The cone (hat) filter weight `H e f = max 0 (rmin - dist e f)` of the 99-line code. -/
noncomputable def coneWeight (rmin : ℝ) (dist : ι → ι → ℝ) (e f : ι) : ℝ :=
  max 0 (rmin - dist e f)

/-- Cone weights are nonnegative. -/
theorem coneWeight_nonneg (rmin : ℝ) (dist : ι → ι → ℝ) (e f : ι) :
    0 ≤ coneWeight rmin dist e f :=
  le_max_left _ _

/-- With `dist e e = 0`, the diagonal cone weight is `rmin`. -/
theorem coneWeight_self {rmin : ℝ} {dist : ι → ι → ℝ} (hr : 0 ≤ rmin) (hd : ∀ e, dist e e = 0)
    (e : ι) : coneWeight rmin dist e e = rmin := by
  simp [coneWeight, hd e, hr]

/-- With `rmin > 0` and `dist e e = 0`, every row of cone weights has positive sum, so the
density-filter normalizer is positive. -/
theorem coneWeight_sum_pos [Fintype ι] {rmin : ℝ} {dist : ι → ι → ℝ} (hr : 0 < rmin)
    (hd : ∀ e, dist e e = 0) (e : ι) : 0 < ∑ f, coneWeight rmin dist e f := by
  have h : coneWeight rmin dist e e ≤ ∑ f, coneWeight rmin dist e f :=
    Finset.single_le_sum (fun f _ => coneWeight_nonneg rmin dist e f) (Finset.mem_univ e)
  rw [coneWeight_self hr.le hd] at h
  linarith

/-! ### The sensitivity filter -/

/-- The heuristic sensitivity filter of the 99-line code,
`dĉ e = (∑ f, H e f * x f * dc f) / (x e * ∑ f, H e f)`. -/
noncomputable def filterSens [Fintype ι] (H : ι → ι → ℝ) (x dc : ι → ℝ) (e : ι) : ℝ :=
  (∑ f, H e f * x f * dc f) / (x e * ∑ f, H e f)

/-- The sensitivity filter preserves the sign of compliance sensitivities: `dĉ ≤ 0`. -/
theorem filterSens_nonpos [Fintype ι] {H : ι → ι → ℝ} {x dc : ι → ℝ} (hH : ∀ e f, 0 ≤ H e f)
    (hx : ∀ f, 0 ≤ x f) (hdc : ∀ f, dc f ≤ 0) (e : ι) : filterSens H x dc e ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg
    (Finset.sum_nonpos fun f _ =>
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hH e f) (hx f)) (hdc f))
    (mul_nonneg (hx e) (Finset.sum_nonneg fun f _ => hH e f))

/-! ### Chain rule through the density filter -/

/-- **Chain rule for the density filter.** For `g` differentiable at the filtered density,
the partial derivative of `x ↦ g (x̃)` with respect to `x f` is
`∑ e, (∂g/∂x̃ e) * H e f / ∑ k, H e k`. -/
theorem fderiv_comp_filterDensity [Fintype ι] [DecidableEq ι] (H : ι → ι → ℝ) (g : (ι → ℝ) → ℝ)
    (x : ι → ℝ) (hg : DifferentiableAt ℝ g (filterDensity H x)) (f : ι) :
    fderiv ℝ (fun y => g (filterDensity H y)) x (Pi.single f 1) =
      ∑ e, fderiv ℝ g (filterDensity H x) (Pi.single e 1) * (H e f / ∑ k, H e k) := by
  set F : (ι → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (filterLinear H)
  have hF : ∀ y, F y = filterDensity H y := fun _ => rfl
  have hcomp : (fun y => g (filterDensity H y)) = g ∘ F := by
    rfl
  rw [hcomp, fderiv_comp x (hF x ▸ hg) F.differentiableAt, F.fderiv,
    ContinuousLinearMap.comp_apply, hF]
  set L := fderiv ℝ g (filterDensity H x)
  have hv : filterDensity H (Pi.single f 1) = ∑ e, (H e f / ∑ k, H e k) • Pi.single e 1 := by
    funext e'
    rw [filterDensity_single, Finset.sum_apply]
    simp [Pi.single_apply]
  rw [show F (Pi.single f 1) = filterDensity H (Pi.single f 1) from hF _, hv, map_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [map_smul, smul_eq_mul, mul_comm]

end TopologyOptimization
