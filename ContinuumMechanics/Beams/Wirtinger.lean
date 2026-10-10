import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Wirtinger's inequality on an interval

For `u ∈ C¹` with `u(0) = u(L) = 0`,

`(π/L)² ∫₀ᴸ u² ≤ ∫₀ᴸ u'²`  (**Wirtinger's inequality**, the first Dirichlet eigenvalue of `-d²/dx²`
on `(0, L)` is `(π/L)²`).

We avoid Fourier series and singular weights with **Picone's identity**: for a positive `φ` with
`φ'' = -k² φ` and `ψ = φ'/φ`,

`u'² - k² u² = (u' - u ψ)² + (u² ψ)'`.

Taking `φ(x) = sin(k (x + δ))` with `k = π/(L + 2δ)`, `φ > 0` on `[0, L]`; integrating gives
`k² ∫ u² ≤ ∫ u'²`, and `δ → 0⁺` gives the sharp constant. As a corollary, for `w ∈ C²` with
`w(0) = w(L) = 0`, `(π/L)² ∫ w'² ≤ ∫ w''²`, which is the Rayleigh-quotient bound behind the Euler
buckling load ([TimoshenkoGere1961], §2.1; [HardyLittlewoodPolya1952], §7.7).

## Main results

* `ContinuumMechanics.Beams.wirtinger`: Wirtinger's inequality.
* `ContinuumMechanics.Beams.wirtinger_deriv`: `(π/L)² ∫ w'² ≤ ∫ w''²` for `w(0) = w(L) = 0`.

## References

* [TimoshenkoGere1961] S. P. Timoshenko, J. M. Gere, *Theory of Elastic Stability*, §2.1.
* [HardyLittlewoodPolya1952] G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, §7.7.
-/

open Set Real intervalIntegral Filter Topology
open scoped Real

namespace ContinuumMechanics.Beams

/-- Picone's identity integrated against `φ(x) = sin(k(x + δ))`: `k² ∫ u² ≤ ∫ u'²` with
`k = π/(L + 2δ)`. -/
theorem wirtinger_aux {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (h0 : u 0 = 0) (h1 : u L = 0) :
    (π / (L + 2 * δ)) ^ 2 * ∫ x in (0 : ℝ)..L, u x ^ 2 ≤ ∫ x in (0 : ℝ)..L, deriv u x ^ 2 := by
  set k := π / (L + 2 * δ) with hk_def
  have hk : 0 < k := by positivity
  have hkL : k * (L + 2 * δ) = π := by rw [hk_def]; field_simp
  have hpos : ∀ x ∈ Icc 0 L, 0 < sin (k * (x + δ)) := fun x hx => by
    apply sin_pos_of_pos_of_lt_pi
    · have := hx.1; positivity
    · nlinarith [hx.2]
  let ψ : ℝ → ℝ := fun x => k * cos (k * (x + δ)) / sin (k * (x + δ))
  have hψ : ∀ x ∈ Icc 0 L, HasDerivAt ψ (-k ^ 2 - ψ x ^ 2) x := fun x hx => by
    have dθ : HasDerivAt (fun x => k * (x + δ)) k x := by
      simpa using ((hasDerivAt_id x).add_const δ).const_mul k
    have hs := hpos x hx
    have := (dθ.cos.const_mul k).div dθ.sin hs.ne'
    refine this.congr_deriv ?_
    simp only [ψ]
    field_simp
  have du : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((hu.differentiable one_ne_zero) x).hasDerivAt
  have hdc : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hψc : ContinuousOn ψ (Icc 0 L) := fun x hx =>
    (hψ x hx).continuousAt.continuousWithinAt
  set F' : ℝ → ℝ := fun x => 2 * u x * deriv u x * ψ x + u x * u x * (-k ^ 2 - ψ x ^ 2)
  have hF : ∀ x ∈ uIcc 0 L, HasDerivAt (fun x => u x * u x * ψ x) (F' x) x := fun x hx => by
    rw [uIcc_of_le hL.le] at hx
    refine (((du x).mul (du x)).mul (hψ x hx)).congr_deriv ?_
    simp only [F', Pi.mul_apply]
    ring
  have hF'c : ContinuousOn F' (Icc 0 L) := by
    have hu' := hu.continuous
    refine ((((continuous_const.mul hu').mul hdc).continuousOn.mul hψc).add
      ((hu'.mul hu').continuousOn.mul (continuousOn_const.sub (hψc.pow 2))))
  have hF'i : IntervalIntegrable F' MeasureTheory.volume 0 L :=
    (hF'c.mono (uIcc_of_le hL.le).subset).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt hF hF'i
  simp only [h0, h1, mul_zero, zero_mul, sub_zero] at hftc
  -- integrate Picone's identity
  have hsq : ContinuousOn (fun x => (deriv u x - u x * ψ x) ^ 2) (Icc 0 L) :=
    (hdc.continuousOn.sub (hu.continuous.continuousOn.mul hψc)).pow 2
  have hsqi : IntervalIntegrable (fun x => (deriv u x - u x * ψ x) ^ 2) MeasureTheory.volume 0 L :=
    (hsq.mono (uIcc_of_le hL.le).subset).intervalIntegrable
  have hid : ∫ x in (0 : ℝ)..L, (deriv u x ^ 2 - k ^ 2 * u x ^ 2) =
      ∫ x in (0 : ℝ)..L, ((deriv u x - u x * ψ x) ^ 2 + F' x) := by
    refine integral_congr fun x _ => ?_
    simp only [F']
    ring
  have i1 : IntervalIntegrable (fun x => deriv u x ^ 2) MeasureTheory.volume 0 L :=
    (hdc.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => k ^ 2 * u x ^ 2) MeasureTheory.volume 0 L :=
    ((hu.continuous.pow 2).const_mul _).intervalIntegrable _ _
  rw [integral_add hsqi hF'i, hftc, add_zero, integral_sub i1 i2, integral_const_mul] at hid
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..L, (deriv u x - u x * ψ x) ^ 2 :=
    integral_nonneg hL.le fun x _ => sq_nonneg _
  linarith

/-- **Wirtinger's inequality**: `(π/L)² ∫₀ᴸ u² ≤ ∫₀ᴸ u'²` for `u ∈ C¹` with `u(0) = u(L) = 0`.
[HardyLittlewoodPolya1952], §7.7. -/
theorem wirtinger {L : ℝ} (hL : 0 < L) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (h0 : u 0 = 0)
    (h1 : u L = 0) :
    (π / L) ^ 2 * ∫ x in (0 : ℝ)..L, u x ^ 2 ≤ ∫ x in (0 : ℝ)..L, deriv u x ^ 2 := by
  have hlim : Tendsto (fun δ : ℝ => (π / (L + 2 * δ)) ^ 2 * ∫ x in (0 : ℝ)..L, u x ^ 2)
      (𝓝[>] 0) (𝓝 ((π / L) ^ 2 * ∫ x in (0 : ℝ)..L, u x ^ 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : ContinuousAt (fun δ : ℝ => (π / (L + 2 * δ)) ^ 2 * ∫ x in (0 : ℝ)..L, u x ^ 2) 0 :=
      ((continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        (by simp [hL.ne'])).pow 2).mul continuousAt_const
    simpa using hc.tendsto
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ =>
    wirtinger_aux hL hδ hu h0 h1)

/-- Integration by parts: `∫₀ᴸ w'² = -∫₀ᴸ w w''` for `w ∈ C²` with `w(0) = w(L) = 0`. -/
theorem integral_deriv_sq_eq {L : ℝ} {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (h0 : w 0 = 0)
    (h1 : w L = 0) :
    ∫ x in (0 : ℝ)..L, deriv w x ^ 2 = -∫ x in (0 : ℝ)..L, w x * deriv (deriv w) x := by
  have hw1 : ContDiff ℝ 1 (deriv w) := hw.deriv'
  have dw : ∀ x, HasDerivAt w (deriv w x) x := fun x =>
    ((hw.differentiable (by norm_num)) x).hasDerivAt
  have ddw : ∀ x, HasDerivAt (deriv w) (deriv (deriv w) x) x := fun x =>
    ((hw1.differentiable one_ne_zero) x).hasDerivAt
  have hparts := integral_mul_deriv_eq_deriv_mul (fun x _ => dw x) (fun x _ => ddw x)
    (hw1.continuous.intervalIntegrable 0 L)
    ((hw1.continuous_deriv le_rfl).intervalIntegrable 0 L)
  simp only [h0, h1, zero_mul, sub_zero, zero_sub] at hparts
  rw [hparts, neg_neg]
  exact integral_congr fun x _ => sq _

/-- **Rayleigh bound for pinned columns**: `(π/L)² ∫₀ᴸ w'² ≤ ∫₀ᴸ w''²` for `w ∈ C²` with
`w(0) = w(L) = 0`. [TimoshenkoGere1961], §2.1. -/
theorem wirtinger_deriv {L : ℝ} (hL : 0 < L) {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (h0 : w 0 = 0)
    (h1 : w L = 0) :
    (π / L) ^ 2 * ∫ x in (0 : ℝ)..L, deriv w x ^ 2 ≤
      ∫ x in (0 : ℝ)..L, deriv (deriv w) x ^ 2 := by
  set c := (π / L) ^ 2
  have hc : 0 < c := by positivity
  have hw1 : ContDiff ℝ 1 (deriv w) := hw.deriv'
  have hd : Continuous (deriv w) := hw1.continuous
  have hdd : Continuous (deriv (deriv w)) := hw1.continuous_deriv le_rfl
  set A := ∫ x in (0 : ℝ)..L, deriv w x ^ 2
  set B := ∫ x in (0 : ℝ)..L, deriv (deriv w) x ^ 2
  have hA : A = -∫ x in (0 : ℝ)..L, w x * deriv (deriv w) x := integral_deriv_sq_eq hw h0 h1
  -- Wirtinger for `w`
  have hW := wirtinger hL (hw.of_le one_le_two) h0 h1
  -- `c (-w w'') ≤ (c² w² + w''²)/2` pointwise
  have iw : IntervalIntegrable (fun x => w x * deriv (deriv w) x) MeasureTheory.volume 0 L :=
    (hw.continuous.mul hdd).intervalIntegrable _ _
  have iw2 : IntervalIntegrable (fun x => c * (c * w x ^ 2)) MeasureTheory.volume 0 L :=
    (continuous_const.mul (continuous_const.mul (hw.continuous.pow 2))).intervalIntegrable _ _
  have idd : IntervalIntegrable (fun x => deriv (deriv w) x ^ 2) MeasureTheory.volume 0 L :=
    (hdd.pow 2).intervalIntegrable _ _
  have hmono : ∫ x in (0 : ℝ)..L, c * -(w x * deriv (deriv w) x) ≤
      ∫ x in (0 : ℝ)..L, (c * (c * w x ^ 2) + deriv (deriv w) x ^ 2) / 2 := by
    refine integral_mono_on hL.le (iw.neg.const_mul c) ((iw2.add idd).div_const 2) fun x _ => ?_
    nlinarith [sq_nonneg (c * w x + deriv (deriv w) x)]
  rw [integral_const_mul, integral_neg, ← hA, integral_div, integral_add iw2 idd,
    integral_const_mul, integral_const_mul] at hmono
  nlinarith

end ContinuumMechanics.Beams
