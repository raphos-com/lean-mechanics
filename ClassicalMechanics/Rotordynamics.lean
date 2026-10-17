import ClassicalMechanics.ForcedOscillator
import ClassicalMechanics.Foucault
import ClassicalMechanics.Stability
import Mathlib.Algebra.Order.Star.Real

/-!
# Rotordynamics: the Jeffcott rotor and gyroscopic systems

**The Jeffcott rotor** ([Jeffcott1919]; [Genta2005], §4; [DenHartog1985], §7.4). A disc of
mass `m` sits at mid-span of a massless shaft of lateral stiffness `k` with external viscous
damping `c`; its centre of mass is offset by the eccentricity `e` from the geometric centre,
and the shaft spins at the constant rate `Ω`. In complex form `z = x + i y` (as in
`Foucault`) the geometric centre obeys

`m z̈ + c ż + k z = m e Ω² e^{iΩt}`.

* **Synchronous whirl** (`Jeffcott.whirl_solves`): with the dynamic stiffness
  `D(Ω) = k - mΩ² + i c Ω ≠ 0`, `z(t) = A e^{iΩt}` with `A = m e Ω² / D(Ω)` solves it.
* **Whirl amplitude** (`Jeffcott.norm_whirlAmp`, `Jeffcott.norm_whirlAmp_eq`): `|A|` is the
  amplitude `Driven.amplitude` of the forced oscillator with force `F₀ = m e Ω²`, i.e.
  `|A| = e Ω² / √((ω_n² - Ω²)² + (2ζω_nΩ)²)`, `ω_n² = k/m`, `ζ = c/(2√(km))`.
* **Critical speed** (`Jeffcott.denomC_critical`, `Jeffcott.denomC_critical_undamped`,
  `Jeffcott.tendsto_critical`): at `Ω = ω_n` the real part of `D` vanishes; without damping
  `D(ω_n) = 0` and `|A| → ∞` as `Ω → ω_n`.
* **Phase** (`Jeffcott.whirlAmp_re_pos`, `Jeffcott.whirlAmp_re_neg`,
  `Jeffcott.whirlAmp_critical`, `Jeffcott.arg_whirlAmp_critical`): below the critical speed
  `Re A > 0` (the heavy side flies out, response in phase), above it `Re A < 0`; at the
  critical speed `A = -i (m e ω_n / c)` is purely imaginary, a phase lag of `π/2`.
* **Self-centering** (`Jeffcott.tendsto_whirlAmp_atTop`, `Jeffcott.tendsto_norm_whirlAmp_atTop`,
  `Jeffcott.tendsto_centre_atTop`): as `Ω → ∞`, `A → -e`, so `|A| → e` and the centre of mass
  `z + e e^{iΩt} = (A + e) e^{iΩt}` tends to the bearing axis: the disc spins about its centre
  of mass.

**Gyroscopic systems** ([Meirovitch1970], §6.11; [Merkin1997], §6; [Thomson1880]):
`M q̈ + G q̇ + K q = 0` with `M`, `K` symmetric, `M` positive definite and `G` skew.

* The gyroscopic force does no work, `q̇ · G q̇ = 0` (`dotProduct_mulVec_self_of_skew`), so the
  energy `½ q̇ · M q̇ + ½ q · K q` is conserved (`Gyroscopic.energy_const`).
* **Gyroscopic forces cannot destabilize a stable potential** (`Gyroscopic.bounded`,
  `Gyroscopic.norm_q_le`): for `K` positive definite there is `c > 0` with
  `c (‖q(t)‖² + ‖q̇(t)‖²) ≤ 2 E(0)` for every motion and every time.

**Gyroscopic stabilization** (Thomson–Tait; [Merkin1997], §6.4): for `M = I`,
`K = diag(-k₁, -k₂)` (`k₁, k₂ > 0`, unstable without spin: `charQuad_no_spin`) and
`G = [[0, g], [-g, 0]]` (`spinning`),

* `det(λ² I + λ G + K) = λ⁴ + (g² - k₁ - k₂) λ² + k₁ k₂` (`det_spin`, `det_spinning`);
* the quadratic `μ² + b μ + c` with `c > 0` has only negative real roots iff `b > 0` and
  `b² ≥ 4c` (`quad_roots_iff`); hence all roots `μ = λ²` are real and negative iff
  `g² ≥ (√k₁ + √k₂)²` (`spin_stable_iff`), and are moreover distinct iff
  `g² > (√k₁ + √k₂)²` (`spin_stable_strict_iff`). Then every characteristic exponent `λ` is
  purely imaginary (`re_eq_zero_of_spin`): the motion is purely oscillatory.

## References

* [Jeffcott1919] H. H. Jeffcott, *The lateral vibration of loaded shafts in the neighbourhood
  of a whirling speed*, Phil. Mag. 37 (1919).
* [Genta2005] G. Genta, *Dynamics of Rotating Systems*, Springer (2005), §4.
* [DenHartog1985] J. P. Den Hartog, *Mechanical Vibrations*, Dover (1985), §7.4.
* [Meirovitch1970] L. Meirovitch, *Methods of Analytical Dynamics* (1970), §6.11.
* [Merkin1997] D. R. Merkin, *Introduction to the Theory of Stability*, Springer (1997), §6.
* [Thomson1880] W. Thomson, P. G. Tait, *Treatise on Natural Philosophy*, §345.
-/

open Complex Filter Topology Matrix

noncomputable section

namespace ClassicalMechanics

/-! ### The Jeffcott rotor -/

/-- A **Jeffcott rotor**: disc mass `m > 0`, external damping `c ≥ 0`, shaft stiffness `k > 0`
and mass eccentricity `e`. -/
structure Jeffcott where
  m : ℝ
  c : ℝ
  k : ℝ
  e : ℝ
  m_pos : 0 < m
  c_nonneg : 0 ≤ c
  k_pos : 0 < k

namespace Jeffcott

variable (J : Jeffcott)

/-- The complex **dynamic stiffness** `D(Ω) = k - mΩ² + i c Ω`. -/
def denomC (Ω : ℝ) : ℂ := J.k - J.m * Ω ^ 2 + J.c * Ω * I

/-- `Re D(Ω) = k - mΩ²`. -/
@[simp] theorem denomC_re (Ω : ℝ) : (J.denomC Ω).re = J.k - J.m * Ω ^ 2 := by
  simp [denomC, pow_two]

/-- `Im D(Ω) = c Ω`. -/
@[simp] theorem denomC_im (Ω : ℝ) : (J.denomC Ω).im = J.c * Ω := by
  simp [denomC, pow_two]

/-- The complex **whirl amplitude** `A(Ω) = m e Ω² / D(Ω)`. -/
def whirlAmp (Ω : ℝ) : ℂ := J.m * J.e * Ω ^ 2 / J.denomC Ω

/-- The **synchronous whirl** `z(t) = A e^{iΩt}` of the geometric centre. -/
def whirl (Ω t : ℝ) : ℂ := J.whirlAmp Ω * cexp (Ω * I * t)

/-- The velocity `ż = A · iΩ e^{iΩt}` of the synchronous whirl. -/
def whirlVel (Ω t : ℝ) : ℂ := J.whirlAmp Ω * (Ω * I * cexp (Ω * I * t))

/-- The acceleration `z̈ = A · (iΩ)² e^{iΩt}` of the synchronous whirl. -/
def whirlAcc (Ω t : ℝ) : ℂ := J.whirlAmp Ω * ((Ω * I) ^ 2 * cexp (Ω * I * t))

/-- **The synchronous whirl solves the Jeffcott equation**
`m z̈ + c ż + k z = m e Ω² e^{iΩt}` whenever `D(Ω) ≠ 0`. -/
theorem whirl_solves {Ω : ℝ} (hD : J.denomC Ω ≠ 0) (t : ℝ) :
    HasDerivAt (J.whirl Ω) (J.whirlVel Ω t) t ∧ HasDerivAt (J.whirlVel Ω) (J.whirlAcc Ω t) t ∧
      J.m * J.whirlAcc Ω t + J.c * J.whirlVel Ω t + J.k * J.whirl Ω t =
        J.m * J.e * Ω ^ 2 * cexp (Ω * I * t) := by
  refine ⟨(Foucault.hasDerivAt_cexp_mul _ t).const_mul _,
    ((Foucault.hasDerivAt_cexp_mul _ t).const_mul (Ω * I : ℂ)).const_mul _ |>.congr_deriv
      (by simp only [whirlAcc]; ring), ?_⟩
  have hAD : J.whirlAmp Ω * J.denomC Ω = J.m * J.e * Ω ^ 2 := div_mul_cancel₀ _ hD
  simp only [whirl, whirlVel, whirlAcc]
  unfold denomC at hAD
  linear_combination (J.m * J.whirlAmp Ω * cexp (Ω * I * t) * Ω ^ 2) * I_sq +
    cexp (Ω * I * t) * hAD

/-- The forced oscillator `m ẍ + c ẋ + k x = F₀ cos Ωt` with the rotor's parameters. -/
def toDriven (F₀ : ℝ) : Driven := ⟨J.m, J.c, J.k, F₀, J.m_pos, J.c_nonneg, J.k_pos⟩

/-- `|D(Ω)| = √((k - mΩ²)² + (cΩ)²)`, the square root of the forced-oscillator determinant. -/
theorem norm_denomC (Ω : ℝ) :
    ‖J.denomC Ω‖ = √((J.toDriven 0).denom Ω) := by
  rw [Complex.norm_def, Complex.normSq_apply, denomC_re, denomC_im]
  simp only [Driven.denom, toDriven]
  ring_nf

/-- The **whirl amplitude** `|A(Ω)|` is the forced-oscillator amplitude for the unbalance
force `F₀ = m e Ω²`. -/
theorem norm_whirlAmp (he : 0 ≤ J.e) (Ω : ℝ) :
    ‖J.whirlAmp Ω‖ = (J.toDriven (J.m * J.e * Ω ^ 2)).amplitude Ω := by
  rw [Driven.amplitude_eq, whirlAmp, norm_div, norm_denomC]
  have : 0 ≤ J.m * J.e * Ω ^ 2 := by have := J.m_pos; positivity
  congr 1
  · rw [show ((J.m : ℂ) * J.e * Ω ^ 2) = ((J.m * J.e * Ω ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg this]
    rfl

/-- The **natural frequency** (critical speed) `ω_n = √(k/m)`. -/
def ωn : ℝ := √(J.k / J.m)

/-- The **damping ratio** `ζ = c / (2√(km))`. -/
def ζ : ℝ := J.c / (2 * √(J.k * J.m))

/-- `ω_n² = k/m`. -/
theorem ωn_sq : J.ωn ^ 2 = J.k / J.m := Real.sq_sqrt (div_pos J.k_pos J.m_pos).le

/-- `ω_n > 0`. -/
theorem ωn_pos : 0 < J.ωn := Real.sqrt_pos.2 (div_pos J.k_pos J.m_pos)

/-- `2 ζ ω_n = c/m`. -/
theorem two_ζ_ωn : 2 * J.ζ * J.ωn = J.c / J.m := by
  have hk := J.k_pos; have hm := J.m_pos
  rw [ζ, ωn, Real.sqrt_mul hk.le, Real.sqrt_div' _ hm.le]
  have h1 : 0 < √J.k := Real.sqrt_pos.2 hk
  have h2 : 0 < √J.m := Real.sqrt_pos.2 hm
  field_simp
  rw [Real.sq_sqrt hm.le]

/-- **Whirl amplitude**: `|A| = e Ω² / √((ω_n² - Ω²)² + (2ζω_nΩ)²)` (for `e ≥ 0`). -/
theorem norm_whirlAmp_eq (he : 0 ≤ J.e) (Ω : ℝ) :
    ‖J.whirlAmp Ω‖ = J.e * Ω ^ 2 / √((J.ωn ^ 2 - Ω ^ 2) ^ 2 + (2 * J.ζ * J.ωn * Ω) ^ 2) := by
  rw [norm_whirlAmp _ he, Driven.amplitude, two_ζ_ωn, ωn_sq]
  simp only [toDriven]
  have := J.m_pos.ne'
  congr 1
  · field_simp
  · congr 1; field_simp; ring

/-- At the **critical speed** `Ω = ω_n` the real part of `D` vanishes. -/
theorem denomC_re_critical : (J.denomC J.ωn).re = 0 := by
  rw [denomC_re, ωn_sq]; field_simp [J.m_pos.ne']; ring

/-- At the critical speed `D(ω_n) = i c ω_n`. -/
theorem denomC_critical : J.denomC J.ωn = J.c * J.ωn * I := by
  exact Complex.ext (by simpa using J.denomC_re_critical) (by simp)

/-- Without damping `D(ω_n) = 0`: no synchronous whirl exists at the critical speed. -/
theorem denomC_critical_undamped (hc : J.c = 0) : J.denomC J.ωn = 0 := by
  rw [denomC_critical, hc]; simp

/-- At the critical speed the whirl amplitude is purely imaginary, `A = -i (m e ω_n / c)`. -/
theorem whirlAmp_critical (hc : 0 < J.c) :
    J.whirlAmp J.ωn = -((J.m * J.e * J.ωn / J.c : ℝ) : ℂ) * I := by
  have h1 : (J.c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h2 : (J.ωn : ℂ) ≠ 0 := by exact_mod_cast J.ωn_pos.ne'
  rw [whirlAmp, denomC_critical, div_eq_iff (by simp [h1, h2])]
  push_cast
  field_simp
  rw [I_sq]; ring

/-- At the critical speed the response **lags the unbalance by `π/2`**: `arg A = -π/2`. -/
theorem arg_whirlAmp_critical (hc : 0 < J.c) (he : 0 < J.e) :
    arg (J.whirlAmp J.ωn) = -(Real.pi / 2) := by
  have hr : 0 < J.m * J.e * J.ωn / J.c := by have := J.m_pos; have := J.ωn_pos; positivity
  rw [whirlAmp_critical _ hc, neg_mul, ← mul_neg, arg_real_mul _ hr, arg_neg_I]

/-- `Re A = m e Ω² (k - mΩ²) / |D|²`. -/
theorem whirlAmp_re (Ω : ℝ) :
    (J.whirlAmp Ω).re =
      J.m * J.e * Ω ^ 2 * (J.k - J.m * Ω ^ 2) / Complex.normSq (J.denomC Ω) := by
  rw [whirlAmp, div_re]
  simp [pow_two]

/-- `Im A = -m e Ω² c Ω / |D|²`. -/
theorem whirlAmp_im (Ω : ℝ) :
    (J.whirlAmp Ω).im = -(J.m * J.e * Ω ^ 2 * (J.c * Ω)) / Complex.normSq (J.denomC Ω) := by
  rw [whirlAmp, div_im]
  simp [pow_two]
  ring

/-- **Below the critical speed** the response is in phase with the unbalance: `Re A > 0`. -/
theorem whirlAmp_re_pos (he : 0 < J.e) {Ω : ℝ} (hΩ : Ω ≠ 0) (hsub : Ω ^ 2 < J.ωn ^ 2) :
    0 < (J.whirlAmp Ω).re := by
  rw [ωn_sq, lt_div_iff₀ J.m_pos] at hsub
  have hN : 0 < Complex.normSq (J.denomC Ω) := Complex.normSq_pos.2 fun h => by
    have := congrArg re h; simp at this; linarith
  rw [whirlAmp_re]
  have := J.m_pos
  have : 0 < J.k - J.m * Ω ^ 2 := by linarith
  positivity

/-- **Above the critical speed** the response is out of phase: `Re A < 0`. -/
theorem whirlAmp_re_neg (he : 0 < J.e) {Ω : ℝ} (hsup : J.ωn ^ 2 < Ω ^ 2) :
    (J.whirlAmp Ω).re < 0 := by
  rw [ωn_sq, div_lt_iff₀ J.m_pos] at hsup
  have hΩ : Ω ≠ 0 := by rintro rfl; nlinarith [J.k_pos]
  have hN : 0 < Complex.normSq (J.denomC Ω) := Complex.normSq_pos.2 fun h => by
    have := congrArg re h; simp at this; linarith
  rw [whirlAmp_re]
  have := J.m_pos
  have : J.k - J.m * Ω ^ 2 < 0 := by linarith
  apply div_neg_of_neg_of_pos _ hN
  exact mul_neg_of_pos_of_neg (by positivity) this

/-- For `Ω ≥ 0` the response lags: `Im A ≤ 0`. -/
theorem whirlAmp_im_nonpos (he : 0 ≤ J.e) {Ω : ℝ} (hΩ : 0 ≤ Ω) : (J.whirlAmp Ω).im ≤ 0 := by
  rw [whirlAmp_im, neg_div]
  have := J.m_pos; have := J.c_nonneg
  have : 0 ≤ Complex.normSq (J.denomC Ω) := Complex.normSq_nonneg _
  simp only [Left.neg_nonpos_iff]
  positivity

/-- Undamped whirl amplitude: `|A| = e Ω² / |ω_n² - Ω²|`. -/
theorem undamped_norm (hc : J.c = 0) (he : 0 ≤ J.e) (Ω : ℝ) :
    ‖J.whirlAmp Ω‖ = J.e * Ω ^ 2 / |J.ωn ^ 2 - Ω ^ 2| := by
  rw [norm_whirlAmp_eq _ he, ζ, hc]
  simp [Real.sqrt_sq_eq_abs]

/-- **Critical speed**: without damping the whirl amplitude blows up, `|A(Ω)| → ∞` as
`Ω → ω_n`. -/
theorem tendsto_critical (hc : J.c = 0) (he : 0 < J.e) :
    Tendsto (fun Ω => ‖J.whirlAmp Ω‖) (𝓝[≠] J.ωn) atTop := by
  have hω := J.ωn_pos
  have hev : ∀ᶠ Ω in 𝓝[≠] J.ωn, ‖J.whirlAmp Ω‖ = J.e * Ω ^ 2 * |J.ωn ^ 2 - Ω ^ 2|⁻¹ := by
    filter_upwards with Ω
    rw [undamped_norm _ hc he.le, div_eq_mul_inv]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hnum : Tendsto (fun Ω : ℝ => J.e * Ω ^ 2) (𝓝[≠] J.ωn) (𝓝 (J.e * J.ωn ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto _).mono_left nhdsWithin_le_nhds
  refine hnum.pos_mul_atTop (by positivity) (tendsto_inv_nhdsGT_zero.comp ?_)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun Ω : ℝ => |J.ωn ^ 2 - Ω ^ 2|) (𝓝 J.ωn) (𝓝 (|J.ωn ^ 2 - J.ωn ^ 2|)) :=
      ((continuous_const.sub (continuous_pow 2)).abs.tendsto _)
    simpa using this.mono_left nhdsWithin_le_nhds
  · have hpos : ∀ᶠ Ω in 𝓝[≠] J.ωn, 0 < Ω :=
      (eventually_gt_nhds hω).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with Ω hΩ hne
    have h' : Ω ^ 2 ≠ J.ωn ^ 2 := fun h => hne ((pow_left_inj₀ hΩ.le hω.le two_ne_zero).1 h)
    exact abs_pos.2 (sub_ne_zero.2 (Ne.symm h'))

/-- **Self-centering**: `A(Ω) → -e` as `Ω → ∞`. -/
theorem tendsto_whirlAmp_atTop : Tendsto J.whirlAmp atTop (𝓝 (-(J.e : ℂ))) := by
  have hm := J.m_pos
  have h1 : Tendsto (fun Ω : ℝ => J.k / Ω ^ 2 - J.m) atTop (𝓝 (0 - J.m)) :=
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)).sub tendsto_const_nhds
  have h2 : Tendsto (fun Ω : ℝ => J.c / Ω) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hX : Tendsto (fun Ω : ℝ => ((J.k / Ω ^ 2 - J.m : ℝ) : ℂ) + ((J.c / Ω : ℝ) : ℂ) * I)
      atTop (𝓝 (-(J.m : ℂ))) := by
    have := ((continuous_ofReal.tendsto _).comp h1).add
      (((continuous_ofReal.tendsto _).comp h2).mul_const I)
    simpa using this
  have hlim : Tendsto (fun Ω : ℝ => (J.m : ℂ) * J.e /
      (((J.k / Ω ^ 2 - J.m : ℝ) : ℂ) + ((J.c / Ω : ℝ) : ℂ) * I)) atTop
      (𝓝 ((J.m : ℂ) * J.e / -(J.m : ℂ))) :=
    tendsto_const_nhds.div hX (neg_ne_zero.2 (by exact_mod_cast hm.ne'))
  have heq : (J.m : ℂ) * J.e / -(J.m : ℂ) = -(J.e : ℂ) := by
    field_simp [show (J.m : ℂ) ≠ 0 by exact_mod_cast hm.ne']
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Ω hΩ
  have hΩ' : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hD : J.denomC Ω =
      (Ω : ℂ) ^ 2 * (((J.k / Ω ^ 2 - J.m : ℝ) : ℂ) + ((J.c / Ω : ℝ) : ℂ) * I) := by
    rw [denomC]; push_cast; field_simp
  rw [whirlAmp, hD, mul_comm ((Ω : ℂ) ^ 2), mul_div_mul_right _ _ (pow_ne_zero 2 hΩ')]

/-- **Self-centering**: the whirl radius tends to the eccentricity, `|A(Ω)| → e` as
`Ω → ∞`. -/
theorem tendsto_norm_whirlAmp_atTop (he : 0 ≤ J.e) :
    Tendsto (fun Ω => ‖J.whirlAmp Ω‖) atTop (𝓝 J.e) := by
  have := J.tendsto_whirlAmp_atTop.norm
  simpa [abs_of_nonneg he] using this

/-- **Self-centering**: the centre of mass `(A + e) e^{iΩt}` tends to the bearing axis,
`|A + e| → 0` as `Ω → ∞`; the disc rotates about its centre of mass. -/
theorem tendsto_centre_atTop :
    Tendsto (fun Ω => ‖J.whirlAmp Ω + J.e‖) atTop (𝓝 0) := by
  have := (J.tendsto_whirlAmp_atTop.add_const (J.e : ℂ)).norm
  simpa using this

end Jeffcott

/-! ### Gyroscopic systems -/

variable {n : ℕ}

/-- A skew matrix gives a vanishing quadratic form: `x · G x = 0` (the gyroscopic force does
no work). -/
theorem dotProduct_mulVec_self_of_skew {G : Matrix (Fin n) (Fin n) ℝ} (hG : Gᵀ = -G)
    (x : Fin n → ℝ) : x ⬝ᵥ G *ᵥ x = 0 := by
  have h : x ⬝ᵥ G *ᵥ x = (Gᵀ *ᵥ x) ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
  rw [hG, neg_mulVec, neg_dotProduct, dotProduct_comm (G *ᵥ x)] at h
  linarith

/-- A **gyroscopic system** `M q̈ + G q̇ + K q = 0`: small oscillations together with a skew
gyroscopic matrix `G`. -/
structure Gyroscopic (n : ℕ) extends SmallOscillations n where
  G : Matrix (Fin n) (Fin n) ℝ
  G_skew : Gᵀ = -G

namespace Gyroscopic

variable (S : Gyroscopic n)

/-- A motion of the gyroscopic system: `M q̈ + G q̇ + K q = 0`. -/
def IsMotion (γ : MotionN n) : Prop :=
  ∀ t, S.M *ᵥ γ.a t + S.G *ᵥ γ.v t + S.K *ᵥ γ.q t = 0

/-- The energy `½ q̇ · M q̇ + ½ q · K q`. -/
def energy (γ : MotionN n) (t : ℝ) : ℝ := S.toSmallOscillations.energy γ t

/-- The power of the gyroscopic force vanishes: `q̇ · G q̇ = 0`. -/
theorem gyroscopic_power (v : Fin n → ℝ) : v ⬝ᵥ S.G *ᵥ v = 0 :=
  dotProduct_mulVec_self_of_skew S.G_skew v

/-- **Conservation of energy** for gyroscopic systems. -/
theorem energy_const {γ : MotionN n} (h : S.IsMotion γ) (s t : ℝ) :
    S.energy γ s = S.energy γ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h1 := hasDerivAt_dotN (γ.hasDerivAt_v t) (hasDerivAt_mulVec S.M (γ.hasDerivAt_v t))
  have h2 := hasDerivAt_dotN (γ.hasDerivAt_q t) (hasDerivAt_mulVec S.K (γ.hasDerivAt_q t))
  convert (h1.div_const 2).add (h2.div_const 2) using 1
  · funext x; rfl
  rw [dot_mulVec_comm S.M_symm (γ.a t), dot_mulVec_comm S.K_symm (γ.q t) (γ.v t)]
  have e : γ.v t ⬝ᵥ (S.M *ᵥ γ.a t + S.G *ᵥ γ.v t + S.K *ᵥ γ.q t) = 0 := by
    rw [h t, dotProduct_zero]
  rw [dotProduct_add, dotProduct_add, S.gyroscopic_power] at e
  linarith

/-- **Gyroscopic forces cannot destabilize a stable potential**: if `K` is positive definite,
then `c (‖q(t)‖² + ‖q̇(t)‖²) ≤ 2 E(0)` for some `c > 0`, every motion and every time. -/
theorem bounded (hK : S.K.PosDef) :
    ∃ c > 0, ∀ γ : MotionN n, S.IsMotion γ → ∀ t,
      c * (‖γ.q t‖ ^ 2 + ‖γ.v t‖ ^ 2) ≤ 2 * S.energy γ 0 := by
  obtain ⟨cK, hcK, hK'⟩ := exists_coercive_of_posDef hK
  obtain ⟨cM, hcM, hM'⟩ := exists_coercive_of_posDef S.M_posDef
  refine ⟨min cK cM, lt_min hcK hcM, fun γ h t => ?_⟩
  rw [S.energy_const h 0 t]
  have a := hK' (γ.q t)
  have b := hM' (γ.v t)
  have hq : min cK cM * ‖γ.q t‖ ^ 2 ≤ cK * ‖γ.q t‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
  have hv : min cK cM * ‖γ.v t‖ ^ 2 ≤ cM * ‖γ.v t‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
  simp only [energy, SmallOscillations.energy]
  linarith

/-- Explicit position bound: `‖q(t)‖ ≤ √(2 E(0) / c)` for positive definite `K`. -/
theorem norm_q_le (hK : S.K.PosDef) :
    ∃ c > 0, ∀ γ : MotionN n, S.IsMotion γ → ∀ t, ‖γ.q t‖ ≤ √(2 * S.energy γ 0 / c) := by
  obtain ⟨c, hc, h⟩ := S.bounded hK
  refine ⟨c, hc, fun γ hγ t => ?_⟩
  have := h γ hγ t
  have : ‖γ.q t‖ ^ 2 ≤ 2 * S.energy γ 0 / c := by
    rw [le_div_iff₀ hc]; nlinarith [sq_nonneg ‖γ.v t‖]
  simpa using Real.abs_le_sqrt this

end Gyroscopic

/-! ### Gyroscopic stabilization of a two-degree-of-freedom system -/

section Spin

variable {R : Type*} [CommRing R]

/-- The gyroscopic matrix `G = [[0, g], [-g, 0]]` of a spinning body. -/
def spinG (g : R) : Matrix (Fin 2) (Fin 2) R := !![0, g; -g, 0]

/-- The stiffness matrix `K = diag(-k₁, -k₂)` (unstable for `k₁, k₂ > 0`). -/
def spinK (k₁ k₂ : R) : Matrix (Fin 2) (Fin 2) R := !![-k₁, 0; 0, -k₂]

/-- `G` is skew: `Gᵀ = -G`. -/
theorem spinG_transpose (g : R) : (spinG g)ᵀ = -spinG g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinG]

/-- **Characteristic determinant**: `det(λ² I + λ G + K) = λ⁴ + (g² - k₁ - k₂) λ² + k₁ k₂`. -/
theorem det_spin (l g k₁ k₂ : R) :
    (l ^ 2 • (1 : Matrix (Fin 2) (Fin 2) R) + l • spinG g + spinK k₁ k₂).det =
      l ^ 4 + (g ^ 2 - k₁ - k₂) * l ^ 2 + k₁ * k₂ := by
  rw [det_fin_two]
  simp [spinG, spinK]
  ring

end Spin

/-- The spinning two-degree-of-freedom system `q̈ + G q̇ + K q = 0` as a gyroscopic system. -/
def spinning (g k₁ k₂ : ℝ) : Gyroscopic 2 where
  M := 1
  K := spinK k₁ k₂
  M_symm := transpose_one
  K_symm := by ext i j; fin_cases i <;> fin_cases j <;> simp [spinK]
  M_posDef := PosDef.one
  G := spinG g
  G_skew := spinG_transpose g

/-- For `c > 0`, all complex roots of `μ² + b μ + c` are negative reals iff `b > 0` and
`b² ≥ 4c`. -/
theorem quad_roots_iff {b c : ℝ} (hc : 0 < c) :
    (∀ μ : ℂ, μ ^ 2 + b * μ + c = 0 → μ.im = 0 ∧ μ.re < 0) ↔ 0 < b ∧ 4 * c ≤ b ^ 2 := by
  constructor
  · intro h
    have hD : 4 * c ≤ b ^ 2 := by
      by_contra hlt
      push Not at hlt
      set y := √(4 * c - b ^ 2) / 2
      have hy : 0 < y := by have := Real.sqrt_pos.2 (sub_pos.2 hlt); positivity
      have hy2 : y ^ 2 = (4 * c - b ^ 2) / 4 := by
        rw [div_pow, Real.sq_sqrt (by linarith)]; ring
      have := (h ⟨-b / 2, y⟩ (by
        apply Complex.ext <;> simp [pow_two] <;> nlinarith)).1
      simp at this
      linarith
    refine ⟨?_, hD⟩
    set s := √(b ^ 2 - 4 * c)
    have hs2 : s ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have := (h (((-b + s) / 2 : ℝ) : ℂ)
      (Complex.ext (by simp [pow_two]; nlinarith) (by simp [pow_two]))).2
    simp at this
    linarith
  · rintro ⟨hb, hD⟩ μ hμ
    have hre : μ.re * μ.re - μ.im * μ.im + b * μ.re + c = 0 := by
      simpa [pow_two] using congrArg Complex.re hμ
    have him : μ.re * μ.im + μ.im * μ.re + b * μ.im = 0 := by
      simpa [pow_two] using congrArg Complex.im hμ
    have hy : μ.im = 0 := by
      by_contra hy
      have hx : 2 * μ.re + b = 0 := by
        have : μ.im * (2 * μ.re + b) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hy
      have : 0 < μ.im * μ.im := mul_self_pos.2 hy
      nlinarith
    refine ⟨hy, ?_⟩
    rw [hy] at hre
    by_contra hx
    push Not at hx
    nlinarith

/-- The characteristic quadratic `μ² + (g² - k₁ - k₂) μ + k₁ k₂` in `μ = λ²`. -/
def charQuad (g k₁ k₂ : ℝ) (μ : ℂ) : ℂ :=
  μ ^ 2 + ((g ^ 2 - k₁ - k₂ : ℝ) : ℂ) * μ + ((k₁ * k₂ : ℝ) : ℂ)

/-- The characteristic determinant (over `ℂ`) is the characteristic quadratic at `μ = λ²`. -/
theorem det_spinning (g k₁ k₂ : ℝ) (l : ℂ) :
    (l ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + l • spinG (g : ℂ) + spinK (k₁ : ℂ) k₂).det =
      charQuad g k₁ k₂ (l ^ 2) := by
  rw [det_spin, charQuad]; push_cast; ring

/-- Sign and discriminant conditions: `g² - k₁ - k₂ > 0` and `(g² - k₁ - k₂)² ≥ 4 k₁ k₂` iff
`g² ≥ (√k₁ + √k₂)²`. -/
theorem spin_disc_iff {g k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    (0 < g ^ 2 - k₁ - k₂ ∧ 4 * (k₁ * k₂) ≤ (g ^ 2 - k₁ - k₂) ^ 2) ↔
      (√k₁ + √k₂) ^ 2 ≤ g ^ 2 := by
  have e₁ := Real.sq_sqrt h₁.le
  have e₂ := Real.sq_sqrt h₂.le
  have p₁ := Real.sqrt_pos.2 h₁
  have p₂ := Real.sqrt_pos.2 h₂
  have hs : 0 < √k₁ * √k₂ := mul_pos p₁ p₂
  have hsq : k₁ * k₂ = (√k₁ * √k₂) ^ 2 := by rw [mul_pow, e₁, e₂]
  have hexp : (√k₁ + √k₂) ^ 2 = k₁ + k₂ + 2 * (√k₁ * √k₂) := by nlinarith
  rw [hexp, hsq]
  constructor
  · rintro ⟨hb, hD⟩
    nlinarith
  · intro h
    refine ⟨by linarith, ?_⟩
    nlinarith

/-- Strict form: `g² - k₁ - k₂ > 0` and `(g² - k₁ - k₂)² > 4 k₁ k₂` iff
`g² > (√k₁ + √k₂)²`. -/
theorem spin_disc_iff_strict {g k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    (0 < g ^ 2 - k₁ - k₂ ∧ 4 * (k₁ * k₂) < (g ^ 2 - k₁ - k₂) ^ 2) ↔
      (√k₁ + √k₂) ^ 2 < g ^ 2 := by
  have e₁ := Real.sq_sqrt h₁.le
  have e₂ := Real.sq_sqrt h₂.le
  have p₁ := Real.sqrt_pos.2 h₁
  have p₂ := Real.sqrt_pos.2 h₂
  have hs : 0 < √k₁ * √k₂ := mul_pos p₁ p₂
  have hsq : k₁ * k₂ = (√k₁ * √k₂) ^ 2 := by rw [mul_pow, e₁, e₂]
  have hexp : (√k₁ + √k₂) ^ 2 = k₁ + k₂ + 2 * (√k₁ * √k₂) := by nlinarith
  rw [hexp, hsq]
  constructor
  · rintro ⟨hb, hD⟩
    nlinarith
  · intro h
    refine ⟨by linarith, ?_⟩
    nlinarith

/-- **Gyroscopic stabilization**: all roots `μ = λ²` are negative reals iff
`g² ≥ (√k₁ + √k₂)²`. -/
theorem spin_stable_iff {g k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    (∀ μ : ℂ, charQuad g k₁ k₂ μ = 0 → μ.im = 0 ∧ μ.re < 0) ↔ (√k₁ + √k₂) ^ 2 ≤ g ^ 2 := by
  rw [← spin_disc_iff h₁ h₂, ← quad_roots_iff (mul_pos h₁ h₂)]
  rfl

/-- **Gyroscopic stabilization**, distinct frequencies: all roots `μ = λ²` are negative reals
and distinct iff `g² > (√k₁ + √k₂)²`. -/
theorem spin_stable_strict_iff {g k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    ((∀ μ : ℂ, charQuad g k₁ k₂ μ = 0 → μ.im = 0 ∧ μ.re < 0) ∧
        (g ^ 2 - k₁ - k₂) ^ 2 - 4 * (k₁ * k₂) ≠ 0) ↔ (√k₁ + √k₂) ^ 2 < g ^ 2 := by
  rw [← spin_disc_iff_strict h₁ h₂]
  have := (spin_stable_iff (g := g) h₁ h₂).trans (spin_disc_iff h₁ h₂).symm
  rw [this]
  constructor
  · rintro ⟨⟨hb, hD⟩, hne⟩
    exact ⟨hb, lt_of_le_of_ne hD fun h => hne (by linarith)⟩
  · rintro ⟨hb, hD⟩
    exact ⟨⟨hb, hD.le⟩, by linarith⟩

/-- Under the stabilization condition every characteristic exponent `λ` is purely imaginary:
the motion is purely oscillatory. -/
theorem re_eq_zero_of_spin {g k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hg : (√k₁ + √k₂) ^ 2 ≤ g ^ 2) {l : ℂ}
    (hl : (l ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + l • spinG (g : ℂ) +
      spinK (k₁ : ℂ) k₂).det = 0) : l.re = 0 := by
  rw [det_spinning] at hl
  obtain ⟨him, hre⟩ := (spin_stable_iff h₁ h₂).2 hg _ hl
  have him' : l.re * l.im + l.im * l.re = 0 := by simpa [pow_two] using him
  have hre' : l.re * l.re - l.im * l.im < 0 := by simpa [pow_two] using hre
  by_contra hx
  have : l.im = 0 := by
    have : l.re * (2 * l.im) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hx
    linarith
  rw [this] at hre'
  nlinarith [mul_self_nonneg l.re]

/-- Without spin (`g = 0`) `μ = k₁ > 0` is a root: `λ = √k₁` is a real positive exponent and the
equilibrium is unstable. -/
theorem charQuad_no_spin (k₁ k₂ : ℝ) : charQuad 0 k₁ k₂ k₁ = 0 := by
  rw [charQuad]; push_cast; ring

end ClassicalMechanics
