import ContinuumMechanics.Beams.String
import ContinuumMechanics.Beams.Wirtinger

/-!
# Saint-Venant's principle for antiplane shear in a strip

An **antiplane shear** deformation of a homogeneous isotropic elastic cylinder with shear modulus
`μ` has displacement `(0, 0, w(x, y))`; the only stresses are `τ_xz = μ w_x`, `τ_yz = μ w_y`, and
equilibrium reduces to **Laplace's equation** `Δw = w_xx + w_yy = 0` ([Gurtin1972], §44). We study
the strip `x ≥ 0`, `0 ≤ y ≤ b`, with **traction-free lateral sides** `w_y(x, 0) = w_y(x, b) = 0`,
loaded only at the end `x = 0` by a **self-equilibrated** traction, i.e. with zero
**resultant force** `F(x) = μ ∫₀ᵇ w_x(x, y) dy` at `x = 0`.

Fields are functions `w : ℝ → ℝ → ℝ` of the axial coordinate `x` (first argument) and the
transverse coordinate `y` (second argument), jointly `C²` as functions on `ℝ × ℝ` (the values
off the strip play no role: every equation is imposed only on the closed strip). We reuse the
partial derivatives of `ContinuumMechanics.Strings`: `dt w` is the **axial** derivative `w_x`
and `dx w` is the **transverse** derivative `w_y`.

* **Decaying modes** (`mode`, `modeSum`): `wₙ = e^{-nπx/b} cos(nπy/b)` are harmonic, satisfy the
  lateral conditions and carry zero resultant at every section, as do their finite sums; the
  `n = 0` mode, uniform shear `w = A x + C`, is the only non-decaying separated solution and it
  has resultant `μ A b`, so self-equilibrium rules it out (it reduces to a rigid translation).
* **Section-independence of the resultant** (`hasDerivAt_resultant`, `resultant_eq_on`):
  `F'(x) = μ ∫ w_xx = -μ ∫ w_yy = -μ [w_y]₀ᵇ = 0`.
* **Energy decay** (`energy_le_exp`) on a finite strip `[0, L] × [0, b]` whose far end does no
  work (`∫₀ᵇ w w_x (L, y) dy = 0`, e.g. clamped or traction-free): the strain energy
  `E(x) = (μ/2) ∫ₓᴸ ∫₀ᵇ |∇w|²` stored beyond the section `x` obeys the
  **Horgan–Knowles estimate** `E(x) ≤ E(0) e^{-2πx/b}`. The proof: `E(x) = -(μ/2) ∫₀ᵇ w w_x`
  (Clapeyron, integration by parts and `Δw = 0`), the integrand may be replaced by
  `(w - w̄) w_x` since `∫ w_x = 0` at every section, the zero-mean (Neumann) Wirtinger inequality
  `‖w - w̄‖ ≤ (b/π) ‖w_y‖` and AM–GM give `E(x) ≤ (b/2π)(-E'(x))`, and Grönwall concludes.

## Main results

* `isHarmonicAt_mode`, `mode_lateral`, `integral_dt_mode`: the decaying modes;
  `isHarmonicAt_modeSum`, `modeSum_lateral`, `resultant_modeSum`: finite superpositions;
  `abs_mode_le`, `tendsto_mode`: their exponential decay.
* `resultant_shear`, `shear_eq_const_of_resultant_eq_zero`: the non-decaying mode `n = 0`.
* `hasDerivAt_resultant`, `resultant_eq_on`, `resultant_eq_of_nonneg`: the resultant force is
  the same at every section.
* `wirtinger_mean_zero`: `(π/b)² ∫₀ᵇ u² ≤ ∫₀ᵇ u'²` for `u ∈ C¹` with `∫₀ᵇ u = 0`.
* `abs_integral_mul_dt_le`: the cross-sectional estimate `|∫ w w_x| ≤ (b/2π) ∫ (w_x² + w_y²)`.
* `energy_eq_sub`, `energy_eq`, `hasDerivAt_energy`: `E(x) = -(μ/2) ∫₀ᵇ w w_x` when the far end
  does no work (`sectionWork_eq_zero_of_clamped`, `sectionWork_eq_zero_of_free`), and
  `E'(x) = -(μ/2) ∫₀ᵇ |∇w|²`.
* `energy_le_exp`: **Saint-Venant's principle** `E(x) ≤ E(0) e^{-2πx/b}`.

## References

* [HorganKnowles1983] C. O. Horgan, J. K. Knowles, *Recent developments concerning Saint-Venant's
  principle*, Adv. Appl. Mech. 23 (1983), §2.
* [Knowles1966] J. K. Knowles, *On Saint-Venant's principle in the two-dimensional linear theory
  of elasticity*, Arch. Rational Mech. Anal. 21 (1966).
* [Gurtin1972] M. E. Gurtin, *The Linear Theory of Elasticity*, Handbuch der Physik VIa/2, §44.
* [HardyLittlewoodPolya1952] G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, §7.7.
-/

open Set Real MeasureTheory Filter Topology
open ContinuumMechanics.Strings (dt dx)

noncomputable section

namespace ContinuumMechanics.SaintVenant

/-- **Laplace's equation** `w_xx + w_yy = 0` at the point `(x, y)` (equilibrium of antiplane
shear). -/
def IsHarmonicAt (w : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  dt (dt w) x y + dx (dx w) x y = 0

/-- The **resultant force** `F(x) = μ ∫₀ᵇ w_x(x, y) dy` of the shear traction `τ_xz = μ w_x` on
the cross-section at `x`. -/
def resultant (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ * ∫ y in (0 : ℝ)..b, dt w x y

/-! ### Exact decaying solutions -/

section Modes

/-- The separated field `e^{-kx} cos(ky)`. -/
def mode (k x y : ℝ) : ℝ := exp (-k * x) * cos (k * y)

/-- The companion field `e^{-kx} sin(ky)` (the transverse derivative of `mode`, up to `-k`). -/
def modeSin (k x y : ℝ) : ℝ := exp (-k * x) * sin (k * y)

/-- Axial derivative of `mode`. -/
theorem hasDerivAt_mode_x (k x y : ℝ) :
    HasDerivAt (fun s => mode k s y) (-k * mode k x y) x := by
  have h : HasDerivAt (fun s => -k * s) (-k) x := by
    simpa using (hasDerivAt_id x).const_mul (-k)
  change HasDerivAt (fun s => exp (-k * s) * cos (k * y)) _ x
  convert h.exp.mul_const (cos (k * y)) using 1
  simp only [mode]
  ring

/-- Transverse derivative of `mode`. -/
theorem hasDerivAt_mode_y (k x y : ℝ) :
    HasDerivAt (mode k x) (-k * modeSin k x y) y := by
  have h : HasDerivAt (fun s => k * s) k y := by
    simpa using (hasDerivAt_id y).const_mul k
  change HasDerivAt (fun s => exp (-k * x) * cos (k * s)) _ y
  convert h.cos.const_mul (exp (-k * x)) using 1
  simp only [modeSin]
  ring

/-- Transverse derivative of `modeSin`. -/
theorem hasDerivAt_modeSin_y (k x y : ℝ) :
    HasDerivAt (modeSin k x) (k * mode k x y) y := by
  have h : HasDerivAt (fun s => k * s) k y := by
    simpa using (hasDerivAt_id y).const_mul k
  change HasDerivAt (fun s => exp (-k * x) * sin (k * s)) _ y
  convert h.sin.const_mul (exp (-k * x)) using 1
  simp only [mode]
  ring

/-- A finite superposition `∑ₙ cₙ e^{-kₙx} cos(kₙy)`. -/
def modeSum (s : Finset ℕ) (c k : ℕ → ℝ) (x y : ℝ) : ℝ := ∑ n ∈ s, c n * mode (k n) x y

/-- The companion superposition `∑ₙ cₙ e^{-kₙx} sin(kₙy)`. -/
def modeSinSum (s : Finset ℕ) (c k : ℕ → ℝ) (x y : ℝ) : ℝ := ∑ n ∈ s, c n * modeSin (k n) x y

variable (s : Finset ℕ) (c k : ℕ → ℝ)

/-- Axial derivative of a mode sum. -/
theorem dt_modeSum : dt (modeSum s c k) = modeSum s (fun n => -k n * c n) k := by
  funext x y
  refine (HasDerivAt.fun_sum fun n _ => (hasDerivAt_mode_x (k n) x y).const_mul (c n)).deriv.trans
    ?_
  simp only [modeSum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Transverse derivative of a mode sum. -/
theorem dx_modeSum : dx (modeSum s c k) = modeSinSum s (fun n => -k n * c n) k := by
  funext x y
  refine (HasDerivAt.fun_sum fun n _ => (hasDerivAt_mode_y (k n) x y).const_mul (c n)).deriv.trans
    ?_
  simp only [modeSinSum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Transverse derivative of a companion sum. -/
theorem dx_modeSinSum : dx (modeSinSum s c k) = modeSum s (fun n => k n * c n) k := by
  funext x y
  refine (HasDerivAt.fun_sum fun n _ =>
    (hasDerivAt_modeSin_y (k n) x y).const_mul (c n)).deriv.trans ?_
  simp only [modeSum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Every mode sum is harmonic**: `Δ(∑ cₙ e^{-kₙx} cos(kₙy)) = 0`, for arbitrary
wavenumbers `kₙ`. -/
theorem isHarmonicAt_modeSum (x y : ℝ) : IsHarmonicAt (modeSum s c k) x y := by
  rw [IsHarmonicAt, dt_modeSum, dt_modeSum, dx_modeSum, dx_modeSinSum, modeSum, modeSum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun n _ => by ring

/-- A single mode `e^{-kx} cos(ky)` is harmonic. -/
theorem isHarmonicAt_mode (k₀ x y : ℝ) : IsHarmonicAt (mode k₀) x y := by
  have h := isHarmonicAt_modeSum {0} (fun _ => 1) (fun _ => k₀) x y
  have e : modeSum {0} (fun _ => 1) (fun _ => k₀) = mode k₀ := by
    funext x y
    simp [modeSum]
  rwa [e] at h

/-- The strip wavenumbers `kₙ = nπ/b`. -/
def wavenumber (b : ℝ) (n : ℕ) : ℝ := n * π / b

/-- **Traction-free lateral sides**: a superposition of the strip modes `cos(nπy/b)` has
`w_y = 0` on `y = 0` and on `y = b`. -/
theorem modeSum_lateral {b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    dx (modeSum s c (wavenumber b)) x 0 = 0 ∧ dx (modeSum s c (wavenumber b)) x b = 0 := by
  rw [dx_modeSum]
  refine ⟨Finset.sum_eq_zero fun n _ => by simp [modeSin],
    Finset.sum_eq_zero fun n _ => ?_⟩
  simp only [modeSin, wavenumber, div_mul_cancel₀ _ hb, sin_nat_mul_pi]
  ring

/-- A single strip mode satisfies the traction-free lateral conditions. -/
theorem mode_lateral {b : ℝ} (hb : b ≠ 0) (n : ℕ) (x : ℝ) :
    dx (mode (wavenumber b n)) x 0 = 0 ∧ dx (mode (wavenumber b n)) x b = 0 := by
  have e : modeSum {n} (fun _ => 1) (wavenumber b) = mode (wavenumber b n) := by
    funext x y
    simp [modeSum]
  rw [← e]
  exact modeSum_lateral _ _ hb x

/-- **Zero resultant at every section**: `∫₀ᵇ kₙ e^{-kₙx} cos(kₙy) dy = 0` with `kₙ = nπ/b`
(for `n = 0` because `k₀ = 0`, for `n ≥ 1` because `∫₀ᵇ cos(nπy/b) dy = 0`). -/
theorem integral_dt_mode {b : ℝ} (hb : b ≠ 0) (n : ℕ) (x : ℝ) :
    ∫ y in (0 : ℝ)..b, wavenumber b n * mode (wavenumber b n) x y = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [wavenumber]
  have hI : ∫ y in (0 : ℝ)..b, cos (n * π / b * y) = 0 := by
    have := Strings.integral_cos_int hb (n : ℤ)
    simpa [hn] using this
  simp only [mode, wavenumber, ← mul_assoc, intervalIntegral.integral_const_mul, hI, mul_zero]

/-- **Self-equilibrated sections**: every finite superposition of strip modes carries zero
resultant force on every cross-section. -/
theorem resultant_modeSum {b : ℝ} (hb : b ≠ 0) (μ x : ℝ) :
    resultant μ b (modeSum s c (wavenumber b)) x = 0 := by
  rw [resultant, dt_modeSum]
  simp only [modeSum]
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (Continuous.intervalIntegrable (by simp only [mode]; fun_prop) _ _)]
  simp only [show ∀ n y, -wavenumber b n * c n * mode (wavenumber b n) x y =
      -c n * (wavenumber b n * mode (wavenumber b n) x y) from fun n y => by ring,
    intervalIntegral.integral_const_mul, integral_dt_mode hb, mul_zero, Finset.sum_const_zero]

/-- **Exponential decay of a mode**: `|e^{-kx} cos(ky)| ≤ e^{-kx}`. -/
theorem abs_mode_le (k₀ x y : ℝ) : |mode k₀ x y| ≤ exp (-k₀ * x) := by
  rw [mode, abs_mul, abs_exp]
  exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

/-- Each strip mode with `n ≥ 1` tends to zero away from the loaded end (for `b > 0`). -/
theorem tendsto_mode {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    Tendsto (fun x => mode (wavenumber b n) x y) atTop (𝓝 0) := by
  have hk : 0 < wavenumber b n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold wavenumber
    positivity
  have h := (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
    (neg_neg_of_pos hk))).mul_const (cos (wavenumber b n * y))
  simpa [mode] using h

/-- The **uniform shear** field `w = A x + C` (the separated solution with `k = 0`). -/
def shear (A C x _y : ℝ) : ℝ := A * x + C

/-- Uniform shear is harmonic. -/
theorem isHarmonicAt_shear (A C x y : ℝ) : IsHarmonicAt (shear A C) x y := by
  have h1 : dt (shear A C) = fun _ _ => A := by
    funext x y
    exact ((hasDerivAt_id x).const_mul A |>.add_const C).deriv.trans (mul_one A)
  have h2 : dx (shear A C) = fun _ _ => 0 := by
    funext x y
    exact deriv_const y _
  have h3 : dt (fun (_ _ : ℝ) => A) = fun _ _ => 0 := by
    funext x y
    exact deriv_const x _
  have h4 : dx (fun (_ _ : ℝ) => (0 : ℝ)) = fun _ _ => 0 := by
    funext x y
    exact deriv_const y _
  rw [IsHarmonicAt, h1, h2, h3, h4, add_zero]

/-- Uniform shear has traction-free lateral sides. -/
theorem dx_shear (A C x y : ℝ) : dx (shear A C) x y = 0 :=
  deriv_const y _

/-- Uniform shear carries the resultant `μ A b` on every section: it does **not** decay. -/
theorem resultant_shear (μ b A C x : ℝ) : resultant μ b (shear A C) x = μ * (A * b) := by
  have h1 : dt (shear A C) = fun _ _ => A := by
    funext x y
    exact ((hasDerivAt_id x).const_mul A |>.add_const C).deriv.trans (mul_one A)
  rw [resultant, h1]
  simp [mul_comm]

/-- **Self-equilibrium excludes the non-decaying mode**: a uniform shear with zero resultant
(`μ ≠ 0`, `b ≠ 0`) is a rigid translation `w = C`. -/
theorem shear_eq_const_of_resultant_eq_zero {μ b A C : ℝ} (hμ : μ ≠ 0) (hb : b ≠ 0) {x₀ : ℝ}
    (h : resultant μ b (shear A C) x₀ = 0) : ∀ x y, shear A C x y = C := by
  rw [resultant_shear] at h
  have hA : A = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hμ
    · exact (mul_eq_zero.1 h).resolve_right hb
  intro x y
  simp [shear, hA]

end Modes


/-! ### Differentiation of sectional integrals -/

section Sections

/-- **Differentiation under the integral sign** over a cross-section: if `G(s, y)` and its axial
derivative `G'(s, y)` are continuous on `ℝ × ℝ`, then `d/ds ∫₀ᵇ G(s, y) dy = ∫₀ᵇ G'(s, y) dy`. -/
theorem hasDerivAt_integral_section {G G' : ℝ × ℝ → ℝ} (hG : Continuous G)
    (hG' : Continuous G') (hd : ∀ s y, HasDerivAt (fun s => G (s, y)) (G' (s, y)) s)
    (b x : ℝ) :
    HasDerivAt (fun s => ∫ y in (0 : ℝ)..b, G (s, y)) (∫ y in (0 : ℝ)..b, G' (x, y)) x := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := (0 : ℝ)) (b := b))
    ).exists_bound_of_continuousOn hG'.continuousOn
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := b) (F := fun s y => G (s, y)) (F' := fun s y => G' (s, y))
    (x₀ := x) (bound := fun _ => M) (Metric.closedBall_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun s =>
      (hG.comp (Continuous.prodMk_right s)).aestronglyMeasurable)
    ((hG.comp (Continuous.prodMk_right x)).intervalIntegrable 0 b)
    (hG'.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y hy s hs =>
      hM (s, y) ⟨hs, Set.uIoc_subset_uIcc hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun y _ s _ => hd s y)).2

end Sections

/-! ### The resultant force is the same at every section -/

section Resultant

variable {μ b : ℝ} {w : ℝ → ℝ → ℝ}

/-- **The resultant does not depend on the section**: for a `C²` field that is harmonic on the
section `x` and has traction-free lateral sides there,
`F'(x) = μ ∫₀ᵇ w_xx = -μ ∫₀ᵇ w_yy = -μ (w_y(x, b) - w_y(x, 0)) = 0`. -/
theorem hasDerivAt_resultant (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b) {x : ℝ}
    (hh : ∀ y ∈ Icc 0 b, IsHarmonicAt w x y) (h0 : dx w x 0 = 0) (h1 : dx w x b = 0) :
    HasDerivAt (resultant μ b w) 0 x := by
  set A := Strings.dirDeriv (Function.uncurry w) (1, 0) with hAdef
  set B := Strings.dirDeriv (Function.uncurry w) (0, 1) with hBdef
  have hA : ContDiff ℝ 1 A := Strings.contDiff_dirDeriv hU _
  have hB : ContDiff ℝ 1 B := Strings.contDiff_dirDeriv hU _
  have dA := hA.differentiable one_ne_zero
  have dB := hB.differentiable one_ne_zero
  have cA1 : Continuous fun p => fderiv ℝ A p (1, 0) :=
    (hA.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cB2 : Continuous fun p => fderiv ℝ B p (0, 1) :=
    (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have e : resultant μ b w = fun s => μ * ∫ y in (0 : ℝ)..b, A (s, y) := by
    funext s
    rw [resultant, Strings.dt_eq_dirDeriv hU]
  have hd := (hasDerivAt_integral_section hA.continuous cA1
    (fun s y => Strings.hasDerivAt_fst_of_differentiable dA s y) b x).const_mul μ
  rw [e]
  refine hd.congr_deriv ?_
  have hc : ∫ y in (0 : ℝ)..b, fderiv ℝ A (x, y) (1, 0) =
      ∫ y in (0 : ℝ)..b, -fderiv ℝ B (x, y) (0, 1) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hb] at hy
    have h := hh y hy
    have e1 : dt (dt w) x y = fderiv ℝ A (x, y) (1, 0) := Strings.dt_dt_eq hU x y
    have e2 : dx (dx w) x y = fderiv ℝ B (x, y) (0, 1) := Strings.dx_dx_eq hU x y
    rw [IsHarmonicAt, e1, e2] at h
    linarith
  have eB : ∀ y, B (x, y) = dx w x y := fun y => by rw [Strings.dx_eq_dirDeriv hU]
  rw [hc, intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => Strings.hasDerivAt_snd_of_differentiable dB x y)
    ((cB2.comp (Continuous.prodMk_right x)).intervalIntegrable 0 b), eB, eB, h0, h1]
  simp

/-- **Section-independence of the resultant** on `[0, L]`: if `w` is harmonic on the strip
`[0, L] × [0, b]` with traction-free lateral sides, then `F(x) = F(0)` for `x ∈ [0, L]`. -/
theorem resultant_eq_on (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b) {L : ℝ}
    (hh : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 b, IsHarmonicAt w x y)
    (h0 : ∀ x ∈ Icc 0 L, dx w x 0 = 0) (h1 : ∀ x ∈ Icc 0 L, dx w x b = 0) :
    ∀ x ∈ Icc 0 L, resultant μ b w x = resultant μ b w 0 := by
  have hd : ∀ x ∈ Icc 0 L, HasDerivAt (resultant μ b w) 0 x := fun x hx =>
    hasDerivAt_resultant hU hb (hh x hx) (h0 x hx) (h1 x hx)
  exact constant_of_has_deriv_right_zero (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    fun x hx => (hd x (Ico_subset_Icc_self hx)).hasDerivWithinAt

/-- **Section-independence of the resultant** on the semi-infinite strip `x ≥ 0`. In particular
a self-equilibrated end load (`F(0) = 0`) leaves every section self-equilibrated. -/
theorem resultant_eq_of_nonneg (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b)
    (hh : ∀ x ≥ 0, ∀ y ∈ Icc 0 b, IsHarmonicAt w x y)
    (h0 : ∀ x ≥ 0, dx w x 0 = 0) (h1 : ∀ x ≥ 0, dx w x b = 0) {x : ℝ} (hx : 0 ≤ x) :
    resultant μ b w x = resultant μ b w 0 :=
  resultant_eq_on (L := x) hU hb (fun s hs => hh s hs.1) (fun s hs => h0 s hs.1)
    (fun s hs => h1 s hs.1) x ⟨hx, le_rfl⟩

end Resultant

/-! ### The zero-mean (Neumann) Wirtinger inequality -/

/-- **Wirtinger's inequality for zero-mean functions**: `(π/b)² ∫₀ᵇ u² ≤ ∫₀ᵇ u'²` for `u ∈ C¹`
with `∫₀ᵇ u = 0` (the first non-zero Neumann eigenvalue of `-d²/dy²` on `(0, b)` is `(π/b)²`).
It follows from the Dirichlet bound `Beams.wirtinger_deriv` applied to the primitive
`v(y) = ∫₀ʸ u`, which vanishes at both ends. [HardyLittlewoodPolya1952], §7.7. -/
theorem wirtinger_mean_zero {b : ℝ} (hb : 0 < b) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : ∫ y in (0 : ℝ)..b, u y = 0) :
    (π / b) ^ 2 * ∫ y in (0 : ℝ)..b, u y ^ 2 ≤ ∫ y in (0 : ℝ)..b, deriv u y ^ 2 := by
  have hd : deriv (Strings.primitive u) = u :=
    funext fun y => (Strings.hasDerivAt_primitive hu.continuous y).deriv
  have h := Beams.wirtinger_deriv hb (Strings.contDiff_primitive hu)
    (by simp [Strings.primitive]) hmean
  rwa [hd] at h

/-! ### Energy decay -/

section Energy

variable {μ b L : ℝ} {w : ℝ → ℝ → ℝ}

/-- The **strain energy per unit length** at the section `x`:
`S(x) = (μ/2) ∫₀ᵇ (w_x² + w_y²) dy`. -/
def sectionEnergy (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ / 2 * ∫ y in (0 : ℝ)..b, (dt w x y ^ 2 + dx w x y ^ 2)

/-- The **strain energy stored beyond the section `x`** in the finite strip `[0, L] × [0, b]`:
`E(x) = ∫ₓᴸ S(s) ds = (μ/2) ∫ₓᴸ ∫₀ᵇ |∇w|²`. -/
def energy (μ b L : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in x..L, sectionEnergy μ b w s

/-- The **work of the section traction** `W(x) = ∫₀ᵇ τ_xz w dy = μ ∫₀ᵇ w w_x dy`. -/
def sectionWork (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ * ∫ y in (0 : ℝ)..b, w x y * dt w x y

/-- The sectional energy of a `C²` field is continuous in `x`. -/
theorem continuous_sectionEnergy (hU : ContDiff ℝ 2 (Function.uncurry w)) :
    Continuous (sectionEnergy μ b w) := by
  have hA := (Strings.contDiff_dirDeriv hU (1, 0)).continuous
  have hB := (Strings.contDiff_dirDeriv hU (0, 1)).continuous
  have e : Function.uncurry (fun x y => dt w x y ^ 2 + dx w x y ^ 2) = fun p =>
      Strings.dirDeriv (Function.uncurry w) (1, 0) p ^ 2 +
        Strings.dirDeriv (Function.uncurry w) (0, 1) p ^ 2 := by
    funext p
    simp only [Strings.dt_eq_dirDeriv hU, Strings.dx_eq_dirDeriv hU]
    rfl
  have hc : Continuous (Function.uncurry (fun x y => dt w x y ^ 2 + dx w x y ^ 2)) := by
    rw [e]
    exact (hA.pow 2).add (hB.pow 2)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 b)

/-- **Clapeyron's identity on a section**: for a `C²` field harmonic on the section `x` with
traction-free lateral sides, `d/dx ∫₀ᵇ w w_x dy = ∫₀ᵇ (w_x² + w_y²) dy`
(`(w w_x)_x = w_x² + w w_xx = w_x² - w w_yy`, and `∫ w w_yy = [w w_y]₀ᵇ - ∫ w_y²`). -/
theorem hasDerivAt_integral_mul_dt (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b)
    {x : ℝ} (hh : ∀ y ∈ Icc 0 b, IsHarmonicAt w x y) (h0 : dx w x 0 = 0) (h1 : dx w x b = 0) :
    HasDerivAt (fun s => ∫ y in (0 : ℝ)..b, w s y * dt w s y)
      (∫ y in (0 : ℝ)..b, (dt w x y ^ 2 + dx w x y ^ 2)) x := by
  set W := Function.uncurry w with hWdef
  set A := Strings.dirDeriv W (1, 0) with hAdef
  set B := Strings.dirDeriv W (0, 1) with hBdef
  have hA : ContDiff ℝ 1 A := Strings.contDiff_dirDeriv hU _
  have hB : ContDiff ℝ 1 B := Strings.contDiff_dirDeriv hU _
  have dW : Differentiable ℝ W := hU.differentiable (by norm_num)
  have dA := hA.differentiable one_ne_zero
  have dB := hB.differentiable one_ne_zero
  have cW : Continuous W := hU.continuous
  have cA : Continuous A := hA.continuous
  have cB : Continuous B := hB.continuous
  have cA1 : Continuous fun p => fderiv ℝ A p (1, 0) :=
    (hA.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cB2 : Continuous fun p => fderiv ℝ B p (0, 1) :=
    (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have eA : ∀ s y, dt w s y = A (s, y) := fun s y => by rw [Strings.dt_eq_dirDeriv hU]
  have eB : ∀ s y, dx w s y = B (s, y) := fun s y => by rw [Strings.dx_eq_dirDeriv hU]
  have e : (fun s => ∫ y in (0 : ℝ)..b, w s y * dt w s y) =
      fun s => ∫ y in (0 : ℝ)..b, W (s, y) * A (s, y) := by
    funext s
    simp only [eA]
    rfl
  have hd := hasDerivAt_integral_section (G := fun p => W p * A p)
    (G' := fun p => A p * A p + W p * fderiv ℝ A p (1, 0)) (cW.mul cA)
    ((cA.mul cA).add (cW.mul cA1))
    (fun s y => (Strings.hasDerivAt_fst_of_differentiable dW s y).mul
      (Strings.hasDerivAt_fst_of_differentiable dA s y)) b x
  rw [e]
  refine hd.congr_deriv ?_
  have hc : ∫ y in (0 : ℝ)..b, (A (x, y) * A (x, y) + W (x, y) * fderiv ℝ A (x, y) (1, 0)) =
      ∫ y in (0 : ℝ)..b, ((A (x, y) ^ 2 + B (x, y) ^ 2) -
        (B (x, y) * B (x, y) + W (x, y) * fderiv ℝ B (x, y) (0, 1))) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hb] at hy
    have h := hh y hy
    have e1 : dt (dt w) x y = fderiv ℝ A (x, y) (1, 0) := Strings.dt_dt_eq hU x y
    have e2 : dx (dx w) x y = fderiv ℝ B (x, y) (0, 1) := Strings.dx_dx_eq hU x y
    rw [IsHarmonicAt, e1, e2] at h
    have h' : fderiv ℝ A (x, y) (1, 0) = -fderiv ℝ B (x, y) (0, 1) := by linarith
    simp only [h']
    ring
  have hflux : ∀ y, HasDerivAt (fun y => W (x, y) * B (x, y))
      (B (x, y) * B (x, y) + W (x, y) * fderiv ℝ B (x, y) (0, 1)) y := fun y =>
    (Strings.hasDerivAt_snd_of_differentiable dW x y).mul
      (Strings.hasDerivAt_snd_of_differentiable dB x y)
  have i1 : IntervalIntegrable (fun y => A (x, y) ^ 2 + B (x, y) ^ 2) volume 0 b :=
    (((cA.comp (Continuous.prodMk_right x)).pow 2).add
      ((cB.comp (Continuous.prodMk_right x)).pow 2)).intervalIntegrable 0 b
  have i2 : IntervalIntegrable (fun y => B (x, y) * B (x, y) + W (x, y) *
      fderiv ℝ B (x, y) (0, 1)) volume 0 b :=
    (((cB.comp (Continuous.prodMk_right x)).mul (cB.comp (Continuous.prodMk_right x))).add
      ((cW.comp (Continuous.prodMk_right x)).mul
        (cB2.comp (Continuous.prodMk_right x)))).intervalIntegrable 0 b
  have hB0 : B (x, 0) = 0 := (eB x 0).symm.trans h0
  have hB1 : B (x, b) = 0 := (eB x b).symm.trans h1
  rw [hc, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hflux y) i2, hB0, hB1]
  simp only [mul_zero, sub_zero]
  exact intervalIntegral.integral_congr fun y _ => by simp only [eA, eB]

/-- `W'(x) = 2 S(x)`: the derivative of the section work is twice the sectional energy. -/
theorem hasDerivAt_sectionWork (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b)
    {x : ℝ} (hh : ∀ y ∈ Icc 0 b, IsHarmonicAt w x y) (h0 : dx w x 0 = 0) (h1 : dx w x b = 0) :
    HasDerivAt (sectionWork μ b w) (2 * sectionEnergy μ b w x) x := by
  have h := (hasDerivAt_integral_mul_dt hU hb hh h0 h1).const_mul μ
  exact h.congr_deriv (by unfold sectionEnergy; ring)

/-- **Clapeyron's theorem for the far part of the strip**: if `w` is harmonic on
`[0, L] × [0, b]` with traction-free lateral sides, then for `x ∈ [0, L]`,
`E(x) = (W(L) - W(x)) / 2`. -/
theorem energy_eq_sub (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b)
    (hh : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 b, IsHarmonicAt w x y)
    (h0 : ∀ x ∈ Icc 0 L, dx w x 0 = 0) (h1 : ∀ x ∈ Icc 0 L, dx w x b = 0) {x : ℝ}
    (hx : x ∈ Icc 0 L) :
    energy μ b L w x = (sectionWork μ b w L - sectionWork μ b w x) / 2 := by
  have hd : ∀ s ∈ uIcc x L, HasDerivAt (fun s => sectionWork μ b w s / 2)
      (sectionEnergy μ b w s) s := by
    intro s hs
    rw [uIcc_of_le hx.2] at hs
    have hs' : s ∈ Icc 0 L := ⟨hx.1.trans hs.1, hs.2⟩
    convert (hasDerivAt_sectionWork hU hb (hh s hs') (h0 s hs') (h1 s hs')).div_const 2
      using 1
    ring
  rw [energy, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_sectionEnergy hU).intervalIntegrable x L)]
  ring

/-- With a far end that does no work (`W(L) = 0`), `E(x) = -W(x)/2 = -(μ/2) ∫₀ᵇ w w_x`. -/
theorem energy_eq (hU : ContDiff ℝ 2 (Function.uncurry w)) (hb : 0 ≤ b)
    (hh : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 b, IsHarmonicAt w x y)
    (h0 : ∀ x ∈ Icc 0 L, dx w x 0 = 0) (h1 : ∀ x ∈ Icc 0 L, dx w x b = 0)
    (hfar : sectionWork μ b w L = 0) {x : ℝ} (hx : x ∈ Icc 0 L) :
    energy μ b L w x = -sectionWork μ b w x / 2 := by
  rw [energy_eq_sub hU hb hh h0 h1 hx, hfar, zero_sub]

/-- A **clamped far end** (`w(L, ·) = 0`) does no work. -/
theorem sectionWork_eq_zero_of_clamped (h : ∀ y, w L y = 0) : sectionWork μ b w L = 0 := by
  simp [sectionWork, h]

/-- A **traction-free far end** (`w_x(L, ·) = 0`) does no work. -/
theorem sectionWork_eq_zero_of_free (h : ∀ y, dt w L y = 0) : sectionWork μ b w L = 0 := by
  simp [sectionWork, h]

/-- `E'(x) = -S(x)`: the energy beyond `x` decreases at the rate of the sectional energy. -/
theorem hasDerivAt_energy (hU : ContDiff ℝ 2 (Function.uncurry w)) (x : ℝ) :
    HasDerivAt (energy μ b L w) (-sectionEnergy μ b w x) x := by
  have hc := continuous_sectionEnergy (μ := μ) (b := b) hU
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

/-- The energy beyond `x ≤ L` is non-negative (for `μ ≥ 0`). -/
theorem energy_nonneg (hμ : 0 ≤ μ) (hb : 0 ≤ b) {x : ℝ} (hx : x ≤ L) :
    0 ≤ energy μ b L w x :=
  intervalIntegral.integral_nonneg hx fun _ _ => mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg hb fun _ _ => by positivity)

/-- **The cross-sectional estimate**: on a self-equilibrated section (`∫₀ᵇ w_x = 0`),
`|∫₀ᵇ w w_x| ≤ (b/2π) ∫₀ᵇ (w_x² + w_y²)`. Since `∫ w_x = 0` we may subtract the section mean
`w̄` from `w`; then AM–GM `|p q| ≤ (π/2b) p² + (b/2π) q²` and the zero-mean Wirtinger
inequality `∫ (w - w̄)² ≤ (b/π)² ∫ w_y²` give the bound. -/
theorem abs_integral_mul_dt_le (hb : 0 < b) (hU : ContDiff ℝ 2 (Function.uncurry w)) {x : ℝ}
    (heq : ∫ y in (0 : ℝ)..b, dt w x y = 0) :
    |∫ y in (0 : ℝ)..b, w x y * dt w x y| ≤
      b / (2 * π) * ∫ y in (0 : ℝ)..b, (dt w x y ^ 2 + dx w x y ^ 2) := by
  have hwx : ContDiff ℝ 2 (w x) := hU.comp (contDiff_const.prodMk contDiff_id)
  have ca : Continuous fun y => dt w x y := by
    have e : (fun y => dt w x y) = fun y => Strings.dirDeriv (Function.uncurry w) (1, 0) (x, y) :=
      by rw [Strings.dt_eq_dirDeriv hU]
    rw [e]
    exact (Strings.contDiff_dirDeriv hU _).continuous.comp (Continuous.prodMk_right x)
  have cb : Continuous fun y => dx w x y := hwx.continuous_deriv (by norm_num)
  have cw : Continuous (w x) := hwx.continuous
  set c := (∫ y in (0 : ℝ)..b, w x y) / b with hc
  set u : ℝ → ℝ := fun y => w x y - c with hu
  have cu : Continuous u := cw.sub continuous_const
  have hu1 : ContDiff ℝ 1 u := (hwx.of_le one_le_two).sub contDiff_const
  have hmean : ∫ y in (0 : ℝ)..b, u y = 0 := by
    rw [hu, intervalIntegral.integral_sub (cw.intervalIntegrable 0 b) intervalIntegrable_const,
      intervalIntegral.integral_const, hc]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  have hdu : ∀ y, deriv u y = dx w x y := fun y => deriv_sub_const (f := w x) c
  have hW := wirtinger_mean_zero hb hu1 hmean
  simp only [hdu] at hW
  -- subtract the mean
  have hshift : ∫ y in (0 : ℝ)..b, w x y * dt w x y = ∫ y in (0 : ℝ)..b, u y * dt w x y := by
    have e : ∫ y in (0 : ℝ)..b, u y * dt w x y =
        ∫ y in (0 : ℝ)..b, (w x y * dt w x y - c * dt w x y) :=
      intervalIntegral.integral_congr fun y _ => by simp only [hu]; ring
    rw [e, intervalIntegral.integral_sub (f := fun y => w x y * dt w x y)
      (g := fun y => c * dt w x y) ((cw.mul ca).intervalIntegrable 0 b)
      ((continuous_const.mul ca).intervalIntegrable 0 b), intervalIntegral.integral_const_mul,
      heq, mul_zero, sub_zero]
  -- AM–GM
  set α := π / b with hα
  set β := b / π with hβ
  have hαp : 0 < α := by positivity
  have hβp : 0 < β := by positivity
  have hαβ : α * β = 1 := by rw [hα, hβ]; field_simp
  have i1 : IntervalIntegrable (fun y => |u y * dt w x y|) volume 0 b :=
    ((cu.mul ca).abs).intervalIntegrable 0 b
  have iu : IntervalIntegrable (fun y => α / 2 * u y ^ 2) volume 0 b :=
    (continuous_const.mul (cu.pow 2)).intervalIntegrable 0 b
  have ia : IntervalIntegrable (fun y => β / 2 * dt w x y ^ 2) volume 0 b :=
    (continuous_const.mul (ca.pow 2)).intervalIntegrable 0 b
  have hpt : ∫ y in (0 : ℝ)..b, |u y * dt w x y| ≤
      ∫ y in (0 : ℝ)..b, (α / 2 * u y ^ 2 + β / 2 * dt w x y ^ 2) := by
    refine intervalIntegral.integral_mono_on hb.le i1 (iu.add ia) fun y _ => ?_
    have := mul_nonneg hβp.le (sq_nonneg (α * |u y| - |dt w x y|))
    rw [abs_mul]
    nlinarith [sq_abs (u y), sq_abs (dt w x y)]
  rw [intervalIntegral.integral_add iu ia, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hpt
  have hsplit : ∫ y in (0 : ℝ)..b, (dt w x y ^ 2 + dx w x y ^ 2) =
      (∫ y in (0 : ℝ)..b, dt w x y ^ 2) + ∫ y in (0 : ℝ)..b, dx w x y ^ 2 :=
    intervalIntegral.integral_add ((ca.pow 2).intervalIntegrable 0 b)
      ((cb.pow 2).intervalIntegrable 0 b)
  have hαsq : α * ∫ y in (0 : ℝ)..b, u y ^ 2 ≤ β * ∫ y in (0 : ℝ)..b, dx w x y ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left hW hβp.le
    have : β * (α ^ 2 * ∫ y in (0 : ℝ)..b, u y ^ 2) = α * ∫ y in (0 : ℝ)..b, u y ^ 2 := by
      rw [← mul_assoc, sq, ← mul_assoc, mul_comm β α, hαβ, one_mul]
    linarith
  have hb2 : b / (2 * π) = β / 2 := by rw [hβ]; ring
  rw [hshift, hsplit, hb2]
  calc |∫ y in (0 : ℝ)..b, u y * dt w x y|
      ≤ ∫ y in (0 : ℝ)..b, |u y * dt w x y| :=
        intervalIntegral.abs_integral_le_integral_abs hb.le
    _ ≤ _ := hpt
    _ ≤ _ := by nlinarith

/-- **Saint-Venant's principle for antiplane shear** (Horgan–Knowles energy decay). Let `w` be a
`C²` field, harmonic on the strip `[0, L] × [0, b]`, with traction-free lateral sides
`w_y(x, 0) = w_y(x, b) = 0`, loaded at `x = 0` by a **self-equilibrated** traction (zero
resultant `F(0) = 0`), and whose far end `x = L` does no work (`∫₀ᵇ w w_x (L, y) dy = 0`, e.g.
clamped or traction-free). Then the strain energy beyond the section `x` decays exponentially:
`E(x) ≤ E(0) e^{-2πx/b}` for `x ∈ [0, L]`. [HorganKnowles1983], §2; [Knowles1966]. -/
theorem energy_le_exp (hμ : 0 < μ) (hb : 0 < b) (hU : ContDiff ℝ 2 (Function.uncurry w))
    (hh : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 b, IsHarmonicAt w x y)
    (h0 : ∀ x ∈ Icc 0 L, dx w x 0 = 0) (h1 : ∀ x ∈ Icc 0 L, dx w x b = 0)
    (hself : resultant μ b w 0 = 0) (hfar : sectionWork μ b w L = 0) {x : ℝ}
    (hx : x ∈ Icc 0 L) :
    energy μ b L w x ≤ energy μ b L w 0 * exp (-(2 * π / b) * x) := by
  set l := 2 * π / b with hl
  have hlp : 0 < l := by positivity
  -- every section is self-equilibrated
  have hsec : ∀ s ∈ Icc 0 L, ∫ y in (0 : ℝ)..b, dt w s y = 0 := by
    intro s hs
    have h := (resultant_eq_on (μ := μ) hU hb.le hh h0 h1 s hs).trans hself
    exact (mul_eq_zero.1 h).resolve_left hμ.ne'
  -- the differential inequality `l E ≤ S = -E'`
  have hineq : ∀ s ∈ Icc 0 L, l * energy μ b L w s ≤ sectionEnergy μ b w s := by
    intro s hs
    have hest := abs_integral_mul_dt_le hb hU (hsec s hs)
    rw [energy_eq hU hb.le hh h0 h1 hfar hs, sectionWork, sectionEnergy]
    have hneg := neg_le_abs (∫ y in (0 : ℝ)..b, w s y * dt w s y)
    have key : l * (-(μ * ∫ y in (0 : ℝ)..b, w s y * dt w s y) / 2) =
        μ / 2 * (l * -∫ y in (0 : ℝ)..b, w s y * dt w s y) := by ring
    rw [key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlb : l * (b / (2 * π)) = 1 := by rw [hl]; field_simp
    calc l * -∫ y in (0 : ℝ)..b, w s y * dt w s y
        ≤ l * (b / (2 * π) * ∫ y in (0 : ℝ)..b, (dt w s y ^ 2 + dx w s y ^ 2)) :=
          mul_le_mul_of_nonneg_left (hneg.trans hest) hlp.le
      _ = _ := by rw [← mul_assoc, hlb, one_mul]
  -- Grönwall
  set F : ℝ → ℝ := fun s => energy μ b L w s * exp (l * s) with hF
  have hd : ∀ s, HasDerivAt F
      (-sectionEnergy μ b w s * exp (l * s) + energy μ b L w s * (exp (l * s) * l)) s := by
    intro s
    have h1' : HasDerivAt (fun s => l * s) l s := by
      simpa using (hasDerivAt_id' s).const_mul l
    exact (hasDerivAt_energy hU s).mul h1'.exp
  have hmono : AntitoneOn F (Icc 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [(hd s).deriv]
    have hs' : s ∈ Icc 0 L := interior_subset hs
    have hep := exp_pos (l * s)
    nlinarith [hineq s hs', mul_le_mul_of_nonneg_left (hineq s hs') hep.le]
  have h := hmono ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
  simp only [hF, mul_zero, exp_zero, mul_one] at h
  have h2 := mul_le_mul_of_nonneg_right h (exp_pos (-l * x)).le
  rwa [mul_assoc, ← exp_add, show l * x + -l * x = 0 by ring, exp_zero, mul_one] at h2

end Energy

end ContinuumMechanics.SaintVenant
