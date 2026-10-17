import ContinuumMechanics.Beams.String
import ContinuumMechanics.Beams.Wirtinger

/-!
# Heat conduction in a rod: the one-dimensional heat equation

The temperature `u(t, x)` of a thin homogeneous rod `0 ≤ x ≤ L` with thermal conductivity `k`,
density `ρ` and specific heat `c` obeys the balance of energy `ρ c u_t = -∂ₓ q` together with
**Fourier's law** `q = -k u_x`, i.e. the **heat equation** `u_t = κ u_xx` with thermal diffusivity
`κ = k / (ρ c)` ([Strauss2008], §1.3, §2.3; [Evans2010], §2.3). We take Dirichlet ends
`u(t, 0) = u(t, L) = 0`. Fields are functions `u : ℝ → ℝ → ℝ` of time and position, and the
partial derivatives `dt`, `dx` are those of `ContinuumMechanics.Strings`.

## Main definitions

* `Heat.IsHeat κ u`: the heat equation `∂ₜu = κ ∂ₓ²u`.
* `Heat.diffusivity k ρ c = k / (ρ c)` and `Heat.heatFlux k u = -k u_x` (Fourier's law).
* `Heat.mode L κ n a`: the separated solution `a e^{-κ(nπ/L)² t} sin(nπx/L)`;
  `Heat.modeSum`: finite superpositions.
* `Heat.energy L u`: `E(t) = ½ ∫₀ᴸ u² dx`.
* `Heat.steady T₀ T_L L`: the linear steady profile `T₀ + (T_L - T₀) x / L`.

## Main results

* `isHeat_iff_conservation`: `u_t = κ u_xx` with `κ = k/(ρc)` iff `ρ c u_t = -∂ₓ q`, `q = -k u_x`.
* `isHeat_mode`, `mode_boundary`, `isHeat_modeSum`, `modeSum_boundary`: separated solutions and
  their finite superpositions solve the Dirichlet problem; `isHeat_sum` (superposition).
* `abs_mode_le`, `tendsto_mode`, `energy_mode`: each mode decays like `e^{-κ(nπ/L)² t}`.
* `hasDerivAt_energy`: `E'(t) = -κ ∫₀ᴸ u_x²` for `C²` solutions with Dirichlet ends
  (differentiation under the integral and integration by parts); `energy_antitoneOn`: `E` is
  antitone on `[0, ∞)`.
* `eq_zero_of_zero_data`, `unique`: **uniqueness forward in time** for the initial–boundary value
  problem.
* `energy_le_exp`: **exponential decay** `E(t) ≤ E(0) e^{-2κ(π/L)² t}` (Wirtinger's inequality and
  a Grönwall argument).
* `isHeat_steady`, `steady_boundary`, `heatFlux_steady`: the linear steady state with fixed end
  temperatures and its constant heat flux; `energy_sub_steady_le_exp`: every solution with
  these end temperatures converges exponentially to it in `L²`.

## References

* [Strauss2008] W. A. Strauss, *Partial Differential Equations: An Introduction*, 2nd ed.,
  §1.3, §2.3, §4.1.
* [Evans2010] L. C. Evans, *Partial Differential Equations*, §2.3.
* [Carslaw1959] H. S. Carslaw, J. C. Jaeger, *Conduction of Heat in Solids*, 2nd ed., Ch. I, III.
-/

open Set Real MeasureTheory Filter Topology
open ContinuumMechanics.Strings (dt dx)

noncomputable section

namespace ContinuumMechanics.Heat

/-- The **one-dimensional heat equation** `∂ₜu = κ ∂ₓ²u`, at every time and position. -/
def IsHeat (κ : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt u t x = κ * dx (dx u) t x

/-! ### Fourier's law -/

section Fourier

/-- The **thermal diffusivity** `κ = k / (ρ c)` of a material with conductivity `k`, density `ρ`
and specific heat `c`. -/
def diffusivity (k ρ c : ℝ) : ℝ := k / (ρ * c)

/-- **Fourier's law**: the heat flux `q = -k u_x` down the temperature gradient. -/
def heatFlux (k : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := -k * dx u t x

/-- The divergence of the Fourier flux: `∂ₓq = -k u_xx`. -/
theorem dx_heatFlux (k : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) :
    dx (heatFlux k u) t x = -k * dx (dx u) t x :=
  deriv_const_mul_field (-k)

/-- **Heat equation from energy balance**: with `κ = k/(ρc)`, `u_t = κ u_xx` holds iff the local
energy balance `ρ c u_t = -∂ₓ q` holds for the Fourier flux `q = -k u_x`. -/
theorem isHeat_iff_conservation {k ρ c : ℝ} (hρ : ρ ≠ 0) (hc : c ≠ 0) (u : ℝ → ℝ → ℝ) :
    IsHeat (diffusivity k ρ c) u ↔ ∀ t x, ρ * c * dt u t x = -dx (heatFlux k u) t x := by
  have hρc : ρ * c ≠ 0 := mul_ne_zero hρ hc
  refine forall₂_congr fun t x => ?_
  rw [dx_heatFlux, diffusivity, neg_mul, neg_neg]
  constructor <;> intro h
  · rw [h]; field_simp
  · rw [div_mul_eq_mul_div, eq_div_iff hρc, mul_comm, h]

end Fourier

/-! ### Superposition and separated solutions -/

section Superposition

variable {ι : Type*}

/-- **Superposition principle**: a finite sum of (sufficiently differentiable) solutions of the
heat equation is a solution. -/
theorem isHeat_sum {κ : ℝ} (s : Finset ι) (u : ι → ℝ → ℝ → ℝ)
    (ht : ∀ i t x, DifferentiableAt ℝ (fun s => u i s x) t)
    (hx : ∀ i t x, DifferentiableAt ℝ (u i t) x) (hxx : ∀ i t x, DifferentiableAt ℝ (dx (u i) t) x)
    (hw : ∀ i ∈ s, IsHeat κ (u i)) : IsHeat κ (fun t x => ∑ i ∈ s, u i t x) := by
  intro t x
  rw [Strings.dt_sum s u ht, Strings.dx_sum s u hx, Strings.dx_sum s (fun i => dx (u i)) hxx,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => hw i hi t x

end Superposition

section Modes

variable (L κ : ℝ)

/-- Decay rate of the `n`-th mode: `κ (nπ/L)²`. -/
def rate (n : ℕ) : ℝ := κ * (n * π / L) ^ 2

/-- The `n`-th **separated solution** of the heat equation on `[0, L]` with Dirichlet ends:
`uₙ(t, x) = a e^{-κ(nπ/L)² t} sin(nπx/L)`. -/
def mode (n : ℕ) (a t x : ℝ) : ℝ := a * exp (-rate L κ n * t) * sin (n * π / L * x)

/-- Time derivative of a mode: `∂ₜuₙ = -κ(nπ/L)² uₙ`. -/
theorem hasDerivAt_mode_t (n : ℕ) (a t x : ℝ) :
    HasDerivAt (fun s => mode L κ n a s x) (-rate L κ n * mode L κ n a t x) t := by
  have h1 : HasDerivAt (fun s => -rate L κ n * s) (-rate L κ n) t := by
    simpa using (hasDerivAt_id' t).const_mul (-rate L κ n)
  refine ((h1.exp.const_mul a).mul_const (sin (n * π / L * x))).congr_deriv ?_
  simp only [mode]
  ring

/-- Space derivative of a mode. -/
theorem hasDerivAt_mode_x (n : ℕ) (a t x : ℝ) :
    HasDerivAt (mode L κ n a t)
      (a * exp (-rate L κ n * t) * (n * π / L * cos (n * π / L * x))) x := by
  have h1 : HasDerivAt (fun y => n * π / L * y) (n * π / L) x := by
    simpa using (hasDerivAt_id' x).const_mul (n * π / L)
  refine (h1.sin.const_mul (a * exp (-rate L κ n * t))).congr_deriv ?_
  ring

/-- The space derivative field of a mode. -/
theorem dx_mode (n : ℕ) (a : ℝ) :
    dx (mode L κ n a) = fun t x => a * exp (-rate L κ n * t) * (n * π / L * cos (n * π / L * x)) :=
  funext fun t => funext fun x => (hasDerivAt_mode_x L κ n a t x).deriv

/-- Second space derivative of a mode. -/
theorem hasDerivAt_dx_mode (n : ℕ) (a t x : ℝ) :
    HasDerivAt (dx (mode L κ n a) t)
      (a * exp (-rate L κ n * t) * (n * π / L * (-sin (n * π / L * x) * (n * π / L)))) x := by
  have h1 : HasDerivAt (fun y => n * π / L * y) (n * π / L) x := by
    simpa using (hasDerivAt_id' x).const_mul (n * π / L)
  rw [dx_mode]
  exact (h1.cos.const_mul (n * π / L)).const_mul (a * exp (-rate L κ n * t))

/-- **Separated solutions solve the heat equation.** -/
theorem isHeat_mode (n : ℕ) (a : ℝ) : IsHeat κ (mode L κ n a) := by
  intro t x
  change deriv (fun s => mode L κ n a s x) t = _
  rw [(hasDerivAt_mode_t L κ n a t x).deriv]
  change _ = κ * deriv (dx (mode L κ n a) t) x
  rw [(hasDerivAt_dx_mode L κ n a t x).deriv]
  simp only [mode, rate]
  ring

/-- **Separated solutions satisfy the Dirichlet conditions** `u(t, 0) = u(t, L) = 0`. -/
theorem mode_boundary {L : ℝ} (hL : L ≠ 0) (n : ℕ) (a t : ℝ) :
    mode L κ n a t 0 = 0 ∧ mode L κ n a t L = 0 := by
  refine ⟨by simp [mode], ?_⟩
  simp only [mode]
  rw [div_mul_cancel₀ _ hL, sin_nat_mul_pi, mul_zero]

/-- The decay rate of the `n`-th mode is positive for `n ≠ 0`, `κ > 0`, `L ≠ 0`. -/
theorem rate_pos {L κ : ℝ} (hL : L ≠ 0) (hκ : 0 < κ) {n : ℕ} (hn : n ≠ 0) : 0 < rate L κ n := by
  have : (n : ℝ) * π / L ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast hn) pi_ne_zero) hL
  exact mul_pos hκ (pow_pos (abs_pos.2 this) 2 |>.trans_eq (sq_abs _))

/-- **Exponential decay of a mode**: `|uₙ(t, x)| ≤ |a| e^{-κ(nπ/L)² t}`. -/
theorem abs_mode_le (n : ℕ) (a t x : ℝ) :
    |mode L κ n a t x| ≤ |a| * exp (-rate L κ n * t) := by
  rw [mode, abs_mul, abs_mul, abs_exp]
  exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)

/-- Each mode with `n ≠ 0` tends to zero as `t → ∞` (for `κ > 0`). -/
theorem tendsto_mode {L κ : ℝ} (hL : L ≠ 0) (hκ : 0 < κ) {n : ℕ} (hn : n ≠ 0) (a x : ℝ) :
    Tendsto (fun t => mode L κ n a t x) atTop (𝓝 0) := by
  have h := ((tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
    (neg_neg_of_pos (rate_pos hL hκ hn)))).const_mul a).mul_const (sin (n * π / L * x))
  simpa [mode] using h

/-- **Energy** of a temperature field on `[0, L]`: `E(t) = ½ ∫₀ᴸ u² dx`. -/
def energy (L : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := 1 / 2 * ∫ x in (0 : ℝ)..L, u t x ^ 2

/-- The energy of the `n`-th mode, `n ≠ 0`: `E(t) = (a² L / 4) e^{-2κ(nπ/L)² t}`
(orthogonality relation `∫₀ᴸ sin² (nπx/L) = L/2`). -/
theorem energy_mode {L : ℝ} (hL : L ≠ 0) {n : ℕ} (hn : n ≠ 0) (a t : ℝ) :
    energy L (mode L κ n a) t = a ^ 2 * L / 4 * exp (-(2 * rate L κ n) * t) := by
  have e : ∀ x, mode L κ n a t x ^ 2 =
      (a * exp (-rate L κ n * t)) ^ 2 * (sin (n * π / L * x) * sin (n * π / L * x)) :=
    fun x => by simp only [mode]; ring
  simp only [energy, e, intervalIntegral.integral_const_mul,
    Strings.integral_sin_mul_sin hL hn, ite_true]
  rw [mul_pow, sq (exp _), ← exp_add]
  ring_nf

/-- A finite superposition `∑ₙ aₙ e^{-κ(nπ/L)² t} sin(nπx/L)` of separated solutions. -/
def modeSum (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) : ℝ := ∑ n ∈ s, mode L κ n (a n) t x

/-- **Finite superpositions of separated solutions solve the heat equation.** -/
theorem isHeat_modeSum (s : Finset ℕ) (a : ℕ → ℝ) : IsHeat κ (modeSum L κ s a) :=
  isHeat_sum s (fun n => mode L κ n (a n))
    (fun n t x => (hasDerivAt_mode_t L κ n (a n) t x).differentiableAt)
    (fun n t x => (hasDerivAt_mode_x L κ n (a n) t x).differentiableAt)
    (fun n t x => (hasDerivAt_dx_mode L κ n (a n) t x).differentiableAt)
    fun n _ => isHeat_mode L κ n (a n)

/-- **Finite superpositions of separated solutions satisfy the Dirichlet conditions.** -/
theorem modeSum_boundary {L : ℝ} (hL : L ≠ 0) (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    modeSum L κ s a t 0 = 0 ∧ modeSum L κ s a t L = 0 :=
  ⟨Finset.sum_eq_zero fun n _ => (mode_boundary κ hL n _ t).1,
    Finset.sum_eq_zero fun n _ => (mode_boundary κ hL n _ t).2⟩

end Modes

/-! ### Energy decay, uniqueness and the exponential decay rate -/

section Energy

variable {κ L : ℝ} {u : ℝ → ℝ → ℝ}

/-- **Energy dissipation**: for a `C²` field satisfying the heat equation at time `t` with
Dirichlet ends, `E'(t) = -κ ∫₀ᴸ u_x² dx`. -/
theorem hasDerivAt_energy (hU : ContDiff ℝ 2 (Function.uncurry u)) {t : ℝ}
    (hw : ∀ x, dt u t x = κ * dx (dx u) t x) (h0 : u t 0 = 0) (hL : u t L = 0) :
    HasDerivAt (energy L u) (-κ * ∫ x in (0 : ℝ)..L, dx u t x ^ 2) t := by
  set A := Strings.dirDeriv (Function.uncurry u) (1, 0) with hAdef
  set B := Strings.dirDeriv (Function.uncurry u) (0, 1) with hBdef
  have hA : ContDiff ℝ 1 A := Strings.contDiff_dirDeriv hU _
  have hB : ContDiff ℝ 1 B := Strings.contDiff_dirDeriv hU _
  have dU : Differentiable ℝ (Function.uncurry u) := hU.differentiable (by norm_num)
  have dB := hB.differentiable one_ne_zero
  have cU : Continuous (Function.uncurry u) := hU.continuous
  have cA : Continuous A := hA.continuous
  have cB : Continuous B := hB.continuous
  have cB2 : Continuous fun p => fderiv ℝ B p (0, 1) :=
    (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set Fp : ℝ × ℝ → ℝ := fun p => Function.uncurry u p ^ 2 with hFp
  set Gp : ℝ × ℝ → ℝ := fun p => 2 * Function.uncurry u p * A p with hGp
  have cF : Continuous Fp := by fun_prop
  have cG : Continuous Gp := by fun_prop
  have hE : energy L u = fun s => 1 / 2 * ∫ x in (0 : ℝ)..L, Fp (s, x) := rfl
  have hFd : ∀ s x, HasDerivAt (fun s => Fp (s, x)) (Gp (s, x)) s := by
    intro s x
    convert (Strings.hasDerivAt_fst_of_differentiable dU s x).pow 2 using 1
    simp only [Gp, A, Strings.dirDeriv]
    ring
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t 1).prod (isCompact_uIcc (a := (0 : ℝ)) (b := L))
    ).exists_bound_of_continuousOn cG.continuousOn
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := L) (F := fun s x => Fp (s, x)) (F' := fun s x => Gp (s, x))
    (x₀ := t) (bound := fun _ => M) (Metric.closedBall_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s =>
      (cF.comp (Continuous.prodMk_right s)).aestronglyMeasurable)
    ((cF.comp (Continuous.prodMk_right t)).intervalIntegrable 0 L)
    (cG.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x hx s hs =>
      hM (s, x) ⟨hs, Set.uIoc_subset_uIcc hx⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun x _ s _ => hFd s x)
  rw [hE]
  refine (hd.2.const_mul (1 / 2)).congr_deriv ?_
  have eA : ∀ y, dt u t y = A (t, y) := fun y => by rw [Strings.dt_eq_dirDeriv hU]
  have eB : ∀ y, dx u t y = B (t, y) := fun y => by rw [Strings.dx_eq_dirDeriv hU]
  have hheat : ∀ x, A (t, x) = κ * fderiv ℝ B (t, x) (0, 1) := fun x => by
    rw [← eA, ← Strings.dx_dx_eq hU]
    exact hw x
  -- integration by parts: `(u u_x)_x = u_x² + u u_xx`
  have hflux : ∀ x, HasDerivAt (fun y => Function.uncurry u (t, y) * B (t, y))
      (B (t, x) ^ 2 + Function.uncurry u (t, x) * fderiv ℝ B (t, x) (0, 1)) x := by
    intro x
    convert (Strings.hasDerivAt_snd_of_differentiable dU t x).mul
      (Strings.hasDerivAt_snd_of_differentiable dB t x) using 1
    simp only [B, Strings.dirDeriv]
    ring
  have i1 : IntervalIntegrable (fun x => B (t, x) ^ 2 + Function.uncurry u (t, x) *
      fderiv ℝ B (t, x) (0, 1)) volume 0 L :=
    (((cB.comp (Continuous.prodMk_right t)).pow 2).add ((cU.comp (Continuous.prodMk_right t)).mul
      (cB2.comp (Continuous.prodMk_right t)))).intervalIntegrable 0 L
  have i2 : IntervalIntegrable (fun x => B (t, x) ^ 2) volume 0 L :=
    ((cB.comp (Continuous.prodMk_right t)).pow 2).intervalIntegrable 0 L
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hflux x) i1
  have hu0 : Function.uncurry u (t, 0) = 0 := h0
  have huL : Function.uncurry u (t, L) = 0 := hL
  rw [hu0, huL, zero_mul, zero_mul, sub_zero] at hparts
  have hI : ∫ x in (0 : ℝ)..L, Gp (t, x) = ∫ x in (0 : ℝ)..L,
      (2 * κ * (B (t, x) ^ 2 + Function.uncurry u (t, x) * fderiv ℝ B (t, x) (0, 1)) -
        2 * κ * B (t, x) ^ 2) :=
    intervalIntegral.integral_congr fun x _ => by
      simp only [Gp, hheat]
      ring
  rw [hI, intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hparts]
  simp only [eB]
  ring

/-- The energy of a `C²` solution of the heat equation with Dirichlet ends is **non-increasing**
on `[0, ∞)` (for `κ ≥ 0`, `L ≥ 0`). -/
theorem energy_antitoneOn (hκ : 0 ≤ κ) (hLpos : 0 ≤ L) (hU : ContDiff ℝ 2 (Function.uncurry u))
    (hw : ∀ t ≥ 0, ∀ x, dt u t x = κ * dx (dx u) t x) (h0 : ∀ t ≥ 0, u t 0 = 0)
    (hL : ∀ t ≥ 0, u t L = 0) : AntitoneOn (energy L u) (Ici 0) := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (energy L u)
      (-κ * ∫ x in (0 : ℝ)..L, dx u t x ^ 2) t :=
    fun t ht => hasDerivAt_energy hU (hw t ht) (h0 t ht) (hL t ht)
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    fun t ht => ?_
  rw [(hd t (interior_subset ht)).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hκ)
    (intervalIntegral.integral_nonneg hLpos fun _ _ => sq_nonneg _)

/-- The energy is non-negative (for `L ≥ 0`). -/
theorem energy_nonneg (hLpos : 0 ≤ L) (t : ℝ) : 0 ≤ energy L u t :=
  mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hLpos fun _ _ => sq_nonneg _)

/-- **Zero data give the zero solution forward in time**: a `C²` solution of the heat equation
on `[0, L]` for `t ≥ 0` with Dirichlet ends and vanishing initial temperature vanishes on
`[0, L]` for all `t ≥ 0`. -/
theorem eq_zero_of_zero_data (hκ : 0 ≤ κ) (hLpos : 0 < L)
    (hU : ContDiff ℝ 2 (Function.uncurry u)) (hw : ∀ t ≥ 0, ∀ x, dt u t x = κ * dx (dx u) t x)
    (h0 : ∀ t ≥ 0, u t 0 = 0) (hL : ∀ t ≥ 0, u t L = 0) (hi : ∀ x ∈ Icc 0 L, u 0 x = 0) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = 0 := by
  intro t ht x hx
  have hE0 : energy L u 0 = 0 := by
    rw [energy, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => by
      rw [uIcc_of_le hLpos.le] at hy
      simp only [hi y hy]
      ring)]
    simp
  have hEt : energy L u t = 0 :=
    le_antisymm (hE0 ▸ energy_antitoneOn hκ hLpos.le hU hw h0 hL (mem_Ici.2 le_rfl) ht ht)
      (energy_nonneg hLpos.le t)
  have hI : ∫ y in (0 : ℝ)..L, u t y ^ 2 = 0 := by
    simp only [energy] at hEt
    linarith
  have cu : Continuous (u t) := hU.continuous.comp (Continuous.prodMk_right t)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => sq_nonneg (u t y))
    ((cu.pow 2).intervalIntegrable 0 L)).1 hI
  rw [Ioc_eq_empty (not_lt.2 hLpos.le), union_empty,
    Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
  have h := Measure.eqOn_Icc_of_ae_eq volume hLpos.ne hae (cu.pow 2).continuousOn
    continuousOn_const hx
  simpa using h

/-- The difference of two `C²` solutions of the heat equation at time `t` is a solution at
time `t` (linearity). -/
theorem heat_sub {v : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v)) {t : ℝ} (hwu : ∀ x, dt u t x = κ * dx (dx u) t x)
    (hwv : ∀ x, dt v t x = κ * dx (dx v) t x) (x : ℝ) :
    dt (fun t x => u t x - v t x) t x = κ * dx (dx fun t x => u t x - v t x) t x := by
  have f1 : dx (fun t x => u t x - v t x) = fun t x => dx u t x - dx v t x :=
    funext fun t => funext fun x =>
      deriv_sub (Strings.differentiableAt_x hu t x) (Strings.differentiableAt_x hv t x)
  have f2 : dx (fun t x => dx u t x - dx v t x) = fun t x => dx (dx u) t x - dx (dx v) t x :=
    funext fun t => funext fun x =>
      deriv_sub (Strings.differentiableAt_dx_x hu t x) (Strings.differentiableAt_dx_x hv t x)
  rw [Strings.dt_sub hu hv, f1, f2]
  simp only [hwu x, hwv x]
  ring

/-- **Uniqueness for the initial–boundary value problem, forward in time**: two `C²` solutions of
`u_t = κ u_xx` (`κ ≥ 0`) on `t ≥ 0` with the same Dirichlet data `u(t, 0) = g₀(t)`,
`u(t, L) = g_L(t)` and the same initial temperature on `[0, L]` coincide on `[0, L]` for all
`t ≥ 0`. -/
theorem unique {v : ℝ → ℝ → ℝ} (hκ : 0 ≤ κ) (hLpos : 0 < L)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hv : ContDiff ℝ 2 (Function.uncurry v))
    (hwu : ∀ t ≥ 0, ∀ x, dt u t x = κ * dx (dx u) t x)
    (hwv : ∀ t ≥ 0, ∀ x, dt v t x = κ * dx (dx v) t x)
    (h0 : ∀ t ≥ 0, u t 0 = v t 0) (hL : ∀ t ≥ 0, u t L = v t L)
    (hi : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = v t x := by
  intro t ht x hx
  have hw : ContDiff ℝ 2 (Function.uncurry fun t x => u t x - v t x) := hu.sub hv
  have h := eq_zero_of_zero_data hκ hLpos hw
    (fun s hs => heat_sub hu hv (hwu s hs) (hwv s hs))
    (fun s hs => sub_eq_zero.2 (h0 s hs)) (fun s hs => sub_eq_zero.2 (hL s hs))
    (fun y hy => sub_eq_zero.2 (hi y hy)) t ht x hx
  exact sub_eq_zero.1 h

/-- **Exponential energy decay** (Poincaré–Wirtinger rate): for a `C²` solution of the heat
equation on `t ≥ 0` with Dirichlet ends, `E(t) ≤ E(0) e^{-2κ(π/L)² t}`. By Wirtinger's
inequality `∫ u_x² ≥ (π/L)² ∫ u²`, `E' ≤ -2κ(π/L)² E`, so `E(t) e^{2κ(π/L)² t}` is
non-increasing. -/
theorem energy_le_exp (hκ : 0 ≤ κ) (hLpos : 0 < L) (hU : ContDiff ℝ 2 (Function.uncurry u))
    (hw : ∀ t ≥ 0, ∀ x, dt u t x = κ * dx (dx u) t x) (h0 : ∀ t ≥ 0, u t 0 = 0)
    (hL : ∀ t ≥ 0, u t L = 0) {t : ℝ} (ht : 0 ≤ t) :
    energy L u t ≤ energy L u 0 * exp (-(2 * κ * (π / L) ^ 2) * t) := by
  set l := 2 * κ * (π / L) ^ 2 with hl
  set F : ℝ → ℝ := fun s => energy L u s * exp (l * s) with hF
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt F
      ((-κ * ∫ x in (0 : ℝ)..L, dx u s x ^ 2) * exp (l * s) +
        energy L u s * (exp (l * s) * l)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => l * s) l s := by
      simpa using (hasDerivAt_id' s).const_mul l
    exact (hasDerivAt_energy hU (hw s hs) (h0 s hs) (hL s hs)).mul h1.exp
  have hmono : AntitoneOn F (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    have hs' : s ∈ Ici (0 : ℝ) := interior_subset hs
    rw [(hd s hs').deriv]
    have hus : ContDiff ℝ 2 (u s) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hW := Beams.wirtinger hLpos (hus.of_le one_le_two) (h0 s hs') (hL s hs')
    have hW' : κ * ((π / L) ^ 2 * ∫ x in (0 : ℝ)..L, u s x ^ 2) ≤
        κ * ∫ x in (0 : ℝ)..L, dx u s x ^ 2 := mul_le_mul_of_nonneg_left hW hκ
    have hep := exp_pos (l * s)
    simp only [energy, hl]
    nlinarith
  have h := hmono (mem_Ici.2 le_rfl) ht ht
  simp only [hF, mul_zero, exp_zero, mul_one] at h
  have h2 := mul_le_mul_of_nonneg_right h (exp_pos (-l * t)).le
  rwa [mul_assoc, ← exp_add, show l * t + -l * t = 0 by ring, exp_zero, mul_one] at h2

end Energy

/-! ### Steady state with prescribed end temperatures -/

section Steady

variable (T₀ T_L L : ℝ)

/-- The **linear steady temperature profile** `u(x) = T₀ + (T_L - T₀) x / L` between end
temperatures `T₀` and `T_L`. -/
def steady (x : ℝ) : ℝ := T₀ + (T_L - T₀) * x / L

/-- Derivative of the steady profile: the constant gradient `(T_L - T₀) / L`. -/
theorem hasDerivAt_steady (x : ℝ) : HasDerivAt (steady T₀ T_L L) ((T_L - T₀) / L) x := by
  convert (((hasDerivAt_id' x).const_mul (T_L - T₀)).div_const L).const_add T₀ using 1
  · rfl
  · ring

/-- The temperature gradient of the steady state is constant. -/
theorem dx_steady :
    dx (fun _ x => steady T₀ T_L L x) = fun _ _ => (T_L - T₀) / L :=
  funext fun _ => funext fun x => (hasDerivAt_steady T₀ T_L L x).deriv

/-- **The steady state solves the heat equation**: `u_t = 0 = κ u_xx`. -/
theorem isHeat_steady (κ : ℝ) : IsHeat κ (fun _ x => steady T₀ T_L L x) := by
  intro t x
  rw [dx_steady]
  simp [dt, dx]

/-- The steady state takes the prescribed end temperatures `u(0) = T₀`, `u(L) = T_L`. -/
theorem steady_boundary {L : ℝ} (hL : L ≠ 0) :
    steady T₀ T_L L 0 = T₀ ∧ steady T₀ T_L L L = T_L := by
  refine ⟨by simp [steady], ?_⟩
  simp only [steady]
  field_simp
  ring

/-- **Constant heat flux** through the rod in the steady state (Fourier's law):
`q = -k u_x = k (T₀ - T_L) / L` at every point and time. -/
theorem heatFlux_steady (k t x : ℝ) :
    heatFlux k (fun _ x => steady T₀ T_L L x) t x = k * (T₀ - T_L) / L := by
  simp only [heatFlux, dx_steady]
  ring

/-- The steady field is smooth. -/
theorem contDiff_steady :
    ContDiff ℝ 2 (Function.uncurry fun (_ : ℝ) x => steady T₀ T_L L x) := by
  change ContDiff ℝ 2 fun p : ℝ × ℝ => T₀ + (T_L - T₀) * p.2 / L
  fun_prop

/-- **Exponential approach to the steady state**: if `u` is a `C²` solution of the heat equation
on `t ≥ 0` (`κ ≥ 0`) with end temperatures `u(t, 0) = T₀`, `u(t, L) = T_L`, then the deviation
`w = u - u_steady` satisfies `E_w(t) ≤ E_w(0) e^{-2κ(π/L)² t}`. -/
theorem energy_sub_steady_le_exp {κ L : ℝ} {u : ℝ → ℝ → ℝ} (hκ : 0 ≤ κ) (hLpos : 0 < L)
    (hU : ContDiff ℝ 2 (Function.uncurry u)) (hw : ∀ t ≥ 0, ∀ x, dt u t x = κ * dx (dx u) t x)
    (h0 : ∀ t ≥ 0, u t 0 = T₀) (hL : ∀ t ≥ 0, u t L = T_L) {t : ℝ} (ht : 0 ≤ t) :
    energy L (fun t x => u t x - steady T₀ T_L L x) t ≤
      energy L (fun t x => u t x - steady T₀ T_L L x) 0 * exp (-(2 * κ * (π / L) ^ 2) * t) := by
  have hb := steady_boundary T₀ T_L hLpos.ne'
  have hW : ContDiff ℝ 2 (Function.uncurry fun t x => u t x - steady T₀ T_L L x) :=
    hU.sub (contDiff_steady T₀ T_L L)
  exact energy_le_exp hκ hLpos hW
    (fun s hs => heat_sub hU (contDiff_steady T₀ T_L L) (hw s hs)
      (fun x => isHeat_steady T₀ T_L L κ s x))
    (fun s hs => by simp [h0 s hs, hb.1]) (fun s hs => by simp [hL s hs, hb.2]) ht

end Steady

end ContinuumMechanics.Heat
