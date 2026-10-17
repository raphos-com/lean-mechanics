import ContinuumMechanics.Thermal.Heat
import Mathlib.NumberTheory.ZetaValues

/-!
# Terzaghi's effective stress principle and one-dimensional consolidation

A saturated soil carries a total stress `σ` partly through the grain skeleton and partly through
the pore water. **Terzaghi's principle** states that the deformation and strength of the soil are
governed by the **effective stress** `σ' = σ - u`, `u` the pore-water pressure
([Terzaghi1943], Ch. II; [Craig2004], §3.1–3.2).

When a load `Δσ` is applied to a saturated clay layer, it is first carried entirely by an
**excess pore pressure** `u`, which then dissipates by seepage towards the drainage boundaries.
Combining Darcy's law `v = -(k/γ_w) u_z` for the seepage velocity with the continuity of the
pore water and the compressibility law `Δε_v = m_v Δσ'` (at constant total stress,
`∂ε_v/∂t = -m_v ∂u/∂t`) gives **Terzaghi's consolidation equation**
`∂u/∂t = c_v ∂²u/∂z²`, `c_v = k / (m_v γ_w)` ([Terzaghi1943], Ch. XIII; [Craig2004], §7.6).
This *is* the one-dimensional heat equation, so the results of `ContinuumMechanics.Heat` (energy
decay, uniqueness, exponential decay) apply verbatim to a doubly drained layer of thickness `2H`.

For a uniform initial excess pressure `u₀` the classical series solution is
`u = Σₘ (2u₀/M) sin(Mz/H) e^{-M² T_v}`, `M = (2m+1)π/2`, with time factor `T_v = c_v t / H²`;
each term vanishes at the drainage boundaries `z = 0`, `z = 2H` and has zero gradient
(impermeable plane of symmetry) at `z = H`. The average **degree of consolidation** is
`U(T_v) = 1 - Σₘ (2/M²) e^{-M² T_v}`; since `Σₘ 1/(2m+1)² = π²/8`, `Σₘ 2/M² = 1`, so `U(0) = 0`,
and `U(T_v) → 1` as `T_v → ∞`, with `1 - U(T_v) ≤ e^{-π² T_v / 4}`.

## Main definitions

* `effectiveStress σ u = σ - u`; `layeredStress γ h n = Σᵢ γᵢ hᵢ`; `totalStress`,
  `porePressure`, `effVertical`: vertical stresses in a deposit with a water table;
  `buoyantWeight γ_sat γ_w = γ_sat - γ_w`.
* `coeffConsolidation k m_v γ_w = k / (m_v γ_w)`, `darcyVelocity k γ_w u = -(k/γ_w) u_z`,
  `IsConsolidation c_v u`: Terzaghi's equation `u_t = c_v u_zz`.
* `modeM m = (2m+1)π/2`, `timeFactor c_v H t = c_v t / H²`, `term u₀ H c_v m`: the `m`-th term of
  Terzaghi's series, `partialSol`: its partial sums.
* `avgPressure H u t = (1/H) ∫₀ᴴ u dz`; `degree n T`, `degreeFull T`: the degree of
  consolidation for the truncated and for the full series.
* `finalSettlement m_v Δσ' D = m_v Δσ' D`, `settlement s_∞ T = U(T) s_∞`.

## Main results

* `effVertical_of_waterTable_le`, `effVertical_sub`: below the water table the effective vertical
  stress grows linearly with depth at the rate `γ' = γ_sat - γ_w`.
* `isConsolidation_iff_continuity`: `u_t = c_v u_zz` with `c_v = k/(m_v γ_w)` iff
  `-m_v u_t = ∂_z v` with Darcy's velocity `v = -(k/γ_w) u_z`.
* `IsConsolidation.energy_antitoneOn`, `IsConsolidation.unique`,
  `IsConsolidation.energy_le_exp`: for a doubly drained layer the excess pore pressure energy
  decays, solutions are unique forward in time, and `E(t) ≤ E(0) e^{-(π²/2) T_v}`.
* `isConsolidation_term`, `term_zero`, `term_two_mul`, `dx_term_self`, `term_two_mul_sub`;
  `isConsolidation_partialSol`, `partialSol_zero`, `partialSol_two_mul`,
  `dx_partialSol_self`: each term and each partial sum solves the consolidation equation,
  drains at `z = 0`, `z = 2H` and is impermeable (symmetric) at `z = H`.
* `avgPressure_partialSol`, `degree_eq`: `U = 1 - ū/u₀ = 1 - Σ (2/M²) e^{-M² T_v}`;
  `degree_monotone`, `tendsto_degree`, `degree_zero`, `one_sub_degree_le`.
* `hasSum_one_div_odd_sq`: `Σ 1/(2m+1)² = π²/8`; `hasSum_two_div_modeM_sq`: `Σ 2/M² = 1`.
* `degreeFull_zero` (`U(0) = 0`), `degreeFull_monotoneOn`, `one_sub_degreeFull_le`,
  `tendsto_degreeFull` (`U(T_v) → 1`), `tendsto_degree_degreeFull`.
* `settlement_zero`, `settlement_le`, `tendsto_settlement`: `s(t) = U s_∞` rises from `0` to
  `s_∞`.

## References

* [Terzaghi1943] K. Terzaghi, *Theoretical Soil Mechanics*, Wiley, 1943, Ch. II, XIII.
* [Craig2004] R. F. Craig, *Craig's Soil Mechanics*, 7th ed., §3, §7.
* [Strauss2008] W. A. Strauss, *Partial Differential Equations: An Introduction*, 2nd ed., §4.1.
-/

open Set Real MeasureTheory Filter Topology
open ContinuumMechanics.Strings (dt dx)

noncomputable section

namespace ContinuumMechanics.Geotechnics

/-! ### Effective stress -/

section EffectiveStress

/-- **Terzaghi's effective stress** `σ' = σ - u`: the part of the total stress `σ` carried by the
soil skeleton when the pore water is at pressure `u`. -/
def effectiveStress (σ u : ℝ) : ℝ := σ - u

/-- The total stress is shared between the skeleton and the pore water: `σ = σ' + u`. -/
theorem total_eq_effectiveStress_add (σ u : ℝ) : σ = effectiveStress σ u + u := by
  simp [effectiveStress]

/-- At constant total stress, a change of pore pressure changes the effective stress by the
opposite amount: `Δσ' = -Δu`. -/
theorem effectiveStress_sub_effectiveStress (σ u₁ u₂ : ℝ) :
    effectiveStress σ u₂ - effectiveStress σ u₁ = -(u₂ - u₁) := by
  simp only [effectiveStress]
  ring

/-- **Total vertical stress at the base of `n` horizontal layers** of unit weights `γᵢ` and
thicknesses `hᵢ`: `σ_v = Σᵢ γᵢ hᵢ`. -/
def layeredStress (γ h : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, γ i * h i

/-- Adding a layer adds its weight per unit area `γₙ hₙ`. -/
theorem layeredStress_succ (γ h : ℕ → ℝ) (n : ℕ) :
    layeredStress γ h (n + 1) = layeredStress γ h n + γ n * h n :=
  Finset.sum_range_succ _ _

/-- The total vertical stress does not decrease with the number of layers (non-negative unit
weights and thicknesses). -/
theorem layeredStress_mono {γ h : ℕ → ℝ} (hγ : ∀ i, 0 ≤ γ i) (hh : ∀ i, 0 ≤ h i) :
    Monotone (layeredStress γ h) :=
  monotone_nat_of_le_succ fun n => by
    rw [layeredStress_succ]
    linarith [mul_nonneg (hγ n) (hh n)]

/-- A homogeneous deposit of `n` layers of thickness `h`: `σ_v = γ (n h)`. -/
theorem layeredStress_const (γ h : ℝ) (n : ℕ) :
    layeredStress (fun _ => γ) (fun _ => h) n = γ * (n * h) := by
  simp only [layeredStress, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

variable (γ γsat γw d : ℝ)

/-- Total vertical stress at depth `z` in a uniform deposit with the water table at depth `d`:
unit weight `γ` above the water table and saturated unit weight `γ_sat` below it. -/
def totalStress (z : ℝ) : ℝ := γ * min z d + γsat * max (z - d) 0

/-- Hydrostatic pore pressure `u = γ_w z_w`, `z_w = max (z - d) 0` the depth below the water
table. -/
def porePressure (z : ℝ) : ℝ := γw * max (z - d) 0

/-- Effective vertical stress `σ'_v = σ_v - γ_w z_w`. -/
def effVertical (z : ℝ) : ℝ := effectiveStress (totalStress γ γsat d z) (porePressure γw d z)

/-- The **submerged (buoyant) unit weight** `γ' = γ_sat - γ_w`. -/
def buoyantWeight : ℝ := γsat - γw

/-- Above the water table there is no pore pressure: `σ'_v = σ_v = γ z`. -/
theorem effVertical_of_le_waterTable {z : ℝ} (hz : z ≤ d) : effVertical γ γsat γw d z = γ * z := by
  simp [effVertical, effectiveStress, totalStress, porePressure, min_eq_left hz,
    max_eq_right (sub_nonpos.2 hz)]

/-- Below the water table, `σ'_v = σ_v - γ_w (z - d)`. -/
theorem effVertical_eq_sub {z : ℝ} (hz : d ≤ z) :
    effVertical γ γsat γw d z = totalStress γ γsat d z - γw * (z - d) := by
  simp [effVertical, effectiveStress, porePressure, max_eq_left (sub_nonneg.2 hz)]

/-- **Effective stress below the water table**: `σ'_v = γ d + γ' (z - d)`. -/
theorem effVertical_of_waterTable_le {z : ℝ} (hz : d ≤ z) :
    effVertical γ γsat γw d z = γ * d + buoyantWeight γsat γw * (z - d) := by
  rw [effVertical_eq_sub _ _ _ _ hz, totalStress, min_eq_right hz,
    max_eq_left (sub_nonneg.2 hz), buoyantWeight]
  ring

/-- Below the water table the effective vertical stress increases linearly with depth at the
rate `γ' = γ_sat - γ_w`. -/
theorem effVertical_sub {z₁ z₂ : ℝ} (h₁ : d ≤ z₁) (h₂ : d ≤ z₂) :
    effVertical γ γsat γw d z₂ - effVertical γ γsat γw d z₁ =
      buoyantWeight γsat γw * (z₂ - z₁) := by
  rw [effVertical_of_waterTable_le _ _ _ _ h₁, effVertical_of_waterTable_le _ _ _ _ h₂]
  ring

/-- For `γ_sat ≥ γ_w` the effective vertical stress is non-decreasing below the water table. -/
theorem effVertical_monotoneOn (h : γw ≤ γsat) : MonotoneOn (effVertical γ γsat γw d) (Ici d) := by
  intro z₁ h₁ z₂ h₂ hz
  have := effVertical_sub γ γsat γw d h₁ h₂
  have hb : 0 ≤ buoyantWeight γsat γw := sub_nonneg.2 h
  nlinarith [mul_nonneg hb (sub_nonneg.2 hz)]

end EffectiveStress

/-! ### Terzaghi's consolidation equation -/

section Equation

/-- The **coefficient of consolidation** `c_v = k / (m_v γ_w)` of a soil with permeability `k`
and coefficient of volume compressibility `m_v`; `γ_w` is the unit weight of water. -/
def coeffConsolidation (k mv γw : ℝ) : ℝ := k / (mv * γw)

/-- **Darcy's law**: the seepage velocity `v = -(k/γ_w) u_z` driven by the excess head `u/γ_w`. -/
def darcyVelocity (k γw : ℝ) (u : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ := -(k / γw) * dx u t z

/-- **Terzaghi's one-dimensional consolidation equation** `∂ₜu = c_v ∂_z²u` for the excess pore
pressure `u(t, z)`; it is the heat equation `Heat.IsHeat c_v u`. -/
def IsConsolidation (cv : ℝ) (u : ℝ → ℝ → ℝ) : Prop := Heat.IsHeat cv u

/-- The consolidation equation is the heat equation with diffusivity `c_v`. -/
theorem isConsolidation_iff_isHeat {cv : ℝ} {u : ℝ → ℝ → ℝ} :
    IsConsolidation cv u ↔ Heat.IsHeat cv u := Iff.rfl

/-- Any solution of the heat equation with diffusivity `c_v` is a consolidation solution. -/
theorem _root_.ContinuumMechanics.Heat.IsHeat.isConsolidation {cv : ℝ} {u : ℝ → ℝ → ℝ}
    (h : Heat.IsHeat cv u) : IsConsolidation cv u := h

/-- The divergence of the Darcy velocity: `v_z = -(k/γ_w) u_zz`. -/
theorem dx_darcyVelocity (k γw : ℝ) (u : ℝ → ℝ → ℝ) (t z : ℝ) :
    dx (darcyVelocity k γw u) t z = -(k / γw) * dx (dx u) t z :=
  deriv_const_mul_field _

/-- **Derivation of the consolidation equation**: with `c_v = k/(m_v γ_w)`, `u_t = c_v u_zz`
holds iff the continuity equation `∂ₜε_v = -m_v ∂ₜu = ∂_z v` holds for the Darcy velocity
`v = -(k/γ_w) u_z` (volumetric compression equals the net outflow of pore water). -/
theorem isConsolidation_iff_continuity {k mv γw : ℝ} (hmv : mv ≠ 0) (hγw : γw ≠ 0)
    (u : ℝ → ℝ → ℝ) :
    IsConsolidation (coeffConsolidation k mv γw) u ↔
      ∀ t z, -(mv * dt u t z) = dx (darcyVelocity k γw u) t z := by
  refine forall₂_congr fun t z => ?_
  rw [dx_darcyVelocity, coeffConsolidation]
  constructor <;> intro h
  · rw [h]
    field_simp
  · field_simp at h
    field_simp
    linarith

end Equation

/-! ### Double drainage: energy decay, uniqueness, exponential decay -/

section DoubleDrainage

variable {cv H : ℝ} {u : ℝ → ℝ → ℝ}

/-- The **time factor** `T_v = c_v t / H²` (`H` the drainage path length). -/
def timeFactor (cv H t : ℝ) : ℝ := cv * t / H ^ 2

/-- **Dissipation of excess pore pressure**: for a `C²` solution in a layer `0 ≤ z ≤ 2H`
drained at both faces, the energy `½ ∫₀^{2H} u²` is non-increasing for `t ≥ 0`. -/
theorem IsConsolidation.energy_antitoneOn (hu : IsConsolidation cv u) (hcv : 0 ≤ cv)
    (hH : 0 ≤ H) (hU : ContDiff ℝ 2 (Function.uncurry u)) (h0 : ∀ t ≥ 0, u t 0 = 0)
    (h2H : ∀ t ≥ 0, u t (2 * H) = 0) : AntitoneOn (Heat.energy (2 * H) u) (Ici 0) :=
  Heat.energy_antitoneOn hcv (by linarith) hU (fun t _ => hu t) h0 h2H

/-- **Uniqueness of consolidation**: two `C²` solutions in a doubly drained layer `[0, 2H]` with
the same initial excess pore pressure coincide for all `t ≥ 0`. -/
theorem IsConsolidation.unique {v : ℝ → ℝ → ℝ} (hu : IsConsolidation cv u)
    (hv : IsConsolidation cv v) (hcv : 0 ≤ cv) (hH : 0 < H)
    (hU : ContDiff ℝ 2 (Function.uncurry u)) (hV : ContDiff ℝ 2 (Function.uncurry v))
    (hu0 : ∀ t ≥ 0, u t 0 = 0) (hu2 : ∀ t ≥ 0, u t (2 * H) = 0) (hv0 : ∀ t ≥ 0, v t 0 = 0)
    (hv2 : ∀ t ≥ 0, v t (2 * H) = 0) (hi : ∀ z ∈ Icc 0 (2 * H), u 0 z = v 0 z) :
    ∀ t ≥ 0, ∀ z ∈ Icc 0 (2 * H), u t z = v t z :=
  Heat.unique hcv (by linarith) hU hV (fun t _ => hu t) (fun t _ => hv t)
    (fun t ht => by rw [hu0 t ht, hv0 t ht]) (fun t ht => by rw [hu2 t ht, hv2 t ht]) hi

/-- **Exponential dissipation rate**: for a `C²` solution in a doubly drained layer `[0, 2H]`,
`E(t) ≤ E(0) e^{-(π²/2) T_v}` with `T_v = c_v t / H²`. -/
theorem IsConsolidation.energy_le_exp (hu : IsConsolidation cv u) (hcv : 0 ≤ cv) (hH : 0 < H)
    (hU : ContDiff ℝ 2 (Function.uncurry u)) (h0 : ∀ t ≥ 0, u t 0 = 0)
    (h2H : ∀ t ≥ 0, u t (2 * H) = 0) {t : ℝ} (ht : 0 ≤ t) :
    Heat.energy (2 * H) u t ≤
      Heat.energy (2 * H) u 0 * exp (-(π ^ 2 / 2) * timeFactor cv H t) := by
  have h := Heat.energy_le_exp hcv (by linarith) hU (fun t _ => hu t) h0 h2H ht
  have e : -(2 * cv * (π / (2 * H)) ^ 2) * t = -(π ^ 2 / 2) * timeFactor cv H t := by
    simp only [timeFactor]
    field_simp
  rwa [e] at h

end DoubleDrainage

/-! ### Terzaghi's series solution -/

section Series

variable (u₀ H cv : ℝ)

/-- The eigenvalues `M = (2m+1)π/2` of Terzaghi's series. -/
def modeM (m : ℕ) : ℝ := (2 * m + 1) * π / 2

/-- The `m`-th **term of Terzaghi's series** for a uniform initial excess pressure `u₀`:
`uₘ(t, z) = (2u₀/M) e^{-M² T_v} sin(Mz/H)`, `M = (2m+1)π/2`, `T_v = c_v t/H²`. -/
def term (m : ℕ) (t z : ℝ) : ℝ :=
  2 * u₀ / modeM m * exp (-modeM m ^ 2 * timeFactor cv H t) * sin (modeM m * z / H)

/-- The eigenvalues are positive. -/
theorem modeM_pos (m : ℕ) : 0 < modeM m := by
  unfold modeM
  positivity

/-- The eigenvalues are at least the first one, `π/2`. -/
theorem pi_div_two_le_modeM (m : ℕ) : π / 2 ≤ modeM m := by
  unfold modeM
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  nlinarith [pi_pos]

/-- `cos M = 0`: the eigenvalues are the zeros of the cosine. -/
theorem cos_modeM (m : ℕ) : cos (modeM m) = 0 :=
  Real.cos_eq_zero_iff.2 ⟨m, by simp [modeM]⟩

/-- Each term of Terzaghi's series is the heat mode `2m+1` on the doubly drained layer `[0, 2H]`.
-/
theorem term_eq_mode (m : ℕ) :
    term u₀ H cv m = Heat.mode (2 * H) cv (2 * m + 1) (2 * u₀ / modeM m) := by
  funext t z
  rcases eq_or_ne H 0 with rfl | hH
  · simp [term, Heat.mode, Heat.rate, timeFactor]
  simp only [term, Heat.mode, Heat.rate, timeFactor, modeM]
  push_cast
  congr 1
  · congr 2
    field_simp
  · congr 1
    field_simp

/-- **Each term solves Terzaghi's consolidation equation.** -/
theorem isConsolidation_term (m : ℕ) : IsConsolidation cv (term u₀ H cv m) := by
  rw [IsConsolidation, term_eq_mode]
  exact Heat.isHeat_mode _ _ _ _

/-- Drainage at the top face: `uₘ(t, 0) = 0`. -/
theorem term_zero (m : ℕ) (t : ℝ) : term u₀ H cv m t 0 = 0 := by
  simp [term]

/-- Drainage at the bottom face of the doubly drained layer: `uₘ(t, 2H) = 0`. -/
theorem term_two_mul {H : ℝ} (hH : H ≠ 0) (m : ℕ) (t : ℝ) : term u₀ H cv m t (2 * H) = 0 := by
  rw [term_eq_mode]
  exact (Heat.mode_boundary cv (mul_ne_zero two_ne_zero hH) _ _ t).2

/-- Space derivative of a term. -/
theorem hasDerivAt_term_z (m : ℕ) (t z : ℝ) :
    HasDerivAt (term u₀ H cv m t) (2 * u₀ / modeM m * exp (-modeM m ^ 2 * timeFactor cv H t) *
      (modeM m / H * cos (modeM m * z / H))) z := by
  have h1 : HasDerivAt (fun y => modeM m * y / H) (modeM m / H) z := by
    simpa using ((hasDerivAt_id' z).const_mul (modeM m)).div_const H
  refine (h1.sin.const_mul (2 * u₀ / modeM m * exp (-modeM m ^ 2 * timeFactor cv H t))).congr_deriv
    ?_
  ring

/-- **Impermeable plane** `z = H` (the mid-plane of the doubly drained layer, or the impermeable
base of a singly drained layer of thickness `H`): `∂_z uₘ(t, H) = 0`. -/
theorem dx_term_self {H : ℝ} (hH : H ≠ 0) (m : ℕ) (t : ℝ) : dx (term u₀ H cv m) t H = 0 := by
  change deriv (term u₀ H cv m t) H = 0
  rw [(hasDerivAt_term_z u₀ H cv m t H).deriv, mul_div_cancel_right₀ _ hH, cos_modeM]
  simp

/-- **Symmetry about the mid-plane**: `uₘ(t, 2H - z) = uₘ(t, z)`. -/
theorem term_two_mul_sub {H : ℝ} (hH : H ≠ 0) (m : ℕ) (t z : ℝ) :
    term u₀ H cv m t (2 * H - z) = term u₀ H cv m t z := by
  have e : modeM m * (2 * H - z) / H = ((2 * m + 1 : ℕ) : ℝ) * π - modeM m * z / H := by
    simp only [modeM]
    push_cast
    field_simp
  have hc : cos (((2 * m + 1 : ℕ) : ℝ) * π) = -1 := by
    rw [cos_nat_mul_pi, pow_succ, pow_mul]
    simp
  simp only [term]
  rw [e, sin_sub, sin_nat_mul_pi, hc]
  ring

/-- The `C^∞` regularity of a term (as a function of `(t, z)`). -/
theorem contDiff_term (m : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry (term u₀ H cv m)) := by
  change ContDiff ℝ n fun p : ℝ × ℝ =>
    2 * u₀ / modeM m * exp (-modeM m ^ 2 * (cv * p.1 / H ^ 2)) * sin (modeM m * p.2 / H)
  fun_prop

/-- The **partial sums of Terzaghi's series** `Σ_{m<n} uₘ(t, z)`. -/
def partialSol (n : ℕ) (t z : ℝ) : ℝ := ∑ m ∈ Finset.range n, term u₀ H cv m t z

/-- **The partial sums solve Terzaghi's consolidation equation.** -/
theorem isConsolidation_partialSol (n : ℕ) : IsConsolidation cv (partialSol u₀ H cv n) := by
  have e : partialSol u₀ H cv n = fun t z => ∑ m ∈ Finset.range n,
      Heat.mode (2 * H) cv (2 * m + 1) (2 * u₀ / modeM m) t z := by
    funext t z
    simp only [partialSol, term_eq_mode]
  rw [IsConsolidation, e]
  exact Heat.isHeat_sum _ (fun m => Heat.mode (2 * H) cv (2 * m + 1) (2 * u₀ / modeM m))
    (fun m t x => (Heat.hasDerivAt_mode_t _ _ _ _ t x).differentiableAt)
    (fun m t x => (Heat.hasDerivAt_mode_x _ _ _ _ t x).differentiableAt)
    (fun m t x => (Heat.hasDerivAt_dx_mode _ _ _ _ t x).differentiableAt)
    fun m _ => Heat.isHeat_mode _ _ _ _

/-- The partial sums drain at the top face. -/
theorem partialSol_zero (n : ℕ) (t : ℝ) : partialSol u₀ H cv n t 0 = 0 :=
  Finset.sum_eq_zero fun m _ => term_zero u₀ H cv m t

/-- The partial sums drain at the bottom face `z = 2H`. -/
theorem partialSol_two_mul {H : ℝ} (hH : H ≠ 0) (n : ℕ) (t : ℝ) :
    partialSol u₀ H cv n t (2 * H) = 0 :=
  Finset.sum_eq_zero fun m _ => term_two_mul u₀ cv hH m t

/-- The partial sums have zero gradient (no flow) at `z = H`. -/
theorem dx_partialSol_self {H : ℝ} (hH : H ≠ 0) (n : ℕ) (t : ℝ) :
    dx (partialSol u₀ H cv n) t H = 0 := by
  have e := Strings.dx_sum (Finset.range n) (term u₀ H cv)
    (fun m t z => (hasDerivAt_term_z u₀ H cv m t z).differentiableAt)
  change dx (fun t z => ∑ m ∈ Finset.range n, term u₀ H cv m t z) t H = 0
  rw [e]
  exact Finset.sum_eq_zero fun m _ => dx_term_self u₀ cv hH m t

/-- The partial sums are `C^∞`. -/
theorem contDiff_partialSol (n : ℕ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (Function.uncurry (partialSol u₀ H cv n)) := by
  change ContDiff ℝ k fun p : ℝ × ℝ => ∑ m ∈ Finset.range n, Function.uncurry (term u₀ H cv m) p
  exact ContDiff.sum fun m _ => contDiff_term u₀ H cv m

end Series

/-! ### Degree of consolidation -/

section Degree

/-- The **average excess pore pressure** `ū(t) = (1/H) ∫₀ᴴ u(t, z) dz` over the drainage path
(by symmetry, also the average over the doubly drained layer). -/
def avgPressure (H : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := 1 / H * ∫ z in (0 : ℝ)..H, u t z

/-- `∫₀ᴴ sin(Mz/H) dz = H/M`. -/
theorem integral_sin_modeM {H : ℝ} (hH : H ≠ 0) (m : ℕ) :
    ∫ z in (0 : ℝ)..H, sin (modeM m * z / H) = H / modeM m := by
  have hM := (modeM_pos m).ne'
  have hc : modeM m / H ≠ 0 := div_ne_zero hM hH
  have e : ∀ z, modeM m * z / H = z * (modeM m / H) := fun z => by ring
  simp only [e]
  rw [intervalIntegral.integral_comp_mul_right sin hc, integral_sin, zero_mul,
    show H * (modeM m / H) = modeM m by field_simp, cos_zero, cos_modeM, smul_eq_mul,
    sub_zero, mul_one, inv_div]

/-- The average excess pore pressure carried by the `m`-th term:
`ūₘ = u₀ (2/M²) e^{-M² T_v}`. -/
theorem avgPressure_term (u₀ cv : ℝ) {H : ℝ} (hH : H ≠ 0) (m : ℕ) (t : ℝ) :
    avgPressure H (term u₀ H cv m) t =
      u₀ * (2 / modeM m ^ 2 * exp (-modeM m ^ 2 * timeFactor cv H t)) := by
  have hM := (modeM_pos m).ne'
  simp only [avgPressure, term, intervalIntegral.integral_const_mul, integral_sin_modeM hH]
  field_simp

/-- The average excess pore pressure of the partial sums. -/
theorem avgPressure_partialSol (u₀ cv : ℝ) {H : ℝ} (hH : H ≠ 0) (n : ℕ) (t : ℝ) :
    avgPressure H (partialSol u₀ H cv n) t = u₀ * ∑ m ∈ Finset.range n,
      2 / modeM m ^ 2 * exp (-modeM m ^ 2 * timeFactor cv H t) := by
  have hc : ∀ m, Continuous (term u₀ H cv m t) := fun m => by
    unfold term
    fun_prop
  simp only [avgPressure, partialSol]
  rw [intervalIntegral.integral_finsetSum fun m _ => (hc m).intervalIntegrable 0 H,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← avgPressure_term u₀ cv hH m t, avgPressure]

/-- The **degree of consolidation** of the series truncated at `n` terms, as a function of the
time factor: `U(T_v) = 1 - Σ_{m<n} (2/M²) e^{-M² T_v}`. -/
def degree (n : ℕ) (T : ℝ) : ℝ :=
  1 - ∑ m ∈ Finset.range n, 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T)

/-- **The degree of consolidation is `U = 1 - ū/u₀`.** -/
theorem degree_eq {u₀ : ℝ} (hu₀ : u₀ ≠ 0) (cv : ℝ) {H : ℝ} (hH : H ≠ 0) (n : ℕ) (t : ℝ) :
    degree n (timeFactor cv H t) = 1 - avgPressure H (partialSol u₀ H cv n) t / u₀ := by
  rw [avgPressure_partialSol u₀ cv hH, mul_div_cancel_left₀ _ hu₀, degree]

/-- The degree of consolidation is non-decreasing in the time factor. -/
theorem degree_monotone (n : ℕ) : Monotone (degree n) := by
  intro a b hab
  unfold degree
  gcongr 1 - ?_
  refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  nlinarith [mul_nonneg (sq_nonneg (modeM m)) (sub_nonneg.2 hab)]

/-- The degree of consolidation never exceeds `1`. -/
theorem degree_le_one (n : ℕ) (T : ℝ) : degree n T ≤ 1 := by
  unfold degree
  have : 0 ≤ ∑ m ∈ Finset.range n, 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T) :=
    Finset.sum_nonneg fun m _ => by positivity
  linarith

/-- At `T_v = 0` the truncated degree is `1 - Σ_{m<n} 2/M²`. -/
theorem degree_zero (n : ℕ) : degree n 0 = 1 - ∑ m ∈ Finset.range n, 2 / modeM m ^ 2 := by
  simp [degree]

/-- **Completion of consolidation**: `U(T_v) → 1` as `T_v → ∞`. -/
theorem tendsto_degree (n : ℕ) : Tendsto (degree n) atTop (𝓝 1) := by
  have h : Tendsto (fun T => ∑ m ∈ Finset.range n, 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T))
      atTop (𝓝 (∑ m ∈ Finset.range n, 2 / modeM m ^ 2 * 0)) := by
    refine tendsto_finsetSum _ fun m _ => ?_
    have hM : -modeM m ^ 2 < 0 := neg_neg_of_pos (pow_pos (modeM_pos m) 2)
    exact (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hM)).const_mul _
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simp only [mul_zero, Finset.sum_const_zero, sub_zero] at h2
  exact h2

/-- **Euler's sum over the odd integers**: `Σₘ 1/(2m+1)² = π²/8`, derived from `ζ(2) = π²/6`
by splitting off the even terms, which sum to `π²/24`. -/
theorem hasSum_one_div_odd_sq :
    HasSum (fun m : ℕ => 1 / (2 * (m : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have hz : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun k => f (2 * k)) (π ^ 2 / 24) := by
    convert hz.mul_left (1 / 4) using 1
    · funext k
      simp only [hf]
      push_cast
      ring
    · ring
  have hs : Summable fun k => f (2 * k + 1) :=
    hz.summable.comp_injective fun a b h => by simpa using h
  have hsum := he.even_add_odd hs.hasSum
  have hv : ∑' k, f (2 * k + 1) = π ^ 2 / 8 := by
    have := hz.unique hsum
    linarith
  convert hs.hasSum using 1
  · funext m
    simp [hf]
  · exact hv.symm

/-- `Σₘ 2/M² = 1`, `M = (2m+1)π/2`. -/
theorem hasSum_two_div_modeM_sq : HasSum (fun m => 2 / modeM m ^ 2) 1 := by
  have h := hasSum_one_div_odd_sq.mul_left (8 / π ^ 2)
  have hπ := pi_pos.ne'
  convert h using 1
  · funext m
    simp only [modeM]
    field_simp
    ring
  · field_simp

/-- The terms of the full series are summable for `T_v ≥ 0`. -/
theorem summable_series {T : ℝ} (hT : 0 ≤ T) :
    Summable fun m => 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T) :=
  hasSum_two_div_modeM_sq.summable.of_nonneg_of_le (fun m => by positivity) fun m =>
    mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (by nlinarith [sq_nonneg (modeM m)]))

/-- The **degree of consolidation** for the full Terzaghi series:
`U(T_v) = 1 - Σₘ (2/M²) e^{-M² T_v}`. -/
def degreeFull (T : ℝ) : ℝ := 1 - ∑' m, 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T)

/-- **No consolidation at `T_v = 0`**: `U(0) = 0` (because `Σ 2/M² = 1`). -/
theorem degreeFull_zero : degreeFull 0 = 0 := by
  simp [degreeFull, hasSum_two_div_modeM_sq.tsum_eq]

/-- The truncated degrees converge to the full one as the number of terms grows. -/
theorem tendsto_degree_degreeFull {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => degree n T) atTop (𝓝 (degreeFull T)) :=
  (summable_series hT).hasSum.tendsto_sum_nat.const_sub 1

/-- The degree of consolidation is non-decreasing for `T_v ≥ 0`. -/
theorem degreeFull_monotoneOn : MonotoneOn degreeFull (Ici 0) := by
  intro a ha b hb hab
  unfold degreeFull
  have := (summable_series hb).tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (exp_le_exp.2
    (by nlinarith [mul_nonneg (sq_nonneg (modeM m)) (sub_nonneg.2 hab)])) (by positivity))
    (summable_series ha)
  linarith

/-- The degree of consolidation never exceeds `1`. -/
theorem degreeFull_le_one (T : ℝ) : degreeFull T ≤ 1 := by
  unfold degreeFull
  have : 0 ≤ ∑' m, 2 / modeM m ^ 2 * exp (-modeM m ^ 2 * T) := tsum_nonneg fun m => by positivity
  linarith

/-- **Rate of consolidation**: `1 - U(T_v) ≤ e^{-π² T_v / 4}` for `T_v ≥ 0` (every eigenvalue is
at least `π/2`, and `Σ 2/M² = 1`). -/
theorem one_sub_degreeFull_le {T : ℝ} (hT : 0 ≤ T) :
    1 - degreeFull T ≤ exp (-(π ^ 2 / 4) * T) := by
  have h2 := hasSum_two_div_modeM_sq.mul_right (exp (-(π ^ 2 / 4) * T))
  rw [one_mul] at h2
  have hle := (summable_series hT).tsum_le_tsum (fun m => by
    gcongr
    have := pi_div_two_le_modeM m
    have h0 : 0 ≤ π / 2 := by positivity
    nlinarith) h2.summable
  rw [h2.tsum_eq] at hle
  simp only [degreeFull]
  linarith

/-- The same bound for the truncated series: `1 - U_n(T_v) ≤ e^{-π² T_v / 4}`. -/
theorem one_sub_degree_le (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    1 - degree n T ≤ exp (-(π ^ 2 / 4) * T) := by
  have h := sum_le_hasSum (Finset.range n) (fun m _ => by positivity) (summable_series hT).hasSum
  have h2 := one_sub_degreeFull_le hT
  simp only [degree, degreeFull] at h h2 ⊢
  linarith

/-- **Completion of consolidation for the full series**: `U(T_v) → 1` as `T_v → ∞`. -/
theorem tendsto_degreeFull : Tendsto degreeFull atTop (𝓝 1) := by
  have hl : Tendsto (fun T => 1 - exp (-(π ^ 2 / 4) * T)) atTop (𝓝 1) := by
    have hπ : -(π ^ 2 / 4) < 0 := by
      have := pi_pos
      nlinarith
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hπ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with T hT
    linarith [one_sub_degreeFull_le hT]
  · exact Eventually.of_forall degreeFull_le_one

end Degree

/-! ### Settlement -/

section Settlement

/-- **Final consolidation settlement** `s_∞ = m_v Δσ' D` of a layer of thickness `D` under an
increase `Δσ'` of effective stress (coefficient of volume compressibility `m_v`). -/
def finalSettlement (mv Δσ' D : ℝ) : ℝ := mv * Δσ' * D

/-- Once the excess pore pressure `Δσ` has fully dissipated the effective stress has increased
by the applied load: `Δσ' = σ'(u = 0) - σ'(u = Δσ) = Δσ`, so `s_∞ = m_v Δσ D`. -/
theorem finalSettlement_load (mv Δσ D : ℝ) :
    finalSettlement mv (effectiveStress Δσ 0 - effectiveStress Δσ Δσ) D = mv * Δσ * D := by
  simp [finalSettlement, effectiveStress]

/-- **Settlement at time factor `T_v`**: `s = U(T_v) s_∞`. -/
def settlement (sInf T : ℝ) : ℝ := degreeFull T * sInf

/-- No settlement at `T_v = 0`. -/
theorem settlement_zero (sInf : ℝ) : settlement sInf 0 = 0 := by
  simp [settlement, degreeFull_zero]

/-- The settlement never exceeds the final settlement (for `s_∞ ≥ 0`). -/
theorem settlement_le {sInf : ℝ} (hs : 0 ≤ sInf) (T : ℝ) : settlement sInf T ≤ sInf :=
  mul_le_of_le_one_left hs (degreeFull_le_one T)

/-- The settlement is non-decreasing in time (for `s_∞ ≥ 0`). -/
theorem settlement_monotoneOn {sInf : ℝ} (hs : 0 ≤ sInf) : MonotoneOn (settlement sInf) (Ici 0) :=
  fun _ ha _ hb hab => mul_le_mul_of_nonneg_right (degreeFull_monotoneOn ha hb hab) hs

/-- The settlement tends to the final settlement: `s(T_v) → s_∞`. -/
theorem tendsto_settlement (sInf : ℝ) : Tendsto (settlement sInf) atTop (𝓝 sInf) := by
  have h := tendsto_degreeFull.mul_const sInf
  rwa [one_mul] at h

end Settlement

end ContinuumMechanics.Geotechnics
