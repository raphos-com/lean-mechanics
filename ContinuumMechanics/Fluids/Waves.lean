import ContinuumMechanics.Beams.String
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Linear acoustics and linear water waves

Two classical linearizations of the ideal-fluid (Euler) equations of
`ContinuumMechanics.Fluids.Ideal`.

**Linear acoustics (1D).** Small perturbations `p, ρ, v` of a fluid at rest with density `ρ₀`
obey the linearized momentum equation `ρ₀ v_t = -p_x`, the linearized continuity equation
`ρ_t = -ρ₀ v_x` and the barotropic law `p = c² ρ`, `c² = dp/dρ (ρ₀)`. Eliminating `ρ` and `v`
gives the wave equation `p_tt = c² p_xx` of `ContinuumMechanics.Strings` (fields
`ℝ → ℝ → ℝ` of `t` and `x`, partial derivatives `Strings.dt`, `Strings.dx`).

**Linear water waves.** Over a flat bottom at depth `h`, the velocity potential `φ(x, z, t)`,
`-h ≤ z ≤ 0`, is harmonic, satisfies `φ_z = 0` at the bottom and the combined (kinematic +
dynamic) free-surface condition `φ_tt + g φ_z = 0` at `z = 0`. The travelling wave
`φ = A cosh(k(z + h)) cos(kx - ωt)` solves the problem iff the **dispersion relation**
`ω² = g k tanh(kh)` holds.

## Main definitions

* `IsLinearAcoustics ρ₀ c p ρ v`: the linearized Euler system with sound speed `c`.
* `energyDensity`, `intensity`: acoustic energy density `p²/(2ρ₀c²) + ρ₀v²/2` and intensity
  `p v`.
* `px`, `pz`, `pt`; `IsHarmonic`, `BottomBC`, `FreeSurfaceBC`: the linear water-wave problem.
* `travellingPotential A k h ω`: `A cosh(k(z + h)) cos(kx - ωt)`.
* `omegaSq g k h = g k tanh(kh)`, `phaseSpeed g k h = √((g/k) tanh(kh))`,
  `groupSpeed g k h = (c/2)(1 + 2kh / sinh(2kh))`.

## Main results

* `IsLinearAcoustics.isWave`: `p_tt = c² p_xx` for a `C²` velocity field.
* `isLinearAcoustics_planeWave`, `planeWave_impedance`: plane waves `p = f(x - ct)`,
  `v = p/(ρ₀c)` (acoustic impedance `Z = ρ₀c`).
* `IsLinearAcoustics.energy_conservation`: `e_t + I_x = 0`.
* `hasDerivAt_polytrope`: for `p = Kρ^γ`, `dp/dρ = γp/ρ` (speed of sound of an ideal gas).
* `isHarmonic_travellingPotential`, `bottomBC_travellingPotential`,
  `freeSurfaceBC_travellingPotential_iff`: the dispersion relation `ω² = g k tanh(kh)`.
* `tendsto_omegaSq_div_deep`, `tendsto_phaseSpeed_deep`: deep water, `c → √(g/k)`.
* `tendsto_omegaSq_div_shallow`, `tendsto_phaseSpeed_shallow`: shallow water, `c → √(gh)`.
* `strictAntiOn_tanh_div_self`, `strictAntiOn_phaseSpeed`: longer waves travel faster.
* `hasDerivAt_omega`: the group velocity `dω/dk = (c/2)(1 + 2kh/sinh(2kh))`;
  `groupSpeed_lt_phaseSpeed`, `half_phaseSpeed_lt_groupSpeed`, `tendsto_groupSpeed_deep`
  (`c/2 < c_g < c`, and `c_g → c/2` in deep water).

## References

* [LandauLifshitz1987] L. D. Landau, E. M. Lifshitz, *Fluid Mechanics*, 2nd ed., §§12, 64–65.
* [Lighthill1978] J. Lighthill, *Waves in Fluids*, §§1.1–1.3, 3.1–3.4.
* [Whitham1974] G. B. Whitham, *Linear and Nonlinear Waves*, §§13.1–13.2.
-/

open Real Filter Topology Set

noncomputable section

namespace ContinuumMechanics.Fluids.Waves

open Strings

/-! ### Linear acoustics -/

/-- **Mixed partials commute** for a `C²` field: `∂ₜ∂ₓv = ∂ₓ∂ₜv`. -/
theorem dt_dx_comm {v : ℝ → ℝ → ℝ} (hv : ContDiff ℝ 2 (Function.uncurry v)) (t x : ℝ) :
    dt (dx v) t x = dx (dt v) t x := by
  rw [dx_eq_dirDeriv hv, dt_eq_dirDeriv hv]
  have h1 := hasDerivAt_fst_of_differentiable
    ((contDiff_dirDeriv hv (0, 1)).differentiable one_ne_zero) t x
  have h2 := hasDerivAt_snd_of_differentiable
    ((contDiff_dirDeriv hv (1, 0)).differentiable one_ne_zero) t x
  exact h1.deriv.trans ((fderiv_dirDeriv_comm hv _ _ _).trans h2.deriv.symm)

/-- The **equations of linear acoustics** in one dimension for the acoustic pressure `p`,
density `ρ` and velocity `v` about a state at rest with density `ρ₀`: linearized momentum
`ρ₀ v_t = -p_x`, linearized continuity `ρ_t = -ρ₀ v_x` and the barotropic law `p = c² ρ`. -/
structure IsLinearAcoustics (ρ₀ c : ℝ) (p ρ v : ℝ → ℝ → ℝ) : Prop where
  /-- Linearized Euler equation `ρ₀ v_t = -p_x`. -/
  momentum : ∀ t x, ρ₀ * dt v t x = -dx p t x
  /-- Linearized continuity equation `ρ_t = -ρ₀ v_x`. -/
  continuity : ∀ t x, dt ρ t x = -(ρ₀ * dx v t x)
  /-- Linearized equation of state `p = c² ρ`. -/
  state : ∀ t x, p t x = c ^ 2 * ρ t x

section Acoustics

variable {ρ₀ c : ℝ} {p ρ v : ℝ → ℝ → ℝ}

/-- `p_t = -ρ₀ c² v_x`. -/
theorem IsLinearAcoustics.dt_pressure (h : IsLinearAcoustics ρ₀ c p ρ v) (t x : ℝ) :
    dt p t x = -(c ^ 2 * ρ₀) * dx v t x := by
  have hp : p = fun t x => c ^ 2 * ρ t x := funext fun t => funext fun x => h.state t x
  change deriv (fun s => p s x) t = _
  rw [hp, deriv_const_mul_field]
  have := h.continuity t x
  simp only [dt] at this
  rw [this]; ring

/-- `v_t = -p_x / ρ₀`. -/
theorem IsLinearAcoustics.dt_velocity (h : IsLinearAcoustics ρ₀ c p ρ v) (hρ₀ : ρ₀ ≠ 0)
    (t x : ℝ) : dt v t x = -ρ₀⁻¹ * dx p t x := by
  have := h.momentum t x
  field_simp
  linarith

/-- **The acoustic wave equation**: for a `C²` velocity field, the acoustic pressure satisfies
`p_tt = c² p_xx`. -/
theorem IsLinearAcoustics.isWave (h : IsLinearAcoustics ρ₀ c p ρ v) (hρ₀ : ρ₀ ≠ 0)
    (hv : ContDiff ℝ 2 (Function.uncurry v)) : IsWave c p := by
  intro t x
  have e1 : dt p = fun t x => -(c ^ 2 * ρ₀) * dx v t x :=
    funext fun t => funext fun x => h.dt_pressure t x
  have e2 : dt v = fun t x => -ρ₀⁻¹ * dx p t x :=
    funext fun t => funext fun x => h.dt_velocity hρ₀ t x
  have k1 : dt (dt p) t x = -(c ^ 2 * ρ₀) * dt (dx v) t x := by
    rw [e1]; exact deriv_const_mul_field _
  have k2 : dx (dt v) t x = -ρ₀⁻¹ * dx (dx p) t x := by
    rw [e2]; exact deriv_const_mul_field _
  rw [k1, dt_dx_comm hv, k2]
  field_simp

/-- Time derivative of a right-moving profile `a f(x - ct)`. -/
theorem hasDerivAt_profile_t {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a c x t : ℝ) :
    HasDerivAt (fun s => a * f (x - c * s)) (-c * a * deriv f (x - c * t)) t := by
  have := ((hf (x - c * t)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul c).const_sub x)).const_mul a
  convert this using 1
  · simp
  · ring

/-- Space derivative of a right-moving profile `a f(x - ct)`. -/
theorem hasDerivAt_profile_x {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a c x t : ℝ) :
    HasDerivAt (fun y => a * f (y - c * t)) (a * deriv f (x - c * t)) x := by
  have := ((hf (x - c * t)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const (c * t))).const_mul a
  convert this using 1
  · simp
  · ring

/-- **Plane acoustic waves**: for any differentiable profile `f`, `p = f(x - ct)`,
`ρ = p / c²`, `v = p / (ρ₀ c)` solve the equations of linear acoustics. -/
theorem isLinearAcoustics_planeWave {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hρ₀ : ρ₀ ≠ 0)
    (hc : c ≠ 0) :
    IsLinearAcoustics ρ₀ c (fun t x => f (x - c * t)) (fun t x => f (x - c * t) / c ^ 2)
      (fun t x => f (x - c * t) / (ρ₀ * c)) where
  momentum t x := by
    have h1 := (hasDerivAt_profile_t hf (ρ₀ * c)⁻¹ c x t).deriv
    have h2 := (hasDerivAt_profile_x hf 1 c x t).deriv
    simp only [dt, dx, div_eq_inv_mul] at h1 h2 ⊢
    simp only [one_mul] at h2
    rw [h1, h2]; field_simp
  continuity t x := by
    have h1 := (hasDerivAt_profile_t hf (c ^ 2)⁻¹ c x t).deriv
    have h2 := (hasDerivAt_profile_x hf (ρ₀ * c)⁻¹ c x t).deriv
    simp only [dt, dx, div_eq_inv_mul] at h1 h2 ⊢
    rw [h1, h2]; field_simp
  state t x := by field_simp

/-- **Acoustic impedance**: in a plane wave the pressure is `Z = ρ₀ c` times the velocity. -/
theorem planeWave_impedance (f : ℝ → ℝ) (hρ₀ : ρ₀ ≠ 0) (hc : c ≠ 0) (t x : ℝ) :
    f (x - c * t) = ρ₀ * c * (f (x - c * t) / (ρ₀ * c)) := by
  field_simp

/-- The **acoustic energy density** `e = p²/(2ρ₀c²) + ρ₀v²/2`. -/
def energyDensity (ρ₀ c : ℝ) (p v : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p t x ^ 2 / (2 * ρ₀ * c ^ 2) + ρ₀ * v t x ^ 2 / 2

/-- The **acoustic intensity** (energy flux) `I = p v`. -/
def intensity (p v : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := p t x * v t x

/-- **Conservation of acoustic energy**: `e_t + I_x = 0` for `C¹` pressure and velocity. -/
theorem IsLinearAcoustics.energy_conservation (h : IsLinearAcoustics ρ₀ c p ρ v)
    (hρ₀ : ρ₀ ≠ 0) (hc : c ≠ 0) (hp : ContDiff ℝ 1 (Function.uncurry p))
    (hv : ContDiff ℝ 1 (Function.uncurry v)) (t x : ℝ) :
    dt (energyDensity ρ₀ c p v) t x + dx (intensity p v) t x = 0 := by
  have hpd := hp.differentiable one_ne_zero
  have hvd := hv.differentiable one_ne_zero
  have hpt := (hasDerivAt_fst_of_differentiable hpd t x).differentiableAt.hasDerivAt
  have hvt := (hasDerivAt_fst_of_differentiable hvd t x).differentiableAt.hasDerivAt
  have hpx := (hasDerivAt_snd_of_differentiable hpd t x).differentiableAt.hasDerivAt
  have hvx := (hasDerivAt_snd_of_differentiable hvd t x).differentiableAt.hasDerivAt
  have he :=
    ((hpt.pow 2).div_const (2 * ρ₀ * c ^ 2)).add (((hvt.pow 2).const_mul ρ₀).div_const 2)
  have hi := hpx.mul hvx
  have e1 : dt (energyDensity ρ₀ c p v) t x = _ := he.deriv
  have e2 : dx (intensity p v) t x = _ := hi.deriv
  rw [e1, e2]
  have a1 : deriv (fun s => p s x) t = -(c ^ 2 * ρ₀) * deriv (fun y => v t y) x :=
    h.dt_pressure t x
  have a2 : ρ₀ * deriv (fun s => v s x) t = -deriv (fun y => p t y) x := h.momentum t x
  simp only [Function.uncurry_apply_pair] at a1 a2 ⊢
  generalize deriv (fun s => p s x) t = Pt at a1 ⊢
  generalize deriv (fun s => v s x) t = Vt at a2 ⊢
  generalize deriv (fun y => p t y) x = Px at a2 ⊢
  generalize deriv (fun y => v t y) x = Vx at a1 ⊢
  rw [a1]
  field_simp
  linear_combination (2 * v t x) * a2

end Acoustics

/-- **Speed of sound of an ideal gas**: for the isentropic law `p(ρ) = K ρ^γ`, the squared
sound speed `c² = dp/dρ` equals `γ p / ρ`. -/
theorem hasDerivAt_polytrope (K γ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => K * s ^ γ) (γ * (K * r ^ γ) / r) r := by
  have := (hasDerivAt_rpow_const (p := γ) (Or.inl hr.ne')).const_mul K
  convert this using 1
  rw [rpow_sub_one hr.ne']; field_simp

/-! ### Linear water waves -/

/-- Horizontal partial derivative `∂ₓφ(x, z, t)`. -/
def px (φ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun x z t => deriv (fun y => φ y z t) x

/-- Vertical partial derivative `∂_zφ(x, z, t)`. -/
def pz (φ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun x z t => deriv (fun y => φ x y t) z

/-- Time derivative `∂ₜφ(x, z, t)`. -/
def pt (φ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun x z t => deriv (fun s => φ x z s) t

/-- **Laplace's equation** `φ_xx + φ_zz = 0` (incompressible irrotational flow). -/
def IsHarmonic (φ : ℝ → ℝ → ℝ → ℝ) : Prop := ∀ x z t, px (px φ) x z t + pz (pz φ) x z t = 0

/-- The **impermeable bottom condition** `φ_z = 0` at `z = -h`. -/
def BottomBC (h : ℝ) (φ : ℝ → ℝ → ℝ → ℝ) : Prop := ∀ x t, pz φ x (-h) t = 0

/-- The **linearized combined free-surface condition** `φ_tt + g φ_z = 0` at `z = 0`. -/
def FreeSurfaceBC (g : ℝ) (φ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, pt (pt φ) x 0 t + g * pz φ x 0 t = 0

/-- The travelling-wave potential `φ = A cosh(k(z + h)) cos(kx - ωt)`. -/
def travellingPotential (A k h ω : ℝ) (x z t : ℝ) : ℝ :=
  A * cosh (k * (z + h)) * cos (k * x - ω * t)

section WaterWaves

variable {A k h ω g : ℝ}

/-- `φ_x` for the travelling-wave potential. -/
theorem px_travellingPotential : px (travellingPotential A k h ω) =
    fun x z t => -(A * k * cosh (k * (z + h))) * sin (k * x - ω * t) := by
  funext x z t
  have := ((((hasDerivAt_id x).const_mul k).sub_const (ω * t)).cos).const_mul
    (A * cosh (k * (z + h)))
  refine (this.deriv.trans ?_ : _)
  simp; ring

/-- `φ_xx = -k² φ` for the travelling-wave potential. -/
theorem px_px_travellingPotential : px (px (travellingPotential A k h ω)) =
    fun x z t => -k ^ 2 * travellingPotential A k h ω x z t := by
  rw [px_travellingPotential]
  funext x z t
  have := ((((hasDerivAt_id x).const_mul k).sub_const (ω * t)).sin).const_mul
    (-(A * k * cosh (k * (z + h))))
  refine (this.deriv.trans ?_ : _)
  simp [travellingPotential]; ring

/-- `φ_z` for the travelling-wave potential. -/
theorem pz_travellingPotential : pz (travellingPotential A k h ω) =
    fun x z t => A * k * sinh (k * (z + h)) * cos (k * x - ω * t) := by
  funext x z t
  have := (((((hasDerivAt_id z).add_const h).const_mul k).cosh).const_mul A).mul_const
    (cos (k * x - ω * t))
  refine (this.deriv.trans ?_ : _)
  simp only [id, mul_one]; ring

/-- `φ_zz = k² φ` for the travelling-wave potential. -/
theorem pz_pz_travellingPotential : pz (pz (travellingPotential A k h ω)) =
    fun x z t => k ^ 2 * travellingPotential A k h ω x z t := by
  rw [pz_travellingPotential]
  funext x z t
  have := (((((hasDerivAt_id z).add_const h).const_mul k).sinh).const_mul (A * k)).mul_const
    (cos (k * x - ω * t))
  refine (this.deriv.trans ?_ : _)
  simp [travellingPotential]; ring

/-- `φ_t` for the travelling-wave potential. -/
theorem pt_travellingPotential : pt (travellingPotential A k h ω) =
    fun x z t => A * ω * cosh (k * (z + h)) * sin (k * x - ω * t) := by
  funext x z t
  have := ((((hasDerivAt_id t).const_mul ω).const_sub (k * x)).cos).const_mul
    (A * cosh (k * (z + h)))
  refine (this.deriv.trans ?_ : _)
  simp; ring

/-- `φ_tt = -ω² φ` for the travelling-wave potential. -/
theorem pt_pt_travellingPotential : pt (pt (travellingPotential A k h ω)) =
    fun x z t => -ω ^ 2 * travellingPotential A k h ω x z t := by
  rw [pt_travellingPotential]
  funext x z t
  have := ((((hasDerivAt_id t).const_mul ω).const_sub (k * x)).sin).const_mul
    (A * ω * cosh (k * (z + h)))
  refine (this.deriv.trans ?_ : _)
  simp [travellingPotential]; ring

/-- The travelling-wave potential is harmonic, for every `k` and `ω`. -/
theorem isHarmonic_travellingPotential : IsHarmonic (travellingPotential A k h ω) := by
  intro x z t; rw [px_px_travellingPotential, pz_pz_travellingPotential]; ring

/-- The travelling-wave potential satisfies the bottom condition at `z = -h`. -/
theorem bottomBC_travellingPotential : BottomBC h (travellingPotential A k h ω) := by
  intro x t; simp [pz_travellingPotential]

/-- The free-surface residual `φ_tt + g φ_z` at `z = 0` of the travelling-wave potential. -/
theorem freeSurface_travellingPotential_eq (x t : ℝ) :
    pt (pt (travellingPotential A k h ω)) x 0 t + g * pz (travellingPotential A k h ω) x 0 t =
      A * cos (k * x - ω * t) * (g * k * sinh (k * h) - ω ^ 2 * cosh (k * h)) := by
  rw [pt_pt_travellingPotential, pz_travellingPotential]; simp [travellingPotential]; ring

/-- **The dispersion relation of linear water waves**: a nonzero travelling-wave potential
satisfies the free-surface condition iff `ω² = g k tanh(kh)`. -/
theorem freeSurfaceBC_travellingPotential_iff (hA : A ≠ 0) :
    FreeSurfaceBC g (travellingPotential A k h ω) ↔ ω ^ 2 = g * k * tanh (k * h) := by
  have hc := (cosh_pos (k * h)).ne'
  rw [tanh_eq_sinh_div_cosh]
  constructor
  · intro H
    have := H 0 0
    rw [freeSurface_travellingPotential_eq] at this
    simp only [mul_zero, sub_zero, cos_zero, mul_one, mul_eq_zero, hA, false_or] at this
    field_simp
    linarith
  · intro H x t
    rw [freeSurface_travellingPotential_eq]
    field_simp at H
    rw [H]; ring

end WaterWaves

/-! ### Hyperbolic tangent: limits and monotonicity -/

/-- `tanh y = 1 - 2 / (e^{2y} + 1)`. -/
theorem tanh_eq_one_sub (y : ℝ) : tanh y = 1 - 2 / (exp y * exp y + 1) := by
  have he := exp_pos y
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, exp_neg]
  field_simp
  ring

/-- `tanh y → 1` as `y → ∞`. -/
theorem tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have h : Tendsto (fun y => exp y * exp y + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_exp_atTop.atTop_mul_atTop₀ tendsto_exp_atTop)
  have := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop h
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub this
  simp only [sub_zero] at this
  exact this.congr fun y => (tanh_eq_one_sub y).symm

/-- `tanh x / x → 1` as `x → 0`. -/
theorem tendsto_tanh_div_self : Tendsto (fun x => tanh x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h1 := (hasDerivAt_sinh 0).tendsto_slope_zero
  simp only [zero_add, sinh_zero, sub_zero, cosh_zero, smul_eq_mul] at h1
  have h2 : Tendsto cosh (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (continuous_cosh.tendsto 0)
  have := h1.div h2 one_ne_zero
  simp only [div_one] at this
  refine this.congr fun x => ?_
  simp only [Pi.div_apply]
  rw [tanh_eq_sinh_div_cosh]; ring

/-- `tanh x / x = sinh x / (x cosh x)`. -/
theorem tanh_div_self_eq (x : ℝ) : tanh x / x = sinh x / (x * cosh x) := by
  rw [tanh_eq_sinh_div_cosh, div_div, mul_comm]

/-- `x < sinh x cosh x` for `x > 0`. -/
theorem self_lt_sinh_mul_cosh {x : ℝ} (hx : 0 < x) : x < sinh x * cosh x := by
  have := self_lt_sinh_iff.2 (by positivity : 0 < 2 * x)
  rw [sinh_two_mul] at this
  linarith

/-- `tanh x / x` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_tanh_div_self : StrictAntiOn (fun x => tanh x / x) (Ioi 0) := by
  simp only [tanh_div_self_eq]
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · refine continuous_sinh.continuousOn.div (continuous_id.mul continuous_cosh).continuousOn ?_
    intro x hx
    exact mul_ne_zero (ne_of_gt hx) (cosh_pos x).ne'
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : 0 < x := hx
    have hne : x * cosh x ≠ 0 := mul_ne_zero hx.ne' (cosh_pos x).ne'
    have hd := (hasDerivAt_sinh x).div ((hasDerivAt_id x).mul (hasDerivAt_cosh x)) hne
    rw [show (fun x => sinh x / (x * cosh x)) = sinh / (id * cosh) from rfl, hd.deriv]
    simp only [Pi.mul_apply, id]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have h1 := cosh_sq_sub_sinh_sq x
    have h2 := self_lt_sinh_mul_cosh hx
    nlinarith

/-- `y² / 4 ≤ sinh y` for `y ≥ 0`. -/
theorem sq_div_four_le_sinh {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 4 ≤ sinh y := by
  have h1 := quadratic_le_exp_of_nonneg hy
  have h2 : exp (-y) ≤ 1 := exp_le_one_iff.2 (by linarith)
  rw [sinh_eq]
  nlinarith

/-- `y / sinh y → 0` as `y → ∞`. -/
theorem tendsto_self_div_sinh_atTop : Tendsto (fun y => y / sinh y) atTop (𝓝 0) := by
  have hup : Tendsto (fun y : ℝ => 4 / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with y hy
    exact div_nonneg hy.le (sinh_pos_iff.2 hy).le
  · filter_upwards [eventually_gt_atTop 0] with y hy
    have hs := sq_div_four_le_sinh hy.le
    have hs0 := sinh_pos_iff.2 hy
    rw [div_le_div_iff₀ hs0 hy]
    nlinarith

/-- `tanh x > 0` for `x > 0`. -/
theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.2 hx) (cosh_pos x)

/-! ### Dispersion: phase and group velocity -/

/-- The squared frequency `ω² = g k tanh(kh)` given by the dispersion relation. -/
def omegaSq (g k h : ℝ) : ℝ := g * k * tanh (k * h)

/-- The phase speed `c = ω / k = √((g / k) tanh(kh))`. -/
def phaseSpeed (g k h : ℝ) : ℝ := √(g * tanh (k * h) / k)

/-- The group velocity `c_g = (c / 2)(1 + 2kh / sinh(2kh))`. -/
def groupSpeed (g k h : ℝ) : ℝ := phaseSpeed g k h / 2 * (1 + 2 * k * h / sinh (2 * k * h))

section Dispersion

variable {g k h ω : ℝ}

/-- The phase speed is positive. -/
theorem phaseSpeed_pos (hg : 0 < g) (hk : 0 < k) (hh : 0 < h) : 0 < phaseSpeed g k h :=
  sqrt_pos.2 (div_pos (mul_pos hg (tanh_pos (mul_pos hk hh))) hk)

/-- If `ω ≥ 0` satisfies the dispersion relation, then `ω / k` is the phase speed. -/
theorem div_eq_phaseSpeed (hk : 0 < k) (hω : 0 ≤ ω) (hd : ω ^ 2 = omegaSq g k h) :
    ω / k = phaseSpeed g k h := by
  rw [phaseSpeed, ← sqrt_sq (div_nonneg hω hk.le), div_pow, hd, omegaSq]
  congr 1
  field_simp

/-- **Deep water**: `ω² / (g k) = tanh(kh) → 1` as `h → ∞`. -/
theorem tendsto_omegaSq_div_deep (hg : g ≠ 0) (hk : 0 < k) :
    Tendsto (fun h => omegaSq g k h / (g * k)) atTop (𝓝 1) := by
  refine (tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop hk)).congr fun h => ?_
  simp only [Function.comp, id, omegaSq]
  field_simp

/-- **Deep water**: the phase speed tends to `√(g / k)` as `h → ∞`. -/
theorem tendsto_phaseSpeed_deep (hk : 0 < k) :
    Tendsto (fun h => phaseSpeed g k h) atTop (𝓝 (√(g / k))) := by
  have := (((tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop hk)).const_mul g).div_const
    k).sqrt
  simpa [Function.comp, phaseSpeed] using this

/-- `k h → 0` (with `k h ≠ 0`) as `h → 0⁺`, for `k > 0`. -/
theorem tendsto_mul_nhdsNE {k : ℝ} (hk : 0 < k) :
    Tendsto (fun h => k * h) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_const_mul k).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero hk.ne' (ne_of_gt hh)

/-- **Shallow water**: `ω² / (k² g h) → 1` as `h → 0⁺`. -/
theorem tendsto_omegaSq_div_shallow (hg : g ≠ 0) (hk : 0 < k) :
    Tendsto (fun h => omegaSq g k h / (k ^ 2 * g * h)) (𝓝[>] 0) (𝓝 1) := by
  refine (tendsto_tanh_div_self.comp (tendsto_mul_nhdsNE hk)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : h ≠ 0 := ne_of_gt hh
  simp only [Function.comp, omegaSq]
  field_simp

/-- **Shallow water (long waves)**: the phase speed tends to the non-dispersive value `√(g h)`
as `k → 0⁺`. -/
theorem tendsto_phaseSpeed_shallow (hh : 0 < h) :
    Tendsto (fun k => phaseSpeed g k h) (𝓝[>] 0) (𝓝 (√(g * h))) := by
  have hl : Tendsto (fun k => h * k) (𝓝[>] 0) (𝓝[≠] 0) := tendsto_mul_nhdsNE hh
  have := ((tendsto_tanh_div_self.comp hl).const_mul (g * h)).sqrt
  simp only [mul_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk : k ≠ 0 := ne_of_gt hk
  simp only [Function.comp, phaseSpeed]
  congr 1
  rw [mul_comm h k]
  field_simp

/-- **Longer waves travel faster**: the phase speed is strictly decreasing in the wavenumber
`k` (i.e. increasing in the wavelength `2π / k`). -/
theorem strictAntiOn_phaseSpeed (hg : 0 < g) (hh : 0 < h) :
    StrictAntiOn (fun k => phaseSpeed g k h) (Ioi 0) := by
  intro a ha b hb hab
  have ha : 0 < a := ha
  have hb : 0 < b := hb
  have key := strictAntiOn_tanh_div_self (mul_pos ha hh) (mul_pos hb hh)
    (mul_lt_mul_of_pos_right hab hh)
  simp only at key
  have e : ∀ k, 0 < k → g * tanh (k * h) / k = g * h * (tanh (k * h) / (k * h)) := by
    intro k hk; field_simp
  simp only [phaseSpeed]
  rw [e a ha, e b hb]
  exact sqrt_lt_sqrt (mul_nonneg (mul_pos hg hh).le
    (div_pos (tanh_pos (mul_pos hb hh)) (mul_pos hb hh)).le)
    (mul_lt_mul_of_pos_left key (mul_pos hg hh))

/-- **Group velocity**: `ω(k) = √(g k tanh(kh))` has derivative
`dω/dk = (c / 2)(1 + 2kh / sinh(2kh))`. -/
theorem hasDerivAt_omega (hg : 0 < g) (hk : 0 < k) (hh : 0 < h) :
    HasDerivAt (fun k => √(omegaSq g k h)) (groupSpeed g k h) k := by
  have hc := cosh_pos (k * h)
  have hs := sinh_pos_iff.2 (mul_pos hk hh)
  have hk' : HasDerivAt (fun k : ℝ => k * h) h k := by
    simpa using (hasDerivAt_id k).mul_const h
  have hF := ((hasDerivAt_id k).const_mul g).mul (hk'.sinh.div hk'.cosh hc.ne')
  have hne : g * k * (sinh (k * h) / cosh (k * h)) ≠ 0 := by positivity
  have := hF.sqrt hne
  simp only [Pi.mul_apply, Pi.div_apply, id, mul_one] at this
  simp only [omegaSq, tanh_eq_sinh_div_cosh]
  convert this using 1
  set X := g * (sinh (k * h) / cosh (k * h)) / k with hX
  have hX0 : 0 < X := by positivity
  have hsq : √(g * k * (sinh (k * h) / cosh (k * h))) = k * √X := by
    rw [show g * k * (sinh (k * h) / cosh (k * h)) = k ^ 2 * X by rw [hX]; field_simp,
      sqrt_mul (by positivity), sqrt_sq hk.le]
  have hS := sq_sqrt hX0.le
  have hS0 := sqrt_pos.2 hX0
  rw [hsq, groupSpeed, phaseSpeed, tanh_eq_sinh_div_cosh, ← hX,
    show 2 * k * h = 2 * (k * h) by ring, sinh_two_mul]
  have h1 := cosh_sq_sub_sinh_sq (k * h)
  field_simp
  rw [hS, hX]
  field_simp
  linear_combination (-(k * h)) * h1

/-- **Water waves are normally dispersive**: the group velocity is smaller than the phase
speed, `c_g < c`. -/
theorem groupSpeed_lt_phaseSpeed (hg : 0 < g) (hk : 0 < k) (hh : 0 < h) :
    groupSpeed g k h < phaseSpeed g k h := by
  have hkh : 0 < 2 * k * h := by positivity
  have hr : 2 * k * h / sinh (2 * k * h) < 1 :=
    (div_lt_one (sinh_pos_iff.2 hkh)).2 (self_lt_sinh_iff.2 hkh)
  have := phaseSpeed_pos hg hk hh
  rw [groupSpeed]
  nlinarith

/-- The group velocity exceeds half the phase speed, `c / 2 < c_g`. -/
theorem half_phaseSpeed_lt_groupSpeed (hg : 0 < g) (hk : 0 < k) (hh : 0 < h) :
    phaseSpeed g k h / 2 < groupSpeed g k h := by
  have hkh : 0 < 2 * k * h := by positivity
  have hr : 0 < 2 * k * h / sinh (2 * k * h) := div_pos hkh (sinh_pos_iff.2 hkh)
  have := phaseSpeed_pos hg hk hh
  rw [groupSpeed]
  nlinarith

/-- **Deep water**: the group velocity tends to half the deep-water phase speed,
`c_g → √(g / k) / 2`, as `h → ∞`. -/
theorem tendsto_groupSpeed_deep (hk : 0 < k) :
    Tendsto (fun h => groupSpeed g k h) atTop (𝓝 (√(g / k) / 2)) := by
  have h2 : Tendsto (fun h => 2 * k * h) atTop atTop := by
    simpa [mul_assoc] using tendsto_id.const_mul_atTop (by positivity : 0 < 2 * k)
  have := ((tendsto_phaseSpeed_deep (g := g) hk).div_const 2).mul
    ((tendsto_self_div_sinh_atTop.comp h2).const_add 1)
  simpa [groupSpeed, Function.comp] using this

end Dispersion

end ContinuumMechanics.Fluids.Waves
