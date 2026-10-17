import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ContinuumMechanics.Stress.Criteria

/-!
# Rate-independent plasticity and limit analysis

Classical small-strain, rate-independent plasticity ([Simo1998], ch. 1–2; [Lubliner2008],
ch. 3–4) and the bound theorems of limit analysis for beams ([Neal1977], ch. 1–3).

* **One-dimensional elastoplasticity with linear isotropic hardening.** A bar with Young
  modulus `E > 0`, hardening modulus `H ≥ 0` and initial yield stress `σ_y > 0` has state
  `(ε, ε_p, α)`, stress `σ = E (ε - ε_p)` and yield function `f = |σ| - (σ_y + H α)`. The
  **return mapping** for a new total strain freezes the plastic variables to get the trial stress
  `σ_tr`; if `f_tr ≤ 0` the step is elastic, otherwise `Δγ = f_tr / (E + H)` and
  `ε_p ← ε_p + Δγ sign σ_tr`, `α ← α + Δγ`.
* **Associated von Mises flow.** For `f(σ) = √(3 J₂(σ)) - σ_y`, the directional derivative of
  `J₂ = ½ s : s` is `s : τ` with `s = dev σ`, so `∂f/∂σ = (3 / (2 σ_vM)) s` and the associated
  flow rule `ε̇_p = λ̇ ∂f/∂σ` is traceless (plastic incompressibility).
* **Maximum plastic dissipation.** For a convex differentiable yield function, a stress on the
  yield surface and a plastic rate in the normal cone, `(σ - σ*) : ε̇_p ≥ 0` for every admissible
  `σ*` (Hill's principle / Drucker's inequality).
* **Limit analysis of beams.** For a rectangular `b × h` section, `M_y = σ_y b h² / 6`,
  `M_p = σ_y b h² / 4`, shape factor `3/2`; collapse loads `P_c = 4 M_p / L` (simply supported,
  central point load) and `q_c = 16 M_p / L²` (fixed–fixed, uniform load), each obtained as an
  upper (kinematic) bound that coincides with a lower (static) bound.

## Main results

* `Plasticity.Bar.Δγ_pos`, `Plasticity.Bar.yieldFn_returnMap_of_pos`: the plastic multiplier is
  positive and the returned state lies on the yield surface (consistency);
  `Plasticity.Bar.returnMap_of_nonpos`: an elastic step;
  `Plasticity.Bar.yieldFn_returnMap_nonpos`: the returned state is always admissible.
* `Plasticity.Bar.hasDerivAt_stress_returnMap_of_pos`: the algorithmic elastoplastic tangent is
  `E H / (E + H)`; `Plasticity.Bar.hasDerivAt_stress_returnMap_of_neg`: elastic tangent `E`.
* `Plasticity.Bar.continuous_monotonic`, `Plasticity.Bar.hasDerivAt_monotonic_of_gt`,
  `Plasticity.Bar.stress_returnMap_virgin`: the monotonic loading curve, its slopes, and its
  agreement with the return mapping from the virgin state.
* `ContinuumMechanics.Lin.hasDerivAt_J₂`, `ContinuumMechanics.Lin.hasDerivAt_vonMises`:
  `d/dt J₂(σ + t τ) = dev σ : τ`, `d/dt σ_vM(σ + t τ) = N : τ` with `N = (3 / (2 σ_vM)) dev σ`.
* `ContinuumMechanics.Lin.tr_plasticRate`: plastic incompressibility `tr (λ̇ N) = 0`.
* `Plasticity.le_of_convexOn_hasGradientAt`: the first-order convexity inequality;
  `Plasticity.maxDissipation`: `0 ≤ ⟪σ - σ*, λ̇ ∇f(σ)⟫`.
* `Plasticity.elastic_moment_integral`, `Plasticity.plastic_moment_integral`,
  `Plasticity.shapeFactor_rect`: `M_y`, `M_p` as stress-block integrals and `M_p / M_y = 3/2`.
* `Plasticity.ss_collapse`: `P_c = 4 M_p / L` is both the mechanism load and the greatest
  statically admissible load; `Plasticity.ff_collapse`: likewise `q_c = 16 M_p / L²`.

## References

* [Simo1998] J. C. Simo, T. J. R. Hughes, *Computational Inelasticity*, ch. 1–2.
* [Lubliner2008] J. Lubliner, *Plasticity Theory*, ch. 3–4.
* [Neal1977] B. G. Neal, *The Plastic Methods of Structural Analysis*, 3rd ed., ch. 1–3.
-/

open Real Set Filter
open scoped Topology InnerProductSpace ContinuumMechanics

noncomputable section

namespace Plasticity

/-! ### One-dimensional elastoplastic bar with linear isotropic hardening -/

/-- Material parameters of a 1D elastoplastic bar: Young modulus `E > 0`, linear isotropic
hardening modulus `H ≥ 0` and initial yield stress `σ_y > 0`. -/
structure Bar where
  /-- Young's modulus. -/
  E : ℝ
  /-- Linear isotropic hardening modulus. -/
  H : ℝ
  /-- Initial yield stress. -/
  σy : ℝ
  /-- The Young modulus is positive. -/
  E_pos : 0 < E
  /-- The hardening modulus is nonnegative. -/
  H_nonneg : 0 ≤ H
  /-- The initial yield stress is positive. -/
  σy_pos : 0 < σy

/-- The state of the bar: total strain `ε`, plastic strain `ε_p` and hardening variable `α`. -/
structure State where
  /-- Total strain. -/
  ε : ℝ
  /-- Plastic strain. -/
  εp : ℝ
  /-- Equivalent plastic strain (isotropic hardening variable). -/
  α : ℝ

namespace Bar

variable (m : Bar)

/-- The stress `σ = E (ε - ε_p)` of a state. -/
def stress (s : State) : ℝ := m.E * (s.ε - s.εp)

/-- The yield function `f(σ, α) = |σ| - (σ_y + H α)`. -/
def yieldFn (σ α : ℝ) : ℝ := |σ| - (m.σy + m.H * α)

/-- The trial stress `E (ε - ε_p)` for a new total strain `ε`, plastic variables frozen. -/
def trialStress (s : State) (ε : ℝ) : ℝ := m.E * (ε - s.εp)

/-- The trial value of the yield function. -/
def trialYield (s : State) (ε : ℝ) : ℝ := m.yieldFn (m.trialStress s ε) s.α

/-- The plastic multiplier `Δγ = f_tr / (E + H)`. -/
def Δγ (s : State) (ε : ℝ) : ℝ := m.trialYield s ε / (m.E + m.H)

/-- The **return mapping**: an elastic step if `f_tr ≤ 0`, otherwise the plastic correction
`ε_p ← ε_p + Δγ sign σ_tr`, `α ← α + Δγ`. -/
def returnMap (s : State) (ε : ℝ) : State :=
  if m.trialYield s ε ≤ 0 then ⟨ε, s.εp, s.α⟩
  else ⟨ε, s.εp + m.Δγ s ε * Real.sign (m.trialStress s ε), s.α + m.Δγ s ε⟩

/-- The elastoplastic tangent modulus `E H / (E + H)`. -/
def tangentModulus : ℝ := m.E * m.H / (m.E + m.H)

/-- `E + H > 0`. -/
theorem E_add_H_pos : 0 < m.E + m.H := add_pos_of_pos_of_nonneg m.E_pos m.H_nonneg

/-- With `f_tr ≤ 0` the step is purely elastic. -/
theorem returnMap_of_nonpos {s : State} {ε : ℝ} (h : m.trialYield s ε ≤ 0) :
    m.returnMap s ε = ⟨ε, s.εp, s.α⟩ := ite_eq_left h

/-- In an elastic step the stress is the trial stress. -/
theorem stress_returnMap_of_nonpos {s : State} {ε : ℝ} (h : m.trialYield s ε ≤ 0) :
    m.stress (m.returnMap s ε) = m.trialStress s ε := by
  rw [returnMap_of_nonpos m h]; rfl

/-- The plastic multiplier is positive in a plastic step. -/
theorem Δγ_pos {s : State} {ε : ℝ} (h : 0 < m.trialYield s ε) : 0 < m.Δγ s ε :=
  div_pos h m.E_add_H_pos

/-- In a plastic step, `σ = σ_tr - E Δγ sign σ_tr`. -/
theorem stress_returnMap_of_pos {s : State} {ε : ℝ} (h : 0 < m.trialYield s ε) :
    m.stress (m.returnMap s ε) =
      m.trialStress s ε - m.E * m.Δγ s ε * Real.sign (m.trialStress s ε) := by
  rw [returnMap, ite_eq_right (not_le.mpr h)]
  simp only [stress, trialStress]
  ring

/-- In a plastic step the hardening variable becomes `α + Δγ`. -/
theorem α_returnMap_of_pos {s : State} {ε : ℝ} (h : 0 < m.trialYield s ε) :
    (m.returnMap s ε).α = s.α + m.Δγ s ε := by
  rw [returnMap, ite_eq_right (not_le.mpr h)]

/-- **Consistency**: after a plastic return the state lies on the (hardened) yield surface. -/
theorem yieldFn_returnMap_of_pos {s : State} {ε : ℝ} (hα : 0 ≤ s.α)
    (h : 0 < m.trialYield s ε) :
    m.yieldFn (m.stress (m.returnMap s ε)) (m.returnMap s ε).α = 0 := by
  rw [stress_returnMap_of_pos m h, α_returnMap_of_pos m h]
  have hEH := m.E_add_H_pos
  have hΔ := m.Δγ_pos h
  have key : (m.E + m.H) * m.Δγ s ε = m.trialYield s ε := by
    rw [Δγ]; field_simp
  have hc : 0 < m.σy + m.H * s.α := by
    have := mul_nonneg m.H_nonneg hα; linarith [m.σy_pos]
  have hHΔ : 0 ≤ m.H * m.Δγ s ε := mul_nonneg m.H_nonneg hΔ.le
  have hf : m.trialYield s ε = |m.trialStress s ε| - (m.σy + m.H * s.α) := rfl
  simp only [yieldFn]
  rcases lt_trichotomy (m.trialStress s ε) 0 with hs | hs | hs
  · rw [Real.sign_of_neg hs]
    rw [abs_of_neg hs] at hf
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  · rw [hs, abs_zero] at hf; linarith
  · rw [Real.sign_of_pos hs]
    rw [abs_of_pos hs] at hf
    rw [abs_of_pos (by nlinarith)]
    nlinarith

/-- The returned state is always plastically admissible: `f ≤ 0`. -/
theorem yieldFn_returnMap_nonpos {s : State} {ε : ℝ} (hα : 0 ≤ s.α) :
    m.yieldFn (m.stress (m.returnMap s ε)) (m.returnMap s ε).α ≤ 0 := by
  by_cases h : m.trialYield s ε ≤ 0
  · rw [stress_returnMap_of_nonpos m h, returnMap_of_nonpos m h]; exact h
  · exact (m.yieldFn_returnMap_of_pos hα (not_le.mp h)).le

/-- **Elastoplastic tangent**: in a plastic step, `dσ/dε = E H / (E + H)`. -/
theorem hasDerivAt_stress_returnMap_of_pos {s : State} {ε₀ : ℝ} (hα : 0 ≤ s.α)
    (h : 0 < m.trialYield s ε₀) :
    HasDerivAt (fun ε => m.stress (m.returnMap s ε)) m.tangentModulus ε₀ := by
  have hEH := m.E_add_H_pos
  set c := m.σy + m.H * s.α with hc_def
  have hc : 0 < c := by
    have := mul_nonneg m.H_nonneg hα; linarith [m.σy_pos]
  have hf : ∀ ε, m.trialYield s ε = |m.E * (ε - s.εp)| - c := fun _ => rfl
  have hcont : Continuous fun ε => m.E * (ε - s.εp) := by fun_prop
  rcases lt_or_ge (m.E * (ε₀ - s.εp)) 0 with hs | hs
  · -- compression branch
    have h0 : m.E * (ε₀ - s.εp) < -c := by
      rw [hf, abs_of_neg hs] at h; linarith
    have hev : ∀ᶠ ε in 𝓝 ε₀, m.E * (ε - s.εp) < -c :=
      (isOpen_lt hcont continuous_const).mem_nhds h0
    have heq : (fun ε => m.stress (m.returnMap s ε)) =ᶠ[𝓝 ε₀]
        fun ε => m.E * (ε - s.εp) + m.E * ((-(m.E * (ε - s.εp)) - c) / (m.E + m.H)) := by
      filter_upwards [hev] with ε hε
      have hneg : m.E * (ε - s.εp) < 0 := by linarith
      have hpos : 0 < m.trialYield s ε := by rw [hf, abs_of_neg hneg]; linarith
      rw [stress_returnMap_of_pos m hpos, Δγ, hf, abs_of_neg hneg]
      simp only [trialStress, Real.sign_of_neg hneg]
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    have := (((hasDerivAt_id ε₀).sub_const s.εp).const_mul m.E)
    have h2 := (((this.neg).sub_const c).div_const (m.E + m.H)).const_mul m.E
    exact (this.add h2).congr_deriv (by simp only [tangentModulus]; field_simp; ring)
  · -- tension branch
    have hs' : 0 < m.E * (ε₀ - s.εp) := by
      rcases hs.lt_or_eq with hs | hs
      · exact hs
      · rw [hf, ← hs, abs_zero] at h; linarith
    have h0 : c < m.E * (ε₀ - s.εp) := by
      rw [hf, abs_of_pos hs'] at h; linarith
    have hev : ∀ᶠ ε in 𝓝 ε₀, c < m.E * (ε - s.εp) :=
      (isOpen_lt continuous_const hcont).mem_nhds h0
    have heq : (fun ε => m.stress (m.returnMap s ε)) =ᶠ[𝓝 ε₀]
        fun ε => m.E * (ε - s.εp) - m.E * ((m.E * (ε - s.εp) - c) / (m.E + m.H)) := by
      filter_upwards [hev] with ε hε
      have hpos' : 0 < m.E * (ε - s.εp) := by linarith
      have hpos : 0 < m.trialYield s ε := by rw [hf, abs_of_pos hpos']; linarith
      rw [stress_returnMap_of_pos m hpos, Δγ, hf, abs_of_pos hpos']
      simp only [trialStress, Real.sign_of_pos hpos']
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    have := (((hasDerivAt_id ε₀).sub_const s.εp).const_mul m.E)
    have h2 := ((this.sub_const c).div_const (m.E + m.H)).const_mul m.E
    exact (this.sub h2).congr_deriv (by simp only [tangentModulus]; field_simp; ring)

/-- **Elastic tangent**: strictly inside the elastic domain, `dσ/dε = E`. -/
theorem hasDerivAt_stress_returnMap_of_neg {s : State} {ε₀ : ℝ}
    (h : m.trialYield s ε₀ < 0) :
    HasDerivAt (fun ε => m.stress (m.returnMap s ε)) m.E ε₀ := by
  have hcont : Continuous fun ε => m.trialYield s ε := by
    unfold trialYield yieldFn trialStress; fun_prop
  have hev : ∀ᶠ ε in 𝓝 ε₀, m.trialYield s ε < 0 :=
    (isOpen_lt hcont continuous_const).mem_nhds h
  have heq : (fun ε => m.stress (m.returnMap s ε)) =ᶠ[𝓝 ε₀] fun ε => m.E * (ε - s.εp) := by
    filter_upwards [hev] with ε hε
    rw [stress_returnMap_of_nonpos m hε.le]; rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using ((hasDerivAt_id ε₀).sub_const s.εp).const_mul m.E

/-- The **monotonic loading curve**: `σ = E ε` up to `ε = σ_y / E`, then
`σ = σ_y + (E H / (E + H)) (ε - σ_y / E)`. -/
def monotonic (ε : ℝ) : ℝ :=
  if ε ≤ m.σy / m.E then m.E * ε else m.σy + m.tangentModulus * (ε - m.σy / m.E)

/-- The monotonic loading curve is continuous (the two branches meet at the yield point). -/
theorem continuous_monotonic : Continuous m.monotonic := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
  intro ε hε
  have := m.E_pos.ne'
  rw [hε]; field_simp; ring

/-- Elastic slope `E` below the yield strain. -/
theorem hasDerivAt_monotonic_of_lt {ε₀ : ℝ} (h : ε₀ < m.σy / m.E) :
    HasDerivAt m.monotonic m.E ε₀ := by
  have heq : m.monotonic =ᶠ[𝓝 ε₀] fun ε => m.E * ε := by
    filter_upwards [Iio_mem_nhds h] with ε hε
    exact ite_eq_left (le_of_lt hε)
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using (hasDerivAt_id ε₀).const_mul m.E

/-- Elastoplastic slope `E H / (E + H)` beyond the yield strain. -/
theorem hasDerivAt_monotonic_of_gt {ε₀ : ℝ} (h : m.σy / m.E < ε₀) :
    HasDerivAt m.monotonic m.tangentModulus ε₀ := by
  have heq : m.monotonic =ᶠ[𝓝 ε₀] fun ε => m.σy + m.tangentModulus * (ε - m.σy / m.E) := by
    filter_upwards [Ioi_mem_nhds h] with ε hε
    exact ite_eq_right (not_le.mpr hε)
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using (((hasDerivAt_id ε₀).sub_const (m.σy / m.E)).const_mul
    m.tangentModulus).const_add m.σy

/-- The **virgin state** `ε = ε_p = α = 0`. -/
def virgin : State := ⟨0, 0, 0⟩

/-- Monotonic loading from the virgin state: a single return-mapping step from the virgin state
to any strain `ε ≥ 0` reproduces the monotonic loading curve. -/
theorem stress_returnMap_virgin {ε : ℝ} (hε : 0 ≤ ε) :
    m.stress (m.returnMap virgin ε) = m.monotonic ε := by
  have hE := m.E_pos
  have hEH := m.E_add_H_pos
  have hf : m.trialYield virgin ε = |m.E * ε| - m.σy := by
    simp [trialYield, yieldFn, trialStress, virgin]
  rw [abs_of_nonneg (mul_nonneg hE.le hε)] at hf
  by_cases h : ε ≤ m.σy / m.E
  · have h' : m.trialYield virgin ε ≤ 0 := by
      rw [hf]; rw [le_div_iff₀ hE] at h; linarith
    rw [stress_returnMap_of_nonpos m h', monotonic, ite_eq_left h]
    simp [trialStress, virgin]
  · have h' : 0 < m.trialYield virgin ε := by
      rw [hf]; rw [not_le, div_lt_iff₀ hE] at h; linarith
    have hy : 0 < m.σy / m.E := div_pos m.σy_pos hE
    have hpos : 0 < m.trialStress virgin ε := by
      simp only [trialStress, virgin, sub_zero]; exact mul_pos hE (by linarith [not_le.mp h])
    rw [stress_returnMap_of_pos m h', monotonic, ite_eq_right h, Real.sign_of_pos hpos, Δγ, hf,
      tangentModulus]
    simp only [trialStress, virgin, sub_zero]
    field_simp
    ring

end Bar

end Plasticity

/-! ### Associated von Mises flow and plastic incompressibility -/

namespace ContinuumMechanics.Lin

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]

/-- The deviator is orthogonal to spherical tensors: `dev σ : τ = dev σ : dev τ`. -/
theorem dev_dcontr_dev (σ τ : Lin V) : dev σ ⊡ dev τ = dev σ ⊡ τ := by
  conv_rhs => rw [← sph_add_dev τ]
  rw [map_add, dcontr_comm (dev σ) (sph τ), sph_dcontr_dev, zero_add]

/-- Expansion `J₂(σ + t τ) = J₂(σ) + t (dev σ : τ) + t² J₂(τ)`. -/
theorem J₂_add_smul (σ τ : Lin V) (t : ℝ) :
    J₂ (σ + t • τ) = J₂ σ + t * (dev σ ⊡ τ) + t ^ 2 * J₂ τ := by
  simp only [J₂, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [dcontr_comm (dev τ) (dev σ), dev_dcontr_dev σ τ]
  ring

/-- **Gradient of `J₂`**: the directional derivative of `J₂ = ½ s : s` at `σ` in the direction
`τ` is `s : τ`, `s = dev σ`; that is, `∂J₂/∂σ = dev σ`. -/
theorem hasDerivAt_J₂ (σ τ : Lin V) :
    HasDerivAt (fun t : ℝ => J₂ (σ + t • τ)) (dev σ ⊡ τ) 0 := by
  simp_rw [J₂_add_smul]
  have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (dev σ ⊡ τ)).const_add (J₂ σ)
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (J₂ τ)
  convert h1.add h2 using 1
  · funext t; simp
  · simp

/-- The von Mises **flow direction** `N = ∂σ_vM/∂σ = (3 / (2 σ_vM)) dev σ`. -/
def flowDir (σ : Lin V) : Lin V := (3 / (2 * vonMises σ)) • dev σ

/-- **Gradient of the von Mises function** `f(σ) = √(3 J₂(σ)) - σ_y` (away from `J₂ = 0`):
its directional derivative in the direction `τ` is `N : τ`, `N = (3 / (2 σ_vM)) dev σ`. In
particular the associated flow direction is proportional to the stress deviator. -/
theorem hasDerivAt_vonMises (σ τ : Lin V) (h : J₂ σ ≠ 0) (σy : ℝ) :
    HasDerivAt (fun t : ℝ => vonMises (σ + t • τ) - σy) (flowDir σ ⊡ τ) 0 := by
  have h3 : 3 * J₂ (σ + (0 : ℝ) • τ) ≠ 0 := by simpa using h
  have := ((hasDerivAt_J₂ σ τ).const_mul 3).sqrt h3
  refine (this.sub_const σy).congr_deriv ?_
  change _ = ((3 / (2 * √(3 * J₂ σ))) • dev σ) ⊡ τ
  rw [zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The flow direction is deviatoric. -/
theorem tr_flowDir (σ : Lin V) : tr (flowDir σ) = 0 := by
  rw [flowDir, map_smul, tr_dev, smul_zero]

/-- **Plastic incompressibility**: the associated plastic strain rate `ε̇_p = λ̇ N` is
traceless, `tr ε̇_p = 0`. -/
theorem tr_plasticRate (σ : Lin V) (lam : ℝ) : tr (lam • flowDir σ) = 0 := by
  rw [map_smul, tr_flowDir, smul_zero]

omit [Nontrivial V] in
/-- Normalisation of the von Mises flow direction: `N : N = 3/2`, so that the equivalent plastic
strain rate `√(⅔ ε̇_p : ε̇_p)` of `ε̇_p = λ̇ N` equals `|λ̇|`. -/
theorem flowDir_dcontr_self (σ : Lin V) (h : J₂ σ ≠ 0) : flowDir σ ⊡ flowDir σ = 3 / 2 := by
  have hJ : 0 < J₂ σ := lt_of_le_of_ne (J₂_nonneg σ) (Ne.symm h)
  have hss : dev σ ⊡ dev σ = 2 * J₂ σ := by rw [J₂]; ring
  have hvm : vonMises σ ^ 2 = 3 * J₂ σ := Real.sq_sqrt (by positivity)
  have hv : vonMises σ ≠ 0 := by
    intro h0; rw [h0] at hvm; linarith
  simp only [flowDir, map_smul, LinearMap.smul_apply, smul_eq_mul, hss]
  field_simp
  rw [hvm]

end ContinuumMechanics.Lin

/-! ### Maximum plastic dissipation -/

namespace Plasticity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **First-order convexity inequality**: a convex function lies above its tangent planes,
`f(σ*) ≥ f(σ) + ⟪∇f(σ), σ* - σ⟫`. -/
theorem le_of_convexOn_hasGradientAt {f : F → ℝ} {g σ : F} (hf : ConvexOn ℝ univ f)
    (hg : HasGradientAt f g σ) (σ' : F) : f σ + ⟪g, σ' - σ⟫_ℝ ≤ f σ' := by
  set ℓ : ℝ →ᵃ[ℝ] F := AffineMap.lineMap σ σ' with hℓ
  have hφ : ConvexOn ℝ univ (f ∘ ℓ) := by
    simpa using hf.comp_affineMap ℓ
  have hl : HasFDerivAt f (InnerProductSpace.toDual ℝ F g) (ℓ 0) := by
    rw [hℓ, AffineMap.lineMap_apply_zero]; exact hg.hasFDerivAt
  have hd := hl.comp_hasDerivAt (0 : ℝ)
    (AffineMap.hasDerivAt_lineMap (a := σ) (b := σ') (x := (0 : ℝ)))
  have := hφ.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp only [Function.comp_apply, InnerProductSpace.toDual_apply_apply, sub_zero,
    div_one] at this
  rw [hℓ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at this
  linarith

/-- **Principle of maximum plastic dissipation** (Hill; Drucker's inequality in convexity form):
if `f` is convex and differentiable at a stress `σ` on the yield surface `f(σ) = 0`, and the
plastic strain rate lies in the normal cone, `ε̇_p = λ̇ ∇f(σ)` with `λ̇ ≥ 0`, then
`(σ - σ*) : ε̇_p ≥ 0` for every plastically admissible stress `σ*` (`f(σ*) ≤ 0`). -/
theorem maxDissipation {f : F → ℝ} {g σ : F} (hf : ConvexOn ℝ univ f)
    (hg : HasGradientAt f g σ) (hσ : f σ = 0) {lam : ℝ} (hlam : 0 ≤ lam) {σ' : F}
    (hσ' : f σ' ≤ 0) : 0 ≤ ⟪σ - σ', lam • g⟫_ℝ := by
  have h := le_of_convexOn_hasGradientAt hf hg σ'
  rw [inner_smul_right, real_inner_comm]
  have : ⟪g, σ - σ'⟫_ℝ = -⟪g, σ' - σ⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  rw [this]
  exact mul_nonneg hlam (by linarith)

/-! ### Limit analysis of beams -/

/-- The elastic limit moment of a rectangular `b × h` section, `M_y = σ_y b h² / 6`. -/
def elasticLimitMoment (σy b h : ℝ) : ℝ := σy * b * h ^ 2 / 6

/-- The plastic moment of a rectangular `b × h` section, `M_p = σ_y b h² / 4`. -/
def plasticMoment (σy b h : ℝ) : ℝ := σy * b * h ^ 2 / 4

/-- At first yield the linear stress distribution `σ(y) = σ_y (2 y / h)` reaches `σ_y` at the
extreme fibre `y = h/2`. -/
theorem elastic_stress_extreme (σy h : ℝ) (hh : h ≠ 0) : σy * (2 * (h / 2) / h) = σy := by
  field_simp

/-- The **elastic limit moment** as the moment of the linear stress block at first yield:
`∫_{-h/2}^{h/2} σ_y (2y/h) y b dy = σ_y b h² / 6`. -/
theorem elastic_moment_integral (σy b h : ℝ) (hh : h ≠ 0) :
    ∫ y in -(h / 2)..h / 2, σy * (2 * y / h) * y * b = elasticLimitMoment σy b h := by
  have : (fun y : ℝ => σy * (2 * y / h) * y * b) = fun y => (2 * σy * b / h) * y ^ 2 := by
    funext y; ring
  rw [this, intervalIntegral.integral_const_mul, integral_pow, elasticLimitMoment]
  field_simp
  ring

/-- `sign y · y = |y|`. -/
theorem sign_mul_self_eq_abs (y : ℝ) : Real.sign y * y = |y| := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [Real.sign_of_neg hy, abs_of_neg hy]; ring
  · simp [hy]
  · rw [Real.sign_of_pos hy, abs_of_pos hy]; ring

/-- `∫_{-a}^{a} |y| dy = a²` for `a ≥ 0`. -/
theorem integral_abs_symm {a : ℝ} (ha : 0 ≤ a) : ∫ y in -a..a, |y| = a ^ 2 := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => |y|) MeasureTheory.volume u v :=
    fun u v => (continuous_abs).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-a) 0) (hi 0 a)]
  have h1 : ∫ y in -a..0, |y| = ∫ y in -a..0, -y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    exact abs_of_nonpos hy.2
  have h2 : ∫ y in (0 : ℝ)..a, |y| = ∫ y in (0 : ℝ)..a, y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le ha] at hy
    exact abs_of_nonneg hy.1
  rw [h1, h2, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

/-- The **plastic moment** as the moment of the fully plastic stress block
`σ(y) = σ_y sign y`: `∫_{-h/2}^{h/2} σ_y sign(y) y b dy = σ_y b h² / 4`. -/
theorem plastic_moment_integral (σy b h : ℝ) (hh : 0 ≤ h) :
    ∫ y in -(h / 2)..h / 2, σy * Real.sign y * y * b = plasticMoment σy b h := by
  have : (fun y : ℝ => σy * Real.sign y * y * b) = fun y => (σy * b) * |y| := by
    funext y; rw [mul_assoc σy, sign_mul_self_eq_abs]; ring
  rw [this, intervalIntegral.integral_const_mul, integral_abs_symm (by linarith), plasticMoment]
  ring

/-- The **shape factor** of a rectangular section: `M_p / M_y = 3/2`. -/
theorem shapeFactor_rect {σy b h : ℝ} (hσ : σy ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    plasticMoment σy b h / elasticLimitMoment σy b h = 3 / 2 := by
  unfold plasticMoment elasticLimitMoment
  field_simp
  ring

/-! #### Simply supported beam with a central point load -/

/-- The bending moment `M(x) = P x / 2` (`x ≤ L/2`), `P (L - x) / 2` (`x ≥ L/2`) of a simply
supported beam of span `L` under a central point load `P`; it is the unique equilibrium moment
field (the beam is statically determinate). -/
def ssMoment (P L x : ℝ) : ℝ := if x ≤ L / 2 then P * x / 2 else P * (L - x) / 2

/-- The moment vanishes at the left support. -/
theorem ssMoment_zero (P L : ℝ) (hL : 0 ≤ L) : ssMoment P L 0 = 0 := by
  rw [ssMoment, ite_eq_left (by linarith)]; ring

/-- The moment vanishes at the right support. -/
theorem ssMoment_L (P L : ℝ) (hL : 0 < L) : ssMoment P L L = 0 := by
  simp [ssMoment, not_le.mpr (half_lt_self hL)]

/-- Equilibrium left of the load: the shear force is `dM/dx = P/2`. -/
theorem hasDerivAt_ssMoment_left (P L : ℝ) {x : ℝ} (hx : x < L / 2) :
    HasDerivAt (ssMoment P L) (P / 2) x := by
  have heq : ssMoment P L =ᶠ[𝓝 x] fun y => P * y / 2 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact ite_eq_left hy.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using ((hasDerivAt_id x).const_mul P).div_const 2

/-- Equilibrium right of the load: the shear force is `dM/dx = -P/2`; the jump `P` in shear
balances the point load. -/
theorem hasDerivAt_ssMoment_right (P L : ℝ) {x : ℝ} (hx : L / 2 < x) :
    HasDerivAt (ssMoment P L) (-(P / 2)) x := by
  have heq : ssMoment P L =ᶠ[𝓝 x] fun y => P * (L - y) / 2 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact ite_eq_right (not_le.mpr hy)
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  exact ((((hasDerivAt_id x).const_sub L).const_mul P).div_const 2).congr_deriv (by ring)

/-- **Upper (kinematic) bound**, one-hinge mechanism: with a central hinge rotating by `2θ`
(`θ` at each support) and central deflection `δ = θ L / 2`, the virtual work equation
`P δ = M_p · 2θ` gives `P = 4 M_p / L`. -/
theorem ss_mechanism {P Mp L θ : ℝ} (hL : L ≠ 0) (hθ : θ ≠ 0) :
    P * (θ * L / 2) = Mp * (2 * θ) ↔ P = 4 * Mp / L := by
  constructor
  · intro h
    field_simp
    have : θ * (P * L - 4 * Mp) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hθ
    · linarith
  · rintro rfl
    field_simp
    ring

/-- **Lower (static) bound**: the equilibrium moment field satisfies the yield condition
`|M(x)| ≤ M_p` on the whole span iff `P ≤ 4 M_p / L`. -/
theorem ss_admissible_iff {P Mp L : ℝ} (hP : 0 ≤ P) (hL : 0 < L) :
    (∀ x ∈ Icc 0 L, |ssMoment P L x| ≤ Mp) ↔ P ≤ 4 * Mp / L := by
  rw [le_div_iff₀ hL]
  constructor
  · intro h
    have := h (L / 2) ⟨by linarith, by linarith⟩
    rw [ssMoment, ite_eq_left le_rfl, abs_of_nonneg (by positivity)] at this
    linarith
  · intro h x hx
    unfold ssMoment
    split_ifs with hxL
    · rw [abs_of_nonneg (by have := hx.1; positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hxL hP]
    · have hLx : 0 ≤ L - x := by linarith [hx.2]
      rw [abs_of_nonneg (by positivity)]
      have : L - x ≤ L / 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hP]

/-- **Collapse load of the simply supported beam**: `P_c = 4 M_p / L` is the mechanism (upper
bound) load, and it is the greatest statically and plastically admissible (lower bound) load;
the two bounds coincide, so `P_c` is exact. -/
theorem ss_collapse {Mp L : ℝ} (hMp : 0 ≤ Mp) (hL : 0 < L) :
    IsGreatest {P | 0 ≤ P ∧ ∀ x ∈ Icc 0 L, |ssMoment P L x| ≤ Mp} (4 * Mp / L) ∧
      ∀ θ ≠ 0, (4 * Mp / L) * (θ * L / 2) = Mp * (2 * θ) := by
  refine ⟨⟨⟨by positivity, (ss_admissible_iff (by positivity) hL).mpr le_rfl⟩, ?_⟩, ?_⟩
  · rintro P ⟨hP, h⟩
    exact (ss_admissible_iff hP hL).mp h
  · intro θ hθ
    exact (ss_mechanism hL.ne' hθ).mpr rfl

/-! #### Fixed–fixed beam with a uniformly distributed load -/

/-- External virtual work of a uniform load `q` on the three-hinge mechanism of a fixed–fixed
beam, whose deflection is `w(x) = θ min(x, L - x)` (central deflection `δ = θ L / 2`):
`∫₀ᴸ q w dx = q (L/2) δ = q θ L² / 4`. -/
theorem ff_external_work (q θ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (0 : ℝ)..L, q * (θ * min x (L - x)) = q * θ * L ^ 2 / 4 := by
  have hi : ∀ u v : ℝ,
      IntervalIntegrable (fun x : ℝ => q * (θ * min x (L - x))) MeasureTheory.volume u v :=
    fun u v => (by fun_prop : Continuous fun x : ℝ => q * (θ * min x (L - x))).intervalIntegrable
      u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (L / 2)) (hi (L / 2) L)]
  have h1 : ∫ x in (0 : ℝ)..L / 2, q * (θ * min x (L - x)) =
      ∫ x in (0 : ℝ)..L / 2, q * θ * x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [min_eq_left (by linarith [hx.2])]; ring
  have h2 : ∫ x in L / 2..L, q * (θ * min x (L - x)) =
      ∫ x in L / 2..L, q * θ * (L - x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [min_eq_right (by linarith [hx.1])]; ring
  rw [h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- **Upper (kinematic) bound**, three-hinge mechanism: hinges at both ends rotating by `θ` and
at midspan by `2θ` absorb internal work `M_p (θ + 2θ + θ) = 4 M_p θ`; equating with the external
work `q θ L² / 4` gives `q = 16 M_p / L²`. -/
theorem ff_mechanism {q Mp L θ : ℝ} (hL : L ≠ 0) (hθ : θ ≠ 0) :
    q * θ * L ^ 2 / 4 = Mp * (θ + 2 * θ + θ) ↔ q = 16 * Mp / L ^ 2 := by
  constructor
  · intro h
    field_simp
    have : θ * (q * L ^ 2 - 16 * Mp) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hθ
    · linarith
  · rintro rfl
    field_simp
    ring

/-- The general equilibrium moment field of a beam under a uniform load `q`:
`M(x) = q x (L - x) / 2 + a + b x`, the end moments `a`, `a + b L` being redundant. -/
def ffMoment (q a b L x : ℝ) : ℝ := q * x * (L - x) / 2 + a + b * x

/-- The shear force `V = dM/dx = q (L - 2x) / 2 + b`. -/
theorem hasDerivAt_ffMoment (q a b L x : ℝ) :
    HasDerivAt (ffMoment q a b L) (q * (L - 2 * x) / 2 + b) x := by
  have hM : ffMoment q a b L = fun y => q * L / 2 * y - q / 2 * y ^ 2 + a + b * y := by
    funext y; unfold ffMoment; ring
  rw [hM]
  have h1 := (hasDerivAt_id x).const_mul (q * L / 2)
  have h2 := ((hasDerivAt_id x).pow 2).const_mul (q / 2)
  have h3 := (hasDerivAt_id x).const_mul b
  exact (((h1.sub h2).add_const a).add h3).congr_deriv (by simp; ring)

/-- Equilibrium with the load: `d²M/dx² = dV/dx = -q`. -/
theorem hasDerivAt_ffShear (q b L x : ℝ) :
    HasDerivAt (fun y => q * (L - 2 * y) / 2 + b) (-q) x := by
  exact (((((hasDerivAt_id x).const_mul 2).const_sub L).const_mul q).div_const 2
    |>.add_const b).congr_deriv (by ring)

/-- **Static bound** for the fixed–fixed beam: if some equilibrium moment field satisfies
`|M| ≤ M_p` at both ends and at midspan, then `q ≤ 16 M_p / L²`, since
`M(L/2) - (M(0) + M(L)) / 2 = q L² / 8`. -/
theorem ff_static_bound {q a b Mp L : ℝ} (hL : 0 < L) (h0 : |ffMoment q a b L 0| ≤ Mp)
    (hm : |ffMoment q a b L (L / 2)| ≤ Mp) (h1 : |ffMoment q a b L L| ≤ Mp) :
    q ≤ 16 * Mp / L ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have key : ffMoment q a b L (L / 2) - (ffMoment q a b L 0 + ffMoment q a b L L) / 2 =
      q * L ^ 2 / 8 := by
    unfold ffMoment; ring
  have := abs_le.mp h0
  have := abs_le.mp hm
  have := abs_le.mp h1
  nlinarith

/-- At `q = 16 M_p / L²` the field `M(x) = q x (L - x) / 2 - M_p` (hogging `-M_p` at the ends,
sagging `M_p` at midspan) is statically admissible: `|M(x)| ≤ M_p` on the span. -/
theorem ff_collapse_field_admissible {Mp L : ℝ} (hMp : 0 ≤ Mp) (hL : 0 < L) :
    ∀ x ∈ Icc 0 L, |ffMoment (16 * Mp / L ^ 2) (-Mp) 0 L x| ≤ Mp := by
  intro x hx
  have hx0 : 0 ≤ x * (L - x) := mul_nonneg hx.1 (by linarith [hx.2])
  have hx1 : x * (L - x) ≤ L ^ 2 / 4 := by nlinarith [sq_nonneg (x - L / 2)]
  have hform : ffMoment (16 * Mp / L ^ 2) (-Mp) 0 L x = 8 * Mp * (x * (L - x)) / L ^ 2 - Mp := by
    unfold ffMoment; field_simp; ring
  rw [hform, abs_le]
  have hL2 : 0 < L ^ 2 := by positivity
  constructor
  · have : 0 ≤ 8 * Mp * (x * (L - x)) / L ^ 2 := by positivity
    linarith
  · have : 8 * Mp * (x * (L - x)) / L ^ 2 ≤ 2 * Mp := by
      rw [div_le_iff₀ hL2]; nlinarith
    linarith

/-- **Collapse load of the fixed–fixed beam**: `q_c = 16 M_p / L²` is the greatest load
carrying a statically and plastically admissible moment field (lower bound), and it satisfies
the three-hinge mechanism equation (upper bound); hence it is exact. -/
theorem ff_collapse {Mp L : ℝ} (hMp : 0 ≤ Mp) (hL : 0 < L) :
    IsGreatest {q | ∃ a b, ∀ x ∈ Icc 0 L, |ffMoment q a b L x| ≤ Mp} (16 * Mp / L ^ 2) ∧
      ∀ θ ≠ 0, (16 * Mp / L ^ 2) * θ * L ^ 2 / 4 = Mp * (θ + 2 * θ + θ) := by
  refine ⟨⟨⟨-Mp, 0, ff_collapse_field_admissible hMp hL⟩, ?_⟩, ?_⟩
  · rintro q ⟨a, b, h⟩
    exact ff_static_bound hL (h 0 ⟨le_rfl, hL.le⟩) (h (L / 2) ⟨by linarith, by linarith⟩)
      (h L ⟨hL.le, le_rfl⟩)
  · intro θ hθ
    exact (ff_mechanism hL.ne' hθ).mpr rfl

end Plasticity
