import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Rayleigh surface waves

An isotropic elastic half-space with Lamé moduli `λ`, `μ` and density `ρ` carries body waves
with speeds `c_L² = (λ + 2μ)/ρ` (longitudinal) and `c_T² = μ/ρ` (transverse), see
`Constitutive/Ellipticity` and `Elastostatics/PlaneWave`. Their squared ratio is

`κ² = c_T²/c_L² = μ/(λ + 2μ) = (1 - 2ν)/(2(1 - ν))`.

A **Rayleigh wave** travels along the traction-free surface with speed `c = ξ c_T`, its potentials
decaying like `exp(-k √(1 - κ²ξ²) z)` and `exp(-k √(1 - ξ²) z)` with depth; the traction-free
conditions have a nonzero solution iff `ξ` is a root of the **Rayleigh secular function**

`R(ξ) = (2 - ξ²)² - 4 √(1 - ξ²) √(1 - κ²ξ²)`

([Achenbach1973], §5.11). Here `κ²` is a real parameter `k`.

## Main results

* `RayleighWave.kappaSq_eq_poisson`: `μ/(λ + 2μ) = (1 - 2ν)/(2(1 - ν))`, `ν = λ/(2(λ + μ))`;
  `RayleighWave.kappaSqNu_mem_of_nonneg` (`κ² ∈ (0, 1/2]` for `ν ∈ [0, 1/2)`),
  `RayleighWave.kappaSqNu_mem` (`κ² ∈ (0, 3/4)` for `ν ∈ (-1, 1/2)`),
  `RayleighWave.kappaSq_mem` (`κ² ∈ (0, 3/4)` for `μ > 0`, `3λ + 2μ > 0`).
* (a) `RayleighWave.secular_zero` (`R(0) = 0`), `RayleighWave.secular_one` (`R(1) = 1`),
  `RayleighWave.tendsto_secular_div_sq` (`R(ξ)/ξ² → -2(1 - κ²)` as `ξ → 0⁺`),
  `RayleighWave.secular_neg_of_sq_le` (`R(ξ) < 0` for `0 < ξ² ≤ (1 - κ²)/2`) and
  `RayleighWave.exists_secular_root` (a root `ξ_R ∈ (0, 1)` for `κ² < 1`).
* (b) `RayleighWave.rationalize`: `(2 - s)⁴ - 16(1 - s)(1 - κ² s) = s · C(s)` with the
  **Rayleigh cubic** `C(s) = s³ - 8s² + (24 - 16κ²)s - 16(1 - κ²)`;
  `RayleighWave.secular_eq_zero_iff` (`R(ξ) = 0 ↔ C(ξ²) = 0` on `(0, 1)`, and likewise for the
  signs), `RayleighWave.cubic_root_unique` (at most one root of `C` in `(0, 1)`, for every `κ²`)
  and `RayleighWave.existsUnique_secular_root` (exactly one root of `R` in `(0, 1)` for
  `κ² < 1`). The cubic need not be monotone on `[0, 1]`; uniqueness instead follows since
  `C(s) = 0` iff `16κ² = s² - 7s + 17 - 1/(1 - s)`, a strictly decreasing function of `s`.
* `RayleighWave.rayleigh_wave_exists`: for `μ > 0`, `λ + μ > 0`, `ρ > 0` there is a unique
  `c_R ∈ (0, c_T)` with `R(c_R/c_T) = 0`: the Rayleigh wave is slower than the shear wave
  (and `RayleighWave.cT_lt_cL`: `c_T < c_L`).
* (c) **Poisson solid** (`λ = μ`, `ν = 1/4`, `κ² = 1/3`): `RayleighWave.poisson_cubic_factor`
  (`3 C(s) = (s - 4)(3s² - 12s + 8)`); the root `s_R = 2 - 2/√3` (`RayleighWave.poissonRootSq`)
  lies in `(0, 1)`, `ξ_R = √s_R` (`RayleighWave.poissonRoot`) satisfies the unrationalised
  equation `R(ξ_R) = 0` (`RayleighWave.secular_poissonRoot`), it is the only root in `(0, 1)`
  (`RayleighWave.poissonRoot_unique`) and `0.919 < ξ_R < 0.920`
  (`RayleighWave.poissonRoot_bounds`), i.e. `c_R ≈ 0.9194 c_T`.
* (d) `RayleighWave.potential_wave_eq`: `φ = e^{-K a y} cos K(x - ct)` solves the wave equation
  with speed `c₀` when `a² = 1 - c²/c₀²`; `RayleighWave.rayleigh_decay_rates` (the Rayleigh
  decay rates `√(1 - κ²ξ²)`, `√(1 - ξ²)` are positive and match the longitudinal and shear
  speeds) and `RayleighWave.tendsto_potential` (exponential decay with depth).

## References

* [Achenbach1973] J. D. Achenbach, *Wave Propagation in Elastic Solids*, §5.11.
* [Rayleigh1885] Lord Rayleigh, *On waves propagated along the plane surface of an elastic
  solid*, Proc. London Math. Soc. 17 (1885).
-/

open Real Set Filter Topology

noncomputable section

namespace ContinuumMechanics.RayleighWave

/-! ### The speed ratio `κ²` -/

/-- The squared ratio `κ² = c_T²/c_L² = μ/(λ + 2μ)` of the shear and longitudinal speeds. -/
def kappaSq (lam μ : ℝ) : ℝ := μ / (lam + 2 * μ)

/-- `κ²` as a function of Poisson's ratio: `(1 - 2ν)/(2(1 - ν))`. -/
def kappaSqNu (ν : ℝ) : ℝ := (1 - 2 * ν) / (2 * (1 - ν))

/-- `c_T² / c_L² = (μ/ρ) / ((λ + 2μ)/ρ) = κ²`. -/
theorem speed_ratio {lam μ ρ : ℝ} (hρ : 0 < ρ) :
    (μ / ρ) / ((lam + 2 * μ) / ρ) = kappaSq lam μ := by
  unfold kappaSq
  rw [div_div_div_cancel_right₀ hρ.ne']

/-- `μ/(λ + 2μ) = (1 - 2ν)/(2(1 - ν))` with Poisson's ratio `ν = λ/(2(λ + μ))`. -/
theorem kappaSq_eq_poisson {lam μ : ℝ} (h1 : lam + μ ≠ 0) :
    kappaSq lam μ = kappaSqNu (lam / (2 * (lam + μ))) := by
  unfold kappaSq kappaSqNu
  have e1 : 1 - 2 * (lam / (2 * (lam + μ))) = μ / (lam + μ) := by
    field_simp; ring
  have e2 : 2 * (1 - lam / (2 * (lam + μ))) = (lam + 2 * μ) / (lam + μ) := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ h1]

/-- For `ν ∈ [0, 1/2)`, `κ² ∈ (0, 1/2]`. -/
theorem kappaSqNu_mem_of_nonneg {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν < 1 / 2) :
    kappaSqNu ν ∈ Ioc 0 (1 / 2) := by
  unfold kappaSqNu
  have hd : 0 < 2 * (1 - ν) := by linarith
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [div_le_iff₀ hd]
  linarith

/-- For `ν ∈ (-1, 1/2)`, `κ² ∈ (0, 3/4)`. -/
theorem kappaSqNu_mem {ν : ℝ} (h0 : -1 < ν) (h1 : ν < 1 / 2) :
    kappaSqNu ν ∈ Ioo 0 (3 / 4) := by
  unfold kappaSqNu
  have hd : 0 < 2 * (1 - ν) := by linarith
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [div_lt_iff₀ hd]
  linarith

/-- For `μ > 0` and positive bulk modulus (`3λ + 2μ > 0`), `κ² ∈ (0, 3/4)`. -/
theorem kappaSq_mem {lam μ : ℝ} (hμ : 0 < μ) (hK : 0 < 3 * lam + 2 * μ) :
    kappaSq lam μ ∈ Ioo 0 (3 / 4) := by
  unfold kappaSq
  have hd : 0 < lam + 2 * μ := by linarith
  refine ⟨div_pos hμ hd, ?_⟩
  rw [div_lt_iff₀ hd]
  linarith

/-- For `μ > 0` and `λ + μ > 0`, `κ² ∈ (0, 1)`. -/
theorem kappaSq_mem_Ioo_one {lam μ : ℝ} (hμ : 0 < μ) (hlm : 0 < lam + μ) :
    kappaSq lam μ ∈ Ioo 0 1 := by
  unfold kappaSq
  have hd : 0 < lam + 2 * μ := by linarith
  refine ⟨div_pos hμ hd, ?_⟩
  rw [div_lt_iff₀ hd]
  linarith

/-- The shear wave is slower than the longitudinal wave: `c_T < c_L` for `λ + μ > 0`. -/
theorem cT_lt_cL {lam μ ρ : ℝ} (hμ : 0 < μ) (hlm : 0 < lam + μ) (hρ : 0 < ρ) :
    √(μ / ρ) < √((lam + 2 * μ) / ρ) :=
  sqrt_lt_sqrt (div_pos hμ hρ).le (div_lt_div_of_pos_right (by linarith) hρ)

/-! ### The secular function and the Rayleigh cubic -/

/-- The **Rayleigh secular function** `R(ξ) = (2 - ξ²)² - 4 √(1 - ξ²) √(1 - κ²ξ²)`. -/
def secular (k ξ : ℝ) : ℝ := (2 - ξ ^ 2) ^ 2 - 4 * √(1 - ξ ^ 2) * √(1 - k * ξ ^ 2)

/-- The **Rayleigh cubic** `C(s) = s³ - 8s² + (24 - 16κ²)s - 16(1 - κ²)`. -/
def cubic (k s : ℝ) : ℝ := s ^ 3 - 8 * s ^ 2 + (24 - 16 * k) * s - 16 * (1 - k)

/-- The conjugate factor `(2 - ξ²)² + 4 √(1 - ξ²) √(1 - κ²ξ²)`, used to rationalise `R`. -/
def conjFactor (k ξ : ℝ) : ℝ := (2 - ξ ^ 2) ^ 2 + 4 * √(1 - ξ ^ 2) * √(1 - k * ξ ^ 2)

/-- `R(0) = 0`: the trivial root. -/
theorem secular_zero (k : ℝ) : secular k 0 = 0 := by
  simp [secular]
  norm_num

/-- `R(1) = 1`. -/
theorem secular_one (k : ℝ) : secular k 1 = 1 := by
  norm_num [secular]

/-- `C(0) = -16(1 - κ²)`. -/
theorem cubic_zero (k : ℝ) : cubic k 0 = -16 * (1 - k) := by
  simp [cubic]

/-- `C(1) = 1`. -/
theorem cubic_one (k : ℝ) : cubic k 1 = 1 := by
  simp only [cubic]
  ring

/-- **Rationalisation identity**: `(2 - s)⁴ - 16(1 - s)(1 - κ²s) = s · C(s)`. -/
theorem rationalize (k s : ℝ) : (2 - s) ^ 4 - 16 * (1 - s) * (1 - k * s) = s * cubic k s := by
  unfold cubic
  ring

/-- `R(ξ) · (conjugate) = ξ² C(ξ²)` whenever both square roots have nonnegative arguments. -/
theorem secular_mul_conjFactor {k ξ : ℝ} (h1 : ξ ^ 2 ≤ 1) (h2 : k * ξ ^ 2 ≤ 1) :
    secular k ξ * conjFactor k ξ = ξ ^ 2 * cubic k (ξ ^ 2) := by
  rw [← rationalize]
  have a := sq_sqrt (sub_nonneg.mpr h1)
  have b := sq_sqrt (sub_nonneg.mpr h2)
  unfold secular conjFactor
  linear_combination (-16 * (1 - k * ξ ^ 2)) * a - 16 * (√(1 - ξ ^ 2)) ^ 2 * b

/-- The conjugate factor is positive for `ξ² < 2`. -/
theorem conjFactor_pos {k ξ : ℝ} (h1 : ξ ^ 2 < 2) : 0 < conjFactor k ξ := by
  unfold conjFactor
  have h : 0 < 2 - ξ ^ 2 := by linarith
  have : 0 < (2 - ξ ^ 2) ^ 2 := by positivity
  have : 0 ≤ 4 * √(1 - ξ ^ 2) * √(1 - k * ξ ^ 2) := by positivity
  linarith

/-- `κ² ξ² ≤ 1` for `κ² ≤ 1` and `ξ² ≤ 1`. -/
theorem mul_sq_le_one {k ξ : ℝ} (hk : k ≤ 1) (h1 : ξ ^ 2 ≤ 1) : k * ξ ^ 2 ≤ 1 := by
  have := sq_nonneg ξ
  rcases le_total 0 k with h | h <;> nlinarith

/-- On `(0, 1)`, `R(ξ) = ξ² C(ξ²) / (conjugate)`. -/
theorem secular_eq {k ξ : ℝ} (hk : k ≤ 1) (hξ : ξ ∈ Ioo 0 1) :
    secular k ξ = ξ ^ 2 * cubic k (ξ ^ 2) / conjFactor k ξ := by
  have h1 : ξ ^ 2 ≤ 1 := by nlinarith [hξ.1, hξ.2]
  rw [eq_div_iff (conjFactor_pos (by linarith)).ne',
    secular_mul_conjFactor h1 (mul_sq_le_one hk h1)]

/-- On `(0, 1)`, `R(ξ) = 0 ↔ C(ξ²) = 0`. -/
theorem secular_eq_zero_iff {k ξ : ℝ} (hk : k ≤ 1) (hξ : ξ ∈ Ioo 0 1) :
    secular k ξ = 0 ↔ cubic k (ξ ^ 2) = 0 := by
  have hs : 0 < ξ ^ 2 := pow_pos hξ.1 2
  rw [secular_eq hk hξ, div_eq_zero_iff, mul_eq_zero]
  have := (conjFactor_pos (k := k) (ξ := ξ) (by nlinarith [hξ.1, hξ.2])).ne'
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hs.ne'
    · exact h
    · exact absurd h this
  · exact fun h => Or.inl (Or.inr h)

/-- On `(0, 1)`, `R(ξ) < 0 ↔ C(ξ²) < 0`. -/
theorem secular_neg_iff {k ξ : ℝ} (hk : k ≤ 1) (hξ : ξ ∈ Ioo 0 1) :
    secular k ξ < 0 ↔ cubic k (ξ ^ 2) < 0 := by
  have hs : 0 < ξ ^ 2 := pow_pos hξ.1 2
  rw [secular_eq hk hξ, div_neg_iff]
  have := conjFactor_pos (k := k) (ξ := ξ) (by nlinarith [hξ.1, hξ.2])
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · by_contra hc
      push Not at hc
      nlinarith
  · exact fun h => Or.inr ⟨by nlinarith, this⟩

/-- On `(0, 1)`, `0 < R(ξ) ↔ 0 < C(ξ²)`. -/
theorem secular_pos_iff {k ξ : ℝ} (hk : k ≤ 1) (hξ : ξ ∈ Ioo 0 1) :
    0 < secular k ξ ↔ 0 < cubic k (ξ ^ 2) := by
  have hs : 0 < ξ ^ 2 := pow_pos hξ.1 2
  rw [secular_eq hk hξ, div_pos_iff]
  have := conjFactor_pos (k := k) (ξ := ξ) (by nlinarith [hξ.1, hξ.2])
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · by_contra hc
      push Not at hc
      nlinarith
    · linarith
  · exact fun h => Or.inl ⟨by positivity, this⟩

/-! ### (a) Existence of a root in `(0, 1)` -/

/-- **Small-`ξ` expansion**: `R(ξ)/ξ² → -2(1 - κ²)` as `ξ → 0⁺`, i.e.
`R(ξ) = -2(1 - κ²)ξ² + o(ξ²)`. -/
theorem tendsto_secular_div_sq {k : ℝ} (hk : k ≤ 1) :
    Tendsto (fun ξ => secular k ξ / ξ ^ 2) (𝓝[>] 0) (𝓝 (-2 * (1 - k))) := by
  have hc : ContinuousAt (fun ξ => cubic k (ξ ^ 2) / conjFactor k ξ) 0 := by
    have h1 : Continuous fun ξ : ℝ => cubic k (ξ ^ 2) := by
      unfold cubic
      fun_prop
    have h2 : Continuous (conjFactor k) := by
      unfold conjFactor
      fun_prop
    exact h1.continuousAt.div h2.continuousAt (conjFactor_pos (by norm_num)).ne'
  have hv : cubic k ((0 : ℝ) ^ 2) / conjFactor k 0 = -2 * (1 - k) := by
    simp [cubic, conjFactor]
    norm_num
    ring
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [hv] at ht
  refine ht.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ξ hξ
  rw [secular_eq hk hξ, mul_div_assoc, mul_div_cancel_left₀ _ (pow_pos hξ.1 2).ne']

/-- `R(ξ) < 0` for `0 < ξ` with `ξ² ≤ (1 - κ²)/2` (and `0 ≤ κ² < 1`): an explicit interval of
negativity near the trivial root. -/
theorem secular_neg_of_sq_le {k ξ : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hξ : 0 < ξ)
    (hs : ξ ^ 2 ≤ (1 - k) / 2) : secular k ξ < 0 := by
  have h1 : ξ < 1 := by nlinarith
  rw [secular_neg_iff hk.le ⟨hξ, h1⟩]
  have hs0 : 0 < ξ ^ 2 := pow_pos hξ 2
  have hs1 : ξ ^ 2 ≤ 1 := by linarith
  generalize ξ ^ 2 = s at hs hs0 hs1
  have h3 : s ^ 3 ≤ s := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0.le]
  unfold cubic
  nlinarith [mul_nonneg hk0 hs0.le, sq_nonneg s]

/-- A root of the Rayleigh cubic in `(0, 1)` exists for `κ² < 1` (intermediate value theorem:
`C(0) < 0 < C(1)`). -/
theorem exists_cubic_root {k : ℝ} (hk : k < 1) : ∃ s ∈ Ioo 0 1, cubic k s = 0 := by
  have hcont : ContinuousOn (cubic k) (Icc 0 1) := by
    unfold cubic
    fun_prop
  have h := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont
  rw [cubic_zero, cubic_one] at h
  exact h ⟨by linarith, by norm_num⟩

/-- **Existence of a Rayleigh wave**: for `κ² < 1` the secular function has a root
`ξ_R ∈ (0, 1)`. -/
theorem exists_secular_root {k : ℝ} (hk : k < 1) : ∃ ξ ∈ Ioo 0 1, secular k ξ = 0 := by
  obtain ⟨s, hs, hs0⟩ := exists_cubic_root hk
  have hξ : √s ∈ Ioo 0 1 :=
    ⟨sqrt_pos.mpr hs.1, (sqrt_lt' one_pos).mpr (by simpa using hs.2)⟩
  refine ⟨√s, hξ, (secular_eq_zero_iff hk.le hξ).mpr ?_⟩
  rwa [sq_sqrt hs.1.le]

/-! ### (b) Uniqueness of the root in `(0, 1)` -/

/-- Eliminating `κ²` between two roots `s₁, s₂` of the cubic. -/
theorem cubic_elim (k s₁ s₂ : ℝ) :
    (1 - s₂) * cubic k s₁ - (1 - s₁) * cubic k s₂ =
      (s₂ - s₁) * ((1 - s₁) * (1 - s₂) * (s₁ + s₂ - 7) - 1) := by
  unfold cubic
  ring

/-- **Uniqueness**: for every `κ²`, the Rayleigh cubic has at most one root in `(0, 1)`.
(Equivalently `16κ² = s² - 7s + 17 - 1/(1 - s)`, strictly decreasing in `s`.) -/
theorem cubic_root_unique {k s₁ s₂ : ℝ} (h₁ : s₁ ∈ Ioo 0 1) (h₂ : s₂ ∈ Ioo 0 1)
    (e₁ : cubic k s₁ = 0) (e₂ : cubic k s₂ = 0) : s₁ = s₂ := by
  have h := cubic_elim k s₁ s₂
  rw [e₁, e₂, mul_zero, mul_zero, sub_zero, eq_comm, mul_eq_zero] at h
  rcases h with h | h
  · linarith
  · have : 0 < (1 - s₁) * (1 - s₂) := mul_pos (by linarith [h₁.2]) (by linarith [h₂.2])
    nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **Existence and uniqueness of the Rayleigh root**: for `κ² < 1` the secular function has
exactly one root in `(0, 1)`. -/
theorem existsUnique_secular_root {k : ℝ} (hk : k < 1) :
    ∃! ξ, ξ ∈ Ioo 0 1 ∧ secular k ξ = 0 := by
  obtain ⟨ξ, hξ, h0⟩ := exists_secular_root hk
  refine ⟨ξ, ⟨hξ, h0⟩, fun η ⟨hη, h1⟩ => ?_⟩
  have hs : ∀ x ∈ Ioo (0 : ℝ) 1, x ^ 2 ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨pow_pos hx.1 2, by nlinarith [hx.1, hx.2]⟩
  have := cubic_root_unique (hs η hη) (hs ξ hξ) ((secular_eq_zero_iff hk.le hη).mp h1)
    ((secular_eq_zero_iff hk.le hξ).mp h0)
  exact (pow_left_inj₀ hη.1.le hξ.1.le two_ne_zero).mp this

/-- **The Rayleigh wave is slower than the shear wave**: for `μ > 0`, `λ + μ > 0`, `ρ > 0`
there is exactly one speed `c_R ∈ (0, c_T)`, `c_T = √(μ/ρ)`, with `R(c_R / c_T) = 0`. -/
theorem rayleigh_wave_exists {lam μ ρ : ℝ} (hμ : 0 < μ) (hlm : 0 < lam + μ) (hρ : 0 < ρ) :
    ∃! c, c ∈ Ioo 0 √(μ / ρ) ∧ secular (kappaSq lam μ) (c / √(μ / ρ)) = 0 := by
  have hT : 0 < √(μ / ρ) := sqrt_pos.mpr (div_pos hμ hρ)
  obtain ⟨ξ, ⟨hξ, h0⟩, hu⟩ := existsUnique_secular_root (kappaSq_mem_Ioo_one hμ hlm).2
  refine ⟨ξ * √(μ / ρ), ⟨⟨mul_pos hξ.1 hT, ?_⟩, ?_⟩, ?_⟩
  · nlinarith [hξ.2]
  · rwa [mul_div_cancel_right₀ _ hT.ne']
  · rintro c ⟨⟨hc0, hc1⟩, hc⟩
    have := hu (c / √(μ / ρ)) ⟨⟨div_pos hc0 hT, (div_lt_one hT).mpr hc1⟩, hc⟩
    rw [← this, div_mul_cancel₀ _ hT.ne']

/-! ### (c) The Poisson solid -/

/-- For the Poisson solid `λ = μ`: `κ² = 1/3`. -/
theorem kappaSq_poisson_solid {μ : ℝ} (hμ : μ ≠ 0) : kappaSq μ μ = 1 / 3 := by
  unfold kappaSq
  field_simp
  ring

/-- For the Poisson solid `λ = μ`: `ν = 1/4`. -/
theorem poisson_ratio_poisson_solid {μ : ℝ} (hμ : μ ≠ 0) : μ / (2 * (μ + μ)) = 1 / 4 := by
  field_simp
  ring

/-- **Factorisation** for `κ² = 1/3`: `3 C(s) = (s - 4)(3s² - 12s + 8)`. -/
theorem poisson_cubic_factor (s : ℝ) :
    3 * cubic (1 / 3) s = (s - 4) * (3 * s ^ 2 - 12 * s + 8) := by
  unfold cubic
  ring

/-- The Rayleigh root for the Poisson solid in `s = ξ²`: `s_R = 2 - 2/√3 = 2 - 2√3/3`. -/
def poissonRootSq : ℝ := 2 - 2 * √3 / 3

/-- `1.732 < √3 < 1.7321`. -/
theorem sqrt_three_bounds : 1.732 < √3 ∧ √3 < 1.7321 :=
  ⟨(lt_sqrt (by norm_num)).mpr (by norm_num), (sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

/-- `0.84526 < s_R < 0.84534`; in particular `s_R ∈ (0, 1)`. -/
theorem poissonRootSq_bounds : 0.84526 < poissonRootSq ∧ poissonRootSq < 0.84534 := by
  obtain ⟨h1, h2⟩ := sqrt_three_bounds
  unfold poissonRootSq
  constructor <;> linarith

/-- `s_R ∈ (0, 1)`. -/
theorem poissonRootSq_mem : poissonRootSq ∈ Ioo 0 1 := by
  obtain ⟨h1, h2⟩ := poissonRootSq_bounds
  constructor <;> linarith

/-- `s_R` is a root of the Rayleigh cubic for `κ² = 1/3` (a root of `3s² - 12s + 8`). -/
theorem cubic_poissonRootSq : cubic (1 / 3) poissonRootSq = 0 := by
  have h3 : 3 * poissonRootSq ^ 2 - 12 * poissonRootSq + 8 = 0 := by
    unfold poissonRootSq
    linear_combination (4 / 3 : ℝ) * sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have := poisson_cubic_factor poissonRootSq
  rw [h3, mul_zero] at this
  linarith

/-- The other two roots `4` and `2 + 2/√3` of the cubic lie outside `(0, 1)` (spurious roots
introduced by rationalisation). -/
theorem poisson_spurious_roots : (1 : ℝ) < 4 ∧ 1 < 2 + 2 * √3 / 3 := by
  have := sqrt_three_bounds.1
  constructor <;> linarith

/-- The Rayleigh root for the Poisson solid: `ξ_R = √(2 - 2/√3) ≈ 0.9194`. -/
def poissonRoot : ℝ := √poissonRootSq

/-- `ξ_R² = s_R`. -/
theorem poissonRoot_sq : poissonRoot ^ 2 = poissonRootSq :=
  sq_sqrt poissonRootSq_mem.1.le

/-- **Numerical bounds**: `0.919 < ξ_R < 0.920`, i.e. `c_R ≈ 0.9194 c_T`. -/
theorem poissonRoot_bounds : 0.919 < poissonRoot ∧ poissonRoot < 0.920 := by
  obtain ⟨h1, h2⟩ := poissonRootSq_bounds
  exact ⟨(lt_sqrt (by norm_num)).mpr (by linarith), (sqrt_lt' (by norm_num)).mpr (by linarith)⟩

/-- `ξ_R ∈ (0, 1)`. -/
theorem poissonRoot_mem : poissonRoot ∈ Ioo 0 1 := by
  obtain ⟨h1, h2⟩ := poissonRoot_bounds
  constructor <;> linarith

/-- `ξ_R` solves the **unrationalised** Rayleigh equation
`(2 - ξ²)² = 4 √(1 - ξ²) √(1 - ξ²/3)`. -/
theorem secular_poissonRoot : secular (1 / 3) poissonRoot = 0 := by
  rw [secular_eq_zero_iff (by norm_num) poissonRoot_mem, poissonRoot_sq]
  exact cubic_poissonRootSq

/-- `ξ_R` is the only root of the secular function in `(0, 1)` for `κ² = 1/3`. -/
theorem poissonRoot_unique {ξ : ℝ} (hξ : ξ ∈ Ioo 0 1) (h : secular (1 / 3) ξ = 0) :
    ξ = poissonRoot :=
  (existsUnique_secular_root (by norm_num : (1 / 3 : ℝ) < 1)).unique ⟨hξ, h⟩
    ⟨poissonRoot_mem, secular_poissonRoot⟩

/-- **Rayleigh speed of a Poisson solid** (`λ = μ > 0`, `ρ > 0`): `c_R = ξ_R c_T` is the unique
speed in `(0, c_T)` solving the secular equation, and `0.919 c_T < c_R < 0.920 c_T`. -/
theorem poisson_solid_rayleigh_speed {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {c : ℝ}
    (hc : c ∈ Ioo 0 √(μ / ρ)) (h : secular (kappaSq μ μ) (c / √(μ / ρ)) = 0) :
    c = poissonRoot * √(μ / ρ) ∧ 0.919 * √(μ / ρ) < c ∧ c < 0.920 * √(μ / ρ) := by
  have hT : 0 < √(μ / ρ) := sqrt_pos.mpr (div_pos hμ hρ)
  rw [kappaSq_poisson_solid hμ.ne'] at h
  have hξ := poissonRoot_unique ⟨div_pos hc.1 hT, (div_lt_one hT).mpr hc.2⟩ h
  have hc' : c = poissonRoot * √(μ / ρ) := by rw [← hξ, div_mul_cancel₀ _ hT.ne']
  obtain ⟨b1, b2⟩ := poissonRoot_bounds
  refine ⟨hc', ?_, ?_⟩ <;> rw [hc'] <;> nlinarith

/-! ### (d) Decay with depth -/

/-- A decaying travelling potential `φ(x, y, t) = e^{-K a y} cos(K(x - c t))`. -/
def potential (K a c x y t : ℝ) : ℝ := exp (-(K * a) * y) * cos (K * (x - c * t))

/-- `∂²φ/∂x² = -K² φ`. -/
theorem deriv2_x (K a c y t x : ℝ) :
    deriv (deriv fun x' => potential K a c x' y t) x = -K ^ 2 * potential K a c x y t := by
  have h1 : deriv (fun x' => potential K a c x' y t) =
      fun x' => -(exp (-(K * a) * y) * K) * sin (K * (x' - c * t)) := by
    funext x'
    unfold potential
    have := (((hasDerivAt_id' x').sub_const (c * t)).const_mul K).cos.const_mul (exp (-(K * a) * y))
    rw [this.deriv]
    simp; ring
  rw [h1]
  have := (((hasDerivAt_id' x).sub_const (c * t)).const_mul K).sin.const_mul
    (-(exp (-(K * a) * y) * K))
  rw [this.deriv]
  unfold potential
  simp; ring

/-- `∂²φ/∂t² = -(Kc)² φ`. -/
theorem deriv2_t (K a c x y t : ℝ) :
    deriv (deriv fun t' => potential K a c x y t') t = -(K * c) ^ 2 * potential K a c x y t := by
  have h1 : deriv (fun t' => potential K a c x y t') =
      fun t' => exp (-(K * a) * y) * (K * c * sin (K * (x - c * t'))) := by
    funext t'
    unfold potential
    have := ((((hasDerivAt_id' t').const_mul c).const_sub x).const_mul K).cos.const_mul
      (exp (-(K * a) * y))
    rw [this.deriv]
    simp; ring
  rw [h1]
  have := (((((hasDerivAt_id' t).const_mul c).const_sub x).const_mul K).sin.const_mul
    (K * c)).const_mul (exp (-(K * a) * y))
  rw [this.deriv]
  unfold potential
  simp; ring

/-- `∂²φ/∂y² = (Ka)² φ`. -/
theorem deriv2_y (K a c x t y : ℝ) :
    deriv (deriv fun y' => potential K a c x y' t) y = (K * a) ^ 2 * potential K a c x y t := by
  have h1 : deriv (fun y' => potential K a c x y' t) =
      fun y' => -(K * a) * exp (-(K * a) * y') * cos (K * (x - c * t)) := by
    funext y'
    unfold potential
    have := (((hasDerivAt_id' y').const_mul (-(K * a))).exp).mul_const (cos (K * (x - c * t)))
    rw [this.deriv]
    ring
  rw [h1]
  have := ((((hasDerivAt_id' y).const_mul (-(K * a))).exp).const_mul (-(K * a))).mul_const
    (cos (K * (x - c * t)))
  rw [this.deriv]
  unfold potential
  simp; ring

/-- **The decaying potential solves the wave equation** `φ_xx + φ_yy = φ_tt / c₀²` iff the decay
rate satisfies `a² = 1 - c²/c₀²` (sufficiency). -/
theorem potential_wave_eq {K a c c₀ : ℝ} (ha : a ^ 2 = 1 - c ^ 2 / c₀ ^ 2) (x y t : ℝ) :
    deriv (deriv fun x' => potential K a c x' y t) x +
        deriv (deriv fun y' => potential K a c x y' t) y =
      1 / c₀ ^ 2 * deriv (deriv fun t' => potential K a c x y t') t := by
  rw [deriv2_x, deriv2_y, deriv2_t]
  linear_combination K ^ 2 * potential K a c x y t * ha

/-- **Exponential decay with depth**: for `K a > 0`, `φ(x, y, t) → 0` as `y → ∞`. -/
theorem tendsto_potential {K a : ℝ} (h : 0 < K * a) (c x t : ℝ) :
    Tendsto (fun y => potential K a c x y t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => -(K * a) * y) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h2 := (tendsto_exp_atBot.comp h1).mul_const (cos (K * (x - c * t)))
  rw [zero_mul] at h2
  exact h2

/-- **Rayleigh potentials** (`0 < κ² ≤ 1`, `ξ ∈ (0, 1)`, `c_T > 0`, `c = ξ c_T`,
`c_L² = c_T²/κ²`): the decay rates `p = √(1 - κ²ξ²)` and `q = √(1 - ξ²)` are positive and
`p² = 1 - c²/c_L²`, `q² = 1 - c²/c_T²`, so the longitudinal potential `e^{-Kpy} cos K(x - ct)`
and the shear potential `e^{-Kqy} cos K(x - ct)` solve the wave equations with speeds `c_L`
and `c_T` (`potential_wave_eq`) and decay exponentially with depth for `K > 0`
(`tendsto_potential`). The surface wave is possible only for `ξ < 1`. -/
theorem rayleigh_decay_rates {k ξ cT : ℝ} (hk0 : 0 < k) (hk : k ≤ 1) (hξ : ξ ∈ Ioo 0 1)
    (hT : 0 < cT) :
    0 < √(1 - k * ξ ^ 2) ∧ 0 < √(1 - ξ ^ 2) ∧
      √(1 - k * ξ ^ 2) ^ 2 = 1 - (ξ * cT) ^ 2 / (cT / √k) ^ 2 ∧
      √(1 - ξ ^ 2) ^ 2 = 1 - (ξ * cT) ^ 2 / cT ^ 2 := by
  have h1 : ξ ^ 2 < 1 := by nlinarith [hξ.1, hξ.2]
  have h2 : k * ξ ^ 2 < 1 := by nlinarith [sq_nonneg ξ]
  refine ⟨sqrt_pos.mpr (by linarith), sqrt_pos.mpr (by linarith), ?_, ?_⟩
  · rw [sq_sqrt (by linarith), div_pow, sq_sqrt hk0.le]
    field_simp
  · rw [sq_sqrt (by linarith)]
    field_simp

end ContinuumMechanics.RayleighWave
