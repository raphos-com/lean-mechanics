import ClassicalMechanics.Vector
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Special-relativistic mechanics of a particle

The speed of light is `c > 0`; all velocities satisfy `|v| < c`, and the **Lorentz factor** is
`γ(v) = 1 / √(1 - v² / c²)` (`gamma`).

**Lorentz boosts** (in `1 + 1` dimensions). The boost `t' = γ (t - v x / c²)`, `x' = γ (x - v t)`
(`boost`) preserves the Minkowski interval `c² t² - x²` (`interval_boost`). Two boosts compose
to the boost with the **relativistic sum** `u ⊕ v = (u + v) / (1 + u v / c²)` (`boost_boost`,
`velAdd`), and `|u|, |v| < c ⇒ |u ⊕ v| < c`: the speed of light cannot be exceeded
(`abs_velAdd_lt`). With the rapidity `v = c tanh η` one has `γ = cosh η` (`gamma_tanh`), the boost
is a hyperbolic rotation (`boost_tanh`) and rapidities add (`velAdd_tanh`,
`boost_tanh_boost_tanh`).

**Kinematic effects.** `γ ≥ 1` (`one_le_gamma`); a clock at rest reads `t' = γ t` in the moving
frame (`boost_clock_at_rest`), a moving clock shows the proper time `t / γ`
(`boost_moving_clock`), and moving rods are contracted, `L = L₀ / γ ≤ L₀`
(`length_contraction`).

**Energy and momentum** in `ℝ³`. For `p = γ m u` and `E = γ m c²` (`momentum`, `energy`) the
**energy–momentum relation** `E² = |p|² c² + (m c²)²` holds (`energy_momentum`). The relativistic
kinetic energy dominates the Newtonian one, `½ m |u|² ≤ E - m c²` (`kinetic_le_energy_sub`), and
in one dimension `(E - m c²) / (½ m v²) → 1` as `v → 0` (`tendsto_energy_ratio`).

**Relativistic Newton law** (one dimension). `d/dt (γ m u) = m γ³ u̇` and
`d/dt (γ m c²) = m γ³ u u̇` (`hasDerivAt_momentum1`, `hasDerivAt_energy1`), hence `ṗ = F` implies
the **work–energy theorem** `Ė = F u` (`work_energy`). Under a constant force `F = m a` the
**hyperbolic motion** `x(t) = (c² / a)(√(1 + (a t / c)²) - 1)` (`hypPos`) has velocity
`u = a t / √(1 + (a t / c)²)` (`hasDerivAt_hypPos`) with `|u| < c` for all times
(`abs_hypVel_lt`), momentum `p = F t` (`momentum_hyp`, `hasDerivAt_momentum_hyp`), constant proper
acceleration `γ³ u̇ = a` (`hyp_proper_accel`), and a hyperbolic worldline (`hypPos_hyperbola`).

**Four-momentum.** The boost `(E, p) ↦ (γ (E - v p), γ (p - v E / c²))` (`fourBoost`) preserves
`E² - p² c²` (`massShell_fourBoost`), which equals `(m c²)²` on a particle
(`massShell_fourMomentum`); it maps the four-momentum of velocity `u` to that of `u ⊕ (-v)`
(`fourBoost_fourMomentum`), and it is additive, so conservation of the total four-momentum in a
collision holds in every frame (`fourBoost_conservation`).

## References

* [Rindler2006] W. Rindler, *Relativity: Special, General, and Cosmological*, 2nd ed., Ch. 2–6.
* [LandauLifshitz1975] L. D. Landau, E. M. Lifshitz, *The Classical Theory of Fields*, 4th ed.,
  §§1–9.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Ch. 7.
-/

open Matrix Filter Topology

noncomputable section

namespace ClassicalMechanics

namespace Relativity

variable {c u v m t x : ℝ}

/-- The **Lorentz factor** `γ = 1 / √(1 - v² / c²)` of the velocity `v`. -/
def gamma (c v : ℝ) : ℝ := (√(1 - v ^ 2 / c ^ 2))⁻¹

/-- For `|v| < c`, `1 - v² / c² > 0`. -/
theorem one_sub_sq_div_pos (hc : 0 < c) (hv : |v| < c) : 0 < 1 - v ^ 2 / c ^ 2 := by
  have h : v ^ 2 < c ^ 2 := sq_lt_sq' (abs_lt.1 hv).1 (abs_lt.1 hv).2
  rw [sub_pos, div_lt_one (by positivity)]
  exact h

/-- The Lorentz factor is positive. -/
theorem gamma_pos (hc : 0 < c) (hv : |v| < c) : 0 < gamma c v :=
  inv_pos.2 (Real.sqrt_pos.2 (one_sub_sq_div_pos hc hv))

/-- `γ² (1 - v² / c²) = 1`. -/
theorem gamma_sq_mul (hc : 0 < c) (hv : |v| < c) : gamma c v ^ 2 * (1 - v ^ 2 / c ^ 2) = 1 := by
  have h := one_sub_sq_div_pos hc hv
  rw [gamma, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- `γ ≥ 1`: moving clocks run slow, moving rods are short. -/
theorem one_le_gamma (hc : 0 < c) (hv : |v| < c) : 1 ≤ gamma c v := by
  have h := one_sub_sq_div_pos hc hv
  rw [gamma, one_le_inv₀ (Real.sqrt_pos.2 h)]
  exact Real.sqrt_le_one.2 (by have := sq_nonneg (v / c); rw [div_pow] at this; linarith)

/-- The Lorentz factor is even in `v`. -/
theorem gamma_neg (c v : ℝ) : gamma c (-v) = gamma c v := by simp [gamma]

/-! ### Lorentz boosts -/

/-- The **Lorentz boost** with velocity `v` along `x`, acting on events `(t, x)`:
`t' = γ (t - v x / c²)`, `x' = γ (x - v t)`. -/
def boost (c v : ℝ) (e : ℝ × ℝ) : ℝ × ℝ :=
  (gamma c v * (e.1 - v * e.2 / c ^ 2), gamma c v * (e.2 - v * e.1))

/-- The **Minkowski interval** `c² t² - x²` of an event `(t, x)`. -/
def interval (c : ℝ) (e : ℝ × ℝ) : ℝ := c ^ 2 * e.1 ^ 2 - e.2 ^ 2

/-- **Lorentz invariance of the interval**: `c² t'² - x'² = c² t² - x²`. -/
theorem interval_boost (hc : 0 < c) (hv : |v| < c) (e : ℝ × ℝ) :
    interval c (boost c v e) = interval c e := by
  have h := gamma_sq_mul hc hv
  have hc0 : c ≠ 0 := hc.ne'
  simp only [interval, boost]
  field_simp at h ⊢
  linear_combination (c ^ 2 * e.1 ^ 2 - e.2 ^ 2) * h


/-- **Time dilation** (clock at rest): a clock at rest at `x = 0` reads `t` when the boosted
observer's clock reads `t' = γ t ≥ t`. -/
theorem boost_clock_at_rest (c v t : ℝ) : (boost c v (t, 0)).1 = gamma c v * t := by
  simp [boost]

/-- **Proper time of a moving clock**: the clock with worldline `x = v t` is at rest at `x' = 0`
in the boosted frame, where it reads `t' = t / γ`. -/
theorem boost_moving_clock (hc : 0 < c) (hv : |v| < c) (t : ℝ) :
    boost c v (t, v * t) = (t / gamma c v, 0) := by
  have h := gamma_sq_mul hc hv
  have hg := (gamma_pos hc hv).ne'
  refine Prod.ext ?_ ?_
  · simp only [boost]
    rw [eq_div_iff hg]
    linear_combination t * h
  · simp [boost]

/-- Two events simultaneous in the unprimed frame have `x'₂ - x'₁ = γ (x₂ - x₁)`. -/
theorem boost_sub_snd (c v t x₁ x₂ : ℝ) :
    (boost c v (t, x₂)).2 - (boost c v (t, x₁)).2 = gamma c v * (x₂ - x₁) := by
  simp only [boost]
  ring

/-- **Length contraction**: a rod at rest in the boosted frame with proper length `L₀` has, as
measured simultaneously in the unprimed frame, the length `L = L₀ / γ ≤ L₀`. -/
theorem length_contraction (hc : 0 < c) (hv : |v| < c) {t x₁ x₂ L₀ : ℝ}
    (h : (boost c v (t, x₂)).2 - (boost c v (t, x₁)).2 = L₀) (hL : 0 ≤ L₀) :
    x₂ - x₁ = L₀ / gamma c v ∧ x₂ - x₁ ≤ L₀ := by
  rw [boost_sub_snd] at h
  have hg := gamma_pos hc hv
  have h1 : x₂ - x₁ = L₀ / gamma c v := by
    rw [eq_div_iff hg.ne']
    linarith
  exact ⟨h1, h1 ▸ div_le_self hL (one_le_gamma hc hv)⟩

/-! ### Relativistic addition of velocities -/

/-- **Relativistic velocity addition** `u ⊕ v = (u + v) / (1 + u v / c²)`. -/
def velAdd (c u v : ℝ) : ℝ := (u + v) / (1 + u * v / c ^ 2)

/-- For `|u|, |v| < c`, `1 + u v / c² > 0`. -/
theorem one_add_mul_div_pos (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) :
    0 < 1 + u * v / c ^ 2 := by
  have h1 : |u * v| < c * c := by
    rw [abs_mul]
    exact mul_lt_mul'' hu hv (abs_nonneg _) (abs_nonneg _)
  have h2 : -(c * c) < u * v := by linarith [neg_abs_le (u * v)]
  have : -1 < u * v / c ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `1 - (u ⊕ v)² / c² = (1 - u² / c²) (1 - v² / c²) / (1 + u v / c²)²`. -/
theorem one_sub_velAdd_sq (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) :
    1 - velAdd c u v ^ 2 / c ^ 2 =
      (1 - u ^ 2 / c ^ 2) * (1 - v ^ 2 / c ^ 2) / (1 + u * v / c ^ 2) ^ 2 := by
  have hD := one_add_mul_div_pos hc hu hv
  have hc0 := hc.ne'
  have hD' : c ^ 2 + u * v ≠ 0 := by
    have : 0 < c ^ 2 * (1 + u * v / c ^ 2) := by positivity
    rw [mul_add, mul_one, mul_div_cancel₀ _ (by positivity)] at this
    exact this.ne'
  rw [velAdd]
  field_simp
  ring

/-- **The speed of light cannot be exceeded**: `|u|, |v| < c ⇒ |u ⊕ v| < c`. -/
theorem abs_velAdd_lt (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) : |velAdd c u v| < c := by
  have h : 0 < 1 - velAdd c u v ^ 2 / c ^ 2 := by
    rw [one_sub_velAdd_sq hc hu hv]
    have := one_add_mul_div_pos hc hu hv
    exact div_pos (mul_pos (one_sub_sq_div_pos hc hu) (one_sub_sq_div_pos hc hv)) (by positivity)
  rw [sub_pos, div_lt_one (by positivity)] at h
  exact abs_lt_of_sq_lt_sq h hc.le

/-- The Lorentz factor of a composite velocity: `γ(u ⊕ v) = γ(u) γ(v) (1 + u v / c²)`. -/
theorem gamma_velAdd (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) :
    gamma c (velAdd c u v) = gamma c u * gamma c v * (1 + u * v / c ^ 2) := by
  have hD := one_add_mul_div_pos hc hu hv
  have hA := one_sub_sq_div_pos hc hu
  have hB := one_sub_sq_div_pos hc hv
  rw [gamma, one_sub_velAdd_sq hc hu hv, Real.sqrt_div (mul_nonneg hA.le hB.le),
    Real.sqrt_mul hA.le, Real.sqrt_sq hD.le, gamma, gamma]
  have := Real.sqrt_pos.2 hA
  have := Real.sqrt_pos.2 hB
  field_simp

/-- **Composition of boosts**: the boost with velocity `v` followed by the boost with velocity
`u` is the boost with the relativistic sum `u ⊕ v = (u + v) / (1 + u v / c²)`. -/
theorem boost_boost (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) (e : ℝ × ℝ) :
    boost c u (boost c v e) = boost c (velAdd c u v) e := by
  have hw : (1 + u * v / c ^ 2) * velAdd c u v = u + v :=
    mul_div_cancel₀ _ (one_add_mul_div_pos hc hu hv).ne'
  simp only [boost]
  rw [gamma_velAdd hc hu hv]
  refine Prod.ext ?_ ?_
  · linear_combination (gamma c u * gamma c v * e.2 / c ^ 2) * hw
  · linear_combination (gamma c u * gamma c v * e.1) * hw

/-! ### Rapidity -/

/-- The Lorentz factor of the velocity `c tanh η` is `cosh η`. -/
theorem gamma_tanh (hc : 0 < c) (η : ℝ) : gamma c (c * Real.tanh η) = Real.cosh η := by
  have hch := Real.cosh_pos η
  have h : 1 - (c * Real.tanh η) ^ 2 / c ^ 2 = (Real.cosh η ^ 2)⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linear_combination Real.cosh_sq η
  rw [gamma, h, Real.sqrt_inv, Real.sqrt_sq hch.le, inv_inv]

/-- Every velocity `c tanh η` is smaller than the speed of light. -/
theorem abs_mul_tanh_lt (hc : 0 < c) (η : ℝ) : |c * Real.tanh η| < c := by
  rw [abs_mul, abs_of_pos hc]
  exact mul_lt_of_lt_one_right hc (Real.abs_tanh_lt_one η)

/-- In rapidity form, a boost is a hyperbolic rotation:
`t' = t cosh η - (x / c) sinh η`, `x' = x cosh η - c t sinh η`. -/
theorem boost_tanh (hc : 0 < c) (η : ℝ) (e : ℝ × ℝ) :
    boost c (c * Real.tanh η) e =
      (e.1 * Real.cosh η - e.2 / c * Real.sinh η, e.2 * Real.cosh η - c * e.1 * Real.sinh η) := by
  have hch := (Real.cosh_pos η).ne'
  have hc0 := hc.ne'
  simp only [boost]
  rw [gamma_tanh hc]
  simp only [Real.tanh_eq_sinh_div_cosh]
  refine Prod.ext ?_ ?_
  · field_simp
  · field_simp

/-- **Rapidities add**: `c tanh a ⊕ c tanh b = c tanh (a + b)`. -/
theorem velAdd_tanh (hc : 0 < c) (a b : ℝ) :
    velAdd c (c * Real.tanh a) (c * Real.tanh b) = c * Real.tanh (a + b) := by
  have ha := (Real.cosh_pos a).ne'
  have hb := (Real.cosh_pos b).ne'
  have hc0 := hc.ne'
  have hab := Real.cosh_pos (a + b)
  rw [Real.cosh_add] at hab
  simp only [velAdd, Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  field_simp

/-- **Composition of boosts in rapidity form**: boosts with rapidities `a` and `b` compose to
the boost with rapidity `a + b`. -/
theorem boost_tanh_boost_tanh (hc : 0 < c) (a b : ℝ) (e : ℝ × ℝ) :
    boost c (c * Real.tanh a) (boost c (c * Real.tanh b) e) =
      boost c (c * Real.tanh (a + b)) e := by
  rw [boost_boost hc (abs_mul_tanh_lt hc a) (abs_mul_tanh_lt hc b), velAdd_tanh hc]

/-! ### Energy and momentum of a particle in space -/

/-- `|a u|² = a² |u|²`. -/
theorem normSq_smul (a : ℝ) (u : Vec) : normSq (a • u) = a ^ 2 * normSq u := by
  simp only [normSq, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- The Lorentz factor `γ = 1 / √(1 - |u|² / c²)` of a velocity `u ∈ ℝ³`. -/
def lorentzFactor (c : ℝ) (u : Vec) : ℝ := (√(1 - normSq u / c ^ 2))⁻¹

/-- The **relativistic momentum** `p = γ m u` of a particle of mass `m` and velocity `u`. -/
def momentum (c m : ℝ) (u : Vec) : Vec := (lorentzFactor c u * m) • u

/-- The **relativistic energy** `E = γ m c²` of a particle of mass `m` and velocity `u`. -/
def energy (c m : ℝ) (u : Vec) : ℝ := lorentzFactor c u * m * c ^ 2

/-- `γ² (1 - |u|² / c²) = 1` for `|u| < c`. -/
theorem lorentzFactor_sq_mul {u : Vec} (hc : 0 < c) (hu : normSq u < c ^ 2) :
    lorentzFactor c u ^ 2 * (1 - normSq u / c ^ 2) = 1 := by
  have h : 0 < 1 - normSq u / c ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hu
  rw [lorentzFactor, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- **Energy–momentum relation** `E² = (|p| c)² + (m c²)²`. -/
theorem energy_momentum {u : Vec} (hc : 0 < c) (hu : normSq u < c ^ 2) :
    energy c m u ^ 2 = normSq (momentum c m u) * c ^ 2 + (m * c ^ 2) ^ 2 := by
  have h := lorentzFactor_sq_mul hc hu
  rw [energy, momentum, normSq_smul]
  set A := 1 - normSq u / c ^ 2 with hA
  have hn : normSq u = c ^ 2 * (1 - A) := by
    rw [hA]
    field_simp
    ring
  rw [hn]
  linear_combination (m ^ 2 * c ^ 4) * h

/-- `1 + s / 2 ≤ 1 / √(1 - s)` for `0 ≤ s < 1`. -/
theorem one_add_half_le_inv_sqrt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 + s / 2 ≤ (√(1 - s))⁻¹ := by
  have hpos : 0 < √(1 - s) := Real.sqrt_pos.2 (by linarith)
  rw [← one_div, le_div_iff₀ hpos]
  have : (1 + s / 2) * √(1 - s) = √((1 + s / 2) ^ 2 * (1 - s)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  rw [this]
  exact Real.sqrt_le_one.2 (by nlinarith [mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0])

/-- **Kinetic energy bound**: `½ m |u|² ≤ E - m c²`; the relativistic kinetic energy exceeds
the Newtonian one. -/
theorem kinetic_le_energy_sub {u : Vec} (hc : 0 < c) (hu : normSq u < c ^ 2) (hm : 0 ≤ m) :
    m / 2 * normSq u ≤ energy c m u - m * c ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have h := one_add_half_le_inv_sqrt (div_nonneg (normSq_nonneg u) hc2.le)
    (by rw [div_lt_one hc2]; exact hu)
  have key : m / 2 * normSq u = m * c ^ 2 * (normSq u / c ^ 2 / 2) := by
    field_simp
  rw [energy, lorentzFactor, key]
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hm hc2.le)]

/-- The ratio of the relativistic to the Newtonian kinetic energy in one dimension,
`(E - m c²) / (½ m v²) = 2 / (√(1 - v²/c²) (1 + √(1 - v²/c²)))`. -/
theorem energy_ratio_eq (hc : 0 < c) (hv : |v| < c) (hv0 : v ≠ 0) (hm : m ≠ 0) :
    (gamma c v * m * c ^ 2 - m * c ^ 2) / (m / 2 * v ^ 2) =
      2 / (√(1 - v ^ 2 / c ^ 2) * (1 + √(1 - v ^ 2 / c ^ 2))) := by
  have hA := one_sub_sq_div_pos hc hv
  have hc0 := hc.ne'
  rw [gamma]
  have hr0 : 0 < √(1 - v ^ 2 / c ^ 2) := Real.sqrt_pos.2 hA
  have hr2 : √(1 - v ^ 2 / c ^ 2) ^ 2 = 1 - v ^ 2 / c ^ 2 := Real.sq_sqrt hA.le
  set r := √(1 - v ^ 2 / c ^ 2)
  have hv2 : v ^ 2 = c ^ 2 * (1 - r ^ 2) := by
    rw [hr2]
    field_simp
    ring
  rw [div_eq_div_iff (mul_ne_zero (div_ne_zero hm two_ne_zero) (pow_ne_zero 2 hv0))
    (by positivity), hv2]
  field_simp
  ring

/-- **Newtonian limit**: `(E - m c²) / (½ m v²) → 1` as `v → 0`. -/
theorem tendsto_energy_ratio (hc : 0 < c) (hm : m ≠ 0) :
    Tendsto (fun v => (gamma c v * m * c ^ 2 - m * c ^ 2) / (m / 2 * v ^ 2)) (𝓝[≠] 0)
      (𝓝 1) := by
  have hg : Tendsto (fun v : ℝ => 2 / (√(1 - v ^ 2 / c ^ 2) * (1 + √(1 - v ^ 2 / c ^ 2))))
      (𝓝 0) (𝓝 1) := by
    have : ContinuousAt
        (fun v : ℝ => 2 / (√(1 - v ^ 2 / c ^ 2) * (1 + √(1 - v ^ 2 / c ^ 2)))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      norm_num
    convert this.tendsto using 2
    norm_num
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  have h1 : ∀ᶠ v in 𝓝[≠] (0 : ℝ), v ≠ 0 := self_mem_nhdsWithin
  have h2 : ∀ᶠ v in 𝓝 (0 : ℝ), v ∈ Set.Ioo (-c) c := Ioo_mem_nhds (by linarith) hc
  filter_upwards [h1, nhdsWithin_le_nhds h2] with v hv0 hv
  exact (energy_ratio_eq hc (abs_lt.2 hv) hv0 hm).symm

/-! ### Relativistic Newton's law in one dimension -/

/-- `d/dt γ(u(t)) = γ³ u u̇ / c²`. -/
theorem hasDerivAt_gamma {vel : ℝ → ℝ} {a t : ℝ} (hc : 0 < c) (hu : HasDerivAt vel a t)
    (hut : |vel t| < c) :
    HasDerivAt (fun s => gamma c (vel s)) (gamma c (vel t) ^ 3 * vel t * a / c ^ 2) t := by
  have hA := one_sub_sq_div_pos hc hut
  have hr := Real.sqrt_pos.2 hA
  have h := ((((hu.pow 2).div_const (c ^ 2)).const_sub 1).sqrt hA.ne').inv hr.ne'
  refine h.congr_deriv ?_
  have hc0 := hc.ne'
  simp only [gamma, Pi.pow_apply]
  norm_num
  field_simp

/-- **Rate of change of relativistic momentum**: `d/dt (γ m u) = m γ³ u̇`. -/
theorem hasDerivAt_momentum1 {vel : ℝ → ℝ} {a t : ℝ} (hc : 0 < c) (hu : HasDerivAt vel a t)
    (hut : |vel t| < c) :
    HasDerivAt (fun s => gamma c (vel s) * m * vel s) (m * gamma c (vel t) ^ 3 * a) t := by
  have h := ((hasDerivAt_gamma hc hu hut).mul_const m).mul hu
  convert h using 1
  have hγ := gamma_sq_mul hc hut
  linear_combination (m * a * gamma c (vel t)) * hγ

/-- **Rate of change of relativistic energy**: `d/dt (γ m c²) = m γ³ u u̇`. -/
theorem hasDerivAt_energy1 {vel : ℝ → ℝ} {a t : ℝ} (hc : 0 < c) (hu : HasDerivAt vel a t)
    (hut : |vel t| < c) :
    HasDerivAt (fun s => gamma c (vel s) * m * c ^ 2)
      (m * gamma c (vel t) ^ 3 * vel t * a) t := by
  have h := ((hasDerivAt_gamma hc hu hut).mul_const m).mul_const (c ^ 2)
  convert h using 1
  have hc0 := hc.ne'
  field_simp

/-- **Work–energy theorem**: if the relativistic momentum obeys Newton's law `ṗ = F`, then the
energy changes at the rate of the power, `Ė = F u`. -/
theorem work_energy {vel : ℝ → ℝ} {a t F : ℝ} (hc : 0 < c) (hu : HasDerivAt vel a t)
    (hut : |vel t| < c) (hp : HasDerivAt (fun s => gamma c (vel s) * m * vel s) F t) :
    HasDerivAt (fun s => gamma c (vel s) * m * c ^ 2) (F * vel t) t := by
  rw [hp.unique (hasDerivAt_momentum1 hc hu hut)]
  convert hasDerivAt_energy1 (m := m) hc hu hut using 1
  ring

/-! ### Hyperbolic motion -/

/-- The quantity `1 + (a t / c)²` of hyperbolic motion. -/
def hypQ (c a t : ℝ) : ℝ := 1 + (a * t / c) ^ 2

/-- **Hyperbolic motion** with proper acceleration `a`:
`x(t) = (c² / a) (√(1 + (a t / c)²) - 1)`. -/
def hypPos (c a t : ℝ) : ℝ := c ^ 2 / a * (√(hypQ c a t) - 1)

/-- Velocity of hyperbolic motion, `u(t) = a t / √(1 + (a t / c)²)`. -/
def hypVel (c a t : ℝ) : ℝ := a * t / √(hypQ c a t)

/-- `1 + (a t / c)² > 0`. -/
theorem hypQ_pos (c a t : ℝ) : 0 < hypQ c a t := by
  unfold hypQ
  positivity

/-- The velocity of hyperbolic motion is the derivative of the position. -/
theorem hasDerivAt_hypPos (hc : 0 < c) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (hypPos c a) (hypVel c a t) t := by
  have hQ := hypQ_pos c a t
  have hc0 := hc.ne'
  have h1 : HasDerivAt (hypQ c a) (2 * (a * t / c) * (a / c)) t := by
    have := ((((hasDerivAt_id t).const_mul a).div_const c).pow 2).const_add 1
    refine this.congr_deriv ?_
    simp
  have h := ((h1.sqrt hQ.ne').sub_const 1).const_mul (c ^ 2 / a)
  refine h.congr_deriv ?_
  have := Real.sqrt_pos.2 hQ
  unfold hypVel
  field_simp

/-- The worldline of hyperbolic motion is a hyperbola: `(x + c²/a)² - c² t² = c⁴ / a²`. -/
theorem hypPos_hyperbola (hc : 0 < c) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    (hypPos c a t + c ^ 2 / a) ^ 2 - c ^ 2 * t ^ 2 = c ^ 4 / a ^ 2 := by
  have hsq := Real.sq_sqrt (hypQ_pos c a t).le
  have hc0 := hc.ne'
  have hk : c ^ 4 / a ^ 2 * (a * t / c) ^ 2 = c ^ 2 * t ^ 2 := by
    field_simp
  unfold hypPos
  set r := √(hypQ c a t)
  unfold hypQ at hsq
  linear_combination c ^ 4 / a ^ 2 * hsq + hk

/-- **The speed of light is never reached** under a constant force: `|u(t)| < c`. -/
theorem abs_hypVel_lt (hc : 0 < c) (a t : ℝ) : |hypVel c a t| < c := by
  have hQ := hypQ_pos c a t
  have hsq := Real.sq_sqrt hQ.le
  have hc0 := hc.ne'
  have h2 : hypVel c a t ^ 2 < c ^ 2 := by
    rw [hypVel, div_pow, hsq, div_lt_iff₀ hQ]
    have : c ^ 2 * hypQ c a t = c ^ 2 + (a * t) ^ 2 := by
      unfold hypQ
      field_simp
    rw [this]
    linarith [pow_pos hc 2]
  exact abs_lt_of_sq_lt_sq h2 hc.le

/-- The Lorentz factor of hyperbolic motion is `γ = √(1 + (a t / c)²)`. -/
theorem gamma_hypVel (hc : 0 < c) (a t : ℝ) : gamma c (hypVel c a t) = √(hypQ c a t) := by
  have hQ := hypQ_pos c a t
  have hsq := Real.sq_sqrt hQ.le
  have hc0 := hc.ne'
  have h : 1 - hypVel c a t ^ 2 / c ^ 2 = (hypQ c a t)⁻¹ := by
    rw [hypVel, div_pow, hsq]
    have hQ' : hypQ c a t ≠ 0 := hQ.ne'
    field_simp
    unfold hypQ
    field_simp
    ring
  rw [gamma, h, Real.sqrt_inv, inv_inv]

/-- In hyperbolic motion the relativistic momentum grows linearly: `p(t) = γ m u = m a t`. -/
theorem momentum_hyp (hc : 0 < c) (a t : ℝ) :
    gamma c (hypVel c a t) * m * hypVel c a t = m * a * t := by
  have := Real.sqrt_pos.2 (hypQ_pos c a t)
  rw [gamma_hypVel hc, hypVel]
  field_simp

/-- **Hyperbolic motion solves the relativistic Newton law** `ṗ = F` with the constant force
`F = m a`. -/
theorem hasDerivAt_momentum_hyp (hc : 0 < c) (a t : ℝ) :
    HasDerivAt (fun s => gamma c (hypVel c a s) * m * hypVel c a s) (m * a) t := by
  have : (fun s => gamma c (hypVel c a s) * m * hypVel c a s) = fun s => m * a * s := by
    funext s
    exact momentum_hyp hc a s
  rw [this]
  simpa using (hasDerivAt_id t).const_mul (m * a)

/-- **Constant proper acceleration**: in hyperbolic motion `γ³ u̇ = a`. -/
theorem hyp_proper_accel (hc : 0 < c) {a : ℝ} (hm : m ≠ 0) (t : ℝ) :
    gamma c (hypVel c a t) ^ 3 * deriv (hypVel c a) t = a := by
  have hQ := hypQ_pos c a t
  have hQd : DifferentiableAt ℝ (hypQ c a) t := by
    unfold hypQ
    fun_prop
  have hd : DifferentiableAt ℝ (hypVel c a) t :=
    (differentiableAt_id.const_mul a).div (hQd.sqrt hQ.ne') (Real.sqrt_pos.2 hQ).ne'
  have := (hasDerivAt_momentum1 (m := m) hc hd.hasDerivAt (abs_hypVel_lt hc a t)).unique
    (hasDerivAt_momentum_hyp hc a t)
  apply mul_left_cancel₀ hm
  linear_combination this

/-! ### Four-momentum -/

/-- The boost `(E, p) ↦ (γ (E - v p), γ (p - v E / c²))` of a four-momentum `(E, p)`. -/
def fourBoost (c v : ℝ) (P : ℝ × ℝ) : ℝ × ℝ :=
  (gamma c v * (P.1 - v * P.2), gamma c v * (P.2 - v * P.1 / c ^ 2))

/-- The invariant `E² - p² c²` of a four-momentum `(E, p)`. -/
def massShell (c : ℝ) (P : ℝ × ℝ) : ℝ := P.1 ^ 2 - P.2 ^ 2 * c ^ 2

/-- The four-momentum `(γ m c², γ m u)` of a particle of mass `m` and velocity `u`. -/
def fourMomentum (c m u : ℝ) : ℝ × ℝ := (gamma c u * m * c ^ 2, gamma c u * m * u)

/-- **Invariance of the rest mass**: `E'² - p'² c² = E² - p² c²`. -/
theorem massShell_fourBoost (hc : 0 < c) (hv : |v| < c) (P : ℝ × ℝ) :
    massShell c (fourBoost c v P) = massShell c P := by
  have h := gamma_sq_mul hc hv
  have hc0 : c ≠ 0 := hc.ne'
  simp only [massShell, fourBoost]
  field_simp at h ⊢
  linear_combination (P.1 ^ 2 - P.2 ^ 2 * c ^ 2) * h

/-- The four-momentum of a particle lies on the mass shell `E² - p² c² = (m c²)²`. -/
theorem massShell_fourMomentum (hc : 0 < c) (hu : |u| < c) :
    massShell c (fourMomentum c m u) = (m * c ^ 2) ^ 2 := by
  have h := gamma_sq_mul hc hu
  have hc0 : c ≠ 0 := hc.ne'
  have hn : c ^ 2 * (u ^ 2 / c ^ 2) = u ^ 2 := by field_simp
  simp only [massShell, fourMomentum]
  linear_combination (m ^ 2 * c ^ 4) * h + (gamma c u ^ 2 * m ^ 2 * c ^ 2) * hn

/-- The boosted four-momentum of a particle with velocity `u` is the four-momentum of the
velocity `u ⊕ (-v)` seen in the boosted frame. -/
theorem fourBoost_fourMomentum (hc : 0 < c) (hu : |u| < c) (hv : |v| < c) :
    fourBoost c v (fourMomentum c m u) = fourMomentum c m (velAdd c u (-v)) := by
  have hv' : |-v| < c := by rwa [abs_neg]
  have hw : (1 + u * -v / c ^ 2) * velAdd c u (-v) = u + -v :=
    mul_div_cancel₀ _ (one_add_mul_div_pos hc hu hv').ne'
  have hc2 : c ^ 2 / c ^ 2 = 1 := div_self (by positivity)
  have hn : c ^ 2 * (u * -v / c ^ 2) = u * -v := by field_simp
  simp only [fourBoost, fourMomentum]
  rw [gamma_velAdd hc hu hv', gamma_neg]
  refine Prod.ext ?_ ?_
  · linear_combination (-(gamma c v * gamma c u * m)) * hn
  · linear_combination (-(gamma c v * gamma c u * m)) * hw - (gamma c v * gamma c u * m * v) * hc2

/-- The four-momentum boost is additive. -/
theorem fourBoost_add (c v : ℝ) (P Q : ℝ × ℝ) :
    fourBoost c v (P + Q) = fourBoost c v P + fourBoost c v Q := by
  refine Prod.ext ?_ ?_ <;> simp only [fourBoost, Prod.fst_add, Prod.snd_add] <;> ring

/-- **Conservation of four-momentum is frame independent**: if the total four-momentum is
conserved in a collision, `P₁ + P₂ = P₃ + P₄`, then it is conserved in every boosted frame. -/
theorem fourBoost_conservation (c v : ℝ) {P₁ P₂ P₃ P₄ : ℝ × ℝ} (h : P₁ + P₂ = P₃ + P₄) :
    fourBoost c v P₁ + fourBoost c v P₂ = fourBoost c v P₃ + fourBoost c v P₄ := by
  rw [← fourBoost_add, h, fourBoost_add]

end Relativity

end ClassicalMechanics
