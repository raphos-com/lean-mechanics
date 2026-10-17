import ClassicalMechanics.KeplerPeriod
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Orbital mechanics

Practical consequences of the Kepler problem (`ClassicalMechanics.Kepler`,
`ClassicalMechanics.KeplerThird`, `ClassicalMechanics.KeplerPeriod`) used in astrodynamics.

* **Vis-viva equation** (`vis_viva`): along a bound Kepler motion (`k > 0`, `L ≠ 0`, `E < 0`)
  with semi-major axis `a = -k/(2E)`, `|v|² = (k/m)(2/r - 1/a)` at every time. For parabolic
  orbits (`E = 0`) `|v|² = 2k/(m r)` (`vis_viva_parabolic`), and for hyperbolic orbits (`E > 0`)
  `|v|² = (k/m)(2/r + 1/a)` with `a = k/(2E) > 0` (`vis_viva_hyperbolic`).
* **Circular orbits**: a Kepler motion with constant radius `R` has `x · v = 0` and the
  **circular speed** `|v| = √(k/(m R))` (`speed_of_circular`), eccentricity `e = 0`
  (`ecc_of_circular`), semi-major axis `R` (`semiMajor_of_circular`) and minimal period
  `2π √(m R³/k)` (`period_of_circular`).
* **Escape speed** `v_esc = √(2k/(m r)) = √2 v_circ` (`Orbit.escapeSpeed_eq`): the motion is
  unbound (`E ≥ 0`) iff `|v| ≥ v_esc` (`energy_nonneg_iff`).
* **Apsides**: at a local extremum of `r` the velocity is perpendicular to the radius
  (`dot_v_eq_zero_of_isLocalExtr`); periapsis `r_p = a(1 - e)` and apoapsis `r_a = a(1 + e)`
  (`periapsis_eq`, `apoapsis_eq`), `a = (r_p + r_a)/2` (`semiMajor_eq_apsides`), the
  **apsidal speeds** satisfy `v_p r_p = v_a r_a = |L|/m` (`speed_mul_r_periapsis_eq_apoapsis`),
  `v_p² = (k/(m a))(1+e)/(1-e)` and `v_a² = (k/(m a))(1-e)/(1+e)`.
* **Hohmann transfer** between circular orbits of radii `r₁ < r₂`: the transfer ellipse has
  `a = (r₁ + r₂)/2`; the velocity increments are
  `Δv₁ = √(k/(m r₁)) (√(2r₂/(r₁+r₂)) - 1) > 0` (`Orbit.hohmannDv₁_eq`, `Orbit.hohmannDv₁_pos`)
  and `Δv₂ = √(k/(m r₂)) (1 - √(2r₁/(r₁+r₂))) > 0` (`Orbit.hohmannDv₂_eq`,
  `Orbit.hohmannDv₂_pos`); the transfer time is half the period of the transfer ellipse,
  `π √(m a³/k)` (`half_period_eq_hohmannTime`). As `r₂ → ∞` the total `Δv₁ + Δv₂` tends to
  `(√2 - 1) v_circ(r₁)`, the cost of escape from the inner orbit
  (`Orbit.tendsto_hohmannDv_atTop`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§3.7–3.8.
* [Curtis2014] H. D. Curtis, *Orbital Mechanics for Engineering Students*, 3rd ed., §§2.6–2.9,
  §6.2.
-/

open Matrix Real Filter Topology

noncomputable section

namespace ClassicalMechanics

namespace Orbit

/-- The **circular speed** `√(k / (m r))` at distance `r`. -/
def circularSpeed (m k r : ℝ) : ℝ := √(k / (m * r))

/-- The **escape speed** `√(2k / (m r))` at distance `r`. -/
def escapeSpeed (m k r : ℝ) : ℝ := √(2 * k / (m * r))

/-- The speed `√((k/m)(2/r - 1/a))` given by the **vis-viva equation** at distance `r` on an
elliptic orbit of semi-major axis `a`. -/
def visVivaSpeed (m k a r : ℝ) : ℝ := √(k / m * (2 / r - 1 / a))

/-- The semi-major axis `(r₁ + r₂)/2` of the **Hohmann transfer ellipse**. -/
def transferSemiMajor (r₁ r₂ : ℝ) : ℝ := (r₁ + r₂) / 2

/-- The first **Hohmann burn**: transfer-ellipse speed minus circular speed at `r₁`. -/
def hohmannDv₁ (m k r₁ r₂ : ℝ) : ℝ :=
  visVivaSpeed m k (transferSemiMajor r₁ r₂) r₁ - circularSpeed m k r₁

/-- The second **Hohmann burn**: circular speed minus transfer-ellipse speed at `r₂`. -/
def hohmannDv₂ (m k r₁ r₂ : ℝ) : ℝ :=
  circularSpeed m k r₂ - visVivaSpeed m k (transferSemiMajor r₁ r₂) r₂

/-- The **Hohmann transfer time** `π √(m a³ / k)`, `a = (r₁ + r₂)/2`. -/
def hohmannTime (m k r₁ r₂ : ℝ) : ℝ := π * √(m * transferSemiMajor r₁ r₂ ^ 3 / k)

/-- On a circular orbit (`a = r`), the vis-viva speed is the circular speed. -/
theorem visVivaSpeed_self {m k r : ℝ} (hr : r ≠ 0) :
    visVivaSpeed m k r r = circularSpeed m k r := by
  rw [visVivaSpeed, circularSpeed]
  congr 1
  field_simp
  ring

/-- `v_esc = √2 · v_circ`. -/
theorem escapeSpeed_eq (m k r : ℝ) : escapeSpeed m k r = √2 * circularSpeed m k r := by
  rw [escapeSpeed, circularSpeed, ← Real.sqrt_mul zero_le_two, mul_div_assoc]

/-- The speed on the transfer ellipse at the inner radius:
`√(k/(m r₁)) · √(2r₂/(r₁+r₂))`. -/
theorem visVivaSpeed_transfer_r₁ {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) :
    visVivaSpeed m k (transferSemiMajor r₁ r₂) r₁ =
      circularSpeed m k r₁ * √(2 * r₂ / (r₁ + r₂)) := by
  rw [visVivaSpeed, circularSpeed, transferSemiMajor,
    ← Real.sqrt_mul (div_pos hk (mul_pos hm h₁)).le]
  congr 1
  field_simp
  ring

/-- The speed on the transfer ellipse at the outer radius:
`√(k/(m r₂)) · √(2r₁/(r₁+r₂))`. -/
theorem visVivaSpeed_transfer_r₂ {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) :
    visVivaSpeed m k (transferSemiMajor r₁ r₂) r₂ =
      circularSpeed m k r₂ * √(2 * r₁ / (r₁ + r₂)) := by
  rw [visVivaSpeed, circularSpeed, transferSemiMajor,
    ← Real.sqrt_mul (div_pos hk (mul_pos hm h₂)).le]
  congr 1
  field_simp
  ring

/-- **First Hohmann burn** `Δv₁ = √(k/(m r₁)) (√(2r₂/(r₁+r₂)) - 1)`. -/
theorem hohmannDv₁_eq {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    hohmannDv₁ m k r₁ r₂ = √(k / (m * r₁)) * (√(2 * r₂ / (r₁ + r₂)) - 1) := by
  rw [hohmannDv₁, visVivaSpeed_transfer_r₁ hm hk h₁ h₂, circularSpeed]
  ring

/-- **Second Hohmann burn** `Δv₂ = √(k/(m r₂)) (1 - √(2r₁/(r₁+r₂)))`. -/
theorem hohmannDv₂_eq {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    hohmannDv₂ m k r₁ r₂ = √(k / (m * r₂)) * (1 - √(2 * r₁ / (r₁ + r₂))) := by
  rw [hohmannDv₂, visVivaSpeed_transfer_r₂ hm hk h₁ h₂, circularSpeed]
  ring

/-- The first Hohmann burn is a positive (prograde) velocity increment. -/
theorem hohmannDv₁_pos {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    0 < hohmannDv₁ m k r₁ r₂ := by
  have h₂ : 0 < r₂ := h₁.trans h₁₂
  rw [hohmannDv₁_eq hm hk h₁ h₂]
  refine mul_pos (Real.sqrt_pos.2 (div_pos hk (mul_pos hm h₁))) (sub_pos.2 ?_)
  rw [Real.lt_sqrt zero_le_one, one_pow, one_lt_div (by linarith)]
  linarith

/-- The second Hohmann burn is a positive (prograde) velocity increment. -/
theorem hohmannDv₂_pos {m k r₁ r₂ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    0 < hohmannDv₂ m k r₁ r₂ := by
  have h₂ : 0 < r₂ := h₁.trans h₁₂
  rw [hohmannDv₂_eq hm hk h₁ h₂]
  refine mul_pos (Real.sqrt_pos.2 (div_pos hk (mul_pos hm h₂))) (sub_pos.2 ?_)
  rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
  linarith

/-- **Escape from a circular orbit**: as `r₂ → ∞`, the total Hohmann velocity increment tends to
`(√2 - 1) √(k/(m r₁))`. -/
theorem tendsto_hohmannDv_atTop {m k r₁ : ℝ} (hm : 0 < m) (hk : 0 < k) (h₁ : 0 < r₁) :
    Tendsto (fun r₂ => hohmannDv₁ m k r₁ r₂ + hohmannDv₂ m k r₁ r₂) atTop
      (𝓝 ((√2 - 1) * circularSpeed m k r₁)) := by
  have hden : Tendsto (fun r₂ : ℝ => r₁ + r₂) atTop atTop := tendsto_atTop_add_const_left _ r₁
    tendsto_id
  have hA : Tendsto (fun r₂ : ℝ => 2 / (r₁ / r₂ + 1)) atTop (𝓝 (2 / (0 + 1))) :=
    tendsto_const_nhds.div ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds)
      (by norm_num)
  have hB : Tendsto (fun r₂ : ℝ => 2 * r₁ / (r₁ + r₂)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hC : Tendsto (fun r₂ : ℝ => k / (m * r₂)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hm)
  have hlim := (tendsto_const_nhds (x := √(k / (m * r₁)))).mul
    (hA.sqrt.sub (tendsto_const_nhds (x := (1 : ℝ))))
    |>.add (hC.sqrt.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hB.sqrt))
  rw [circularSpeed]
  convert hlim.congr' ?_ using 2
  · simp
    ring
  filter_upwards [eventually_gt_atTop 0] with r₂ h₂
  rw [hohmannDv₁_eq hm hk h₁ h₂, hohmannDv₂_eq hm hk h₁ h₂]
  congr 3
  field_simp

end Orbit

namespace KeplerMotion

variable {K : KeplerMotion}

open Orbit

/-! ### The vis-viva equation -/

/-- Energy conservation solved for the speed: `|v|² = (2/m)(E + k/r)`. -/
theorem v_dot_v_eq (t : ℝ) : K.v t ⬝ᵥ K.v t = 2 / K.m * (K.E 0 + K.k / K.r t) := by
  have hm := K.m_pos.ne'
  rw [← K.energy_const t 0, E]
  field_simp
  ring

/-- **Vis-viva equation** for a bound Kepler motion: `|v|² = (k/m)(2/r - 1/a)` at every time. -/
theorem vis_viva (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    K.v t ⬝ᵥ K.v t = K.k / K.m * (2 / K.r t - 1 / K.semiMajor) := by
  have hm := K.m_pos.ne'
  have hr := (K.r_pos t).ne'
  rw [v_dot_v_eq, semiMajor_eq hk hL hE]
  field_simp
  ring

/-- The **vis-viva equation** for the speed: `|v| = √((k/m)(2/r - 1/a))`. -/
theorem speed_eq_visVivaSpeed (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) (t : ℝ) :
    radius (K.v t) = visVivaSpeed K.m K.k K.semiMajor (K.r t) := by
  rw [radius, vis_viva hk hL hE, visVivaSpeed]

/-- **Vis-viva equation** for a parabolic orbit (`E = 0`): `|v|² = 2k/(m r)`. -/
theorem vis_viva_parabolic (hE : K.E 0 = 0) (t : ℝ) :
    K.v t ⬝ᵥ K.v t = 2 * K.k / (K.m * K.r t) := by
  have hm := K.m_pos.ne'
  have hr := (K.r_pos t).ne'
  rw [v_dot_v_eq, hE]
  field_simp
  ring

/-- The semi-major axis `a = k/(2E) > 0` of a hyperbolic orbit (`E > 0`). -/
def hypSemiMajor (K : KeplerMotion) : ℝ := K.k / (2 * K.E 0)

/-- The hyperbolic semi-major axis is positive for an attractive force and `E > 0`. -/
theorem hypSemiMajor_pos (hk : 0 < K.k) (hE : 0 < K.E 0) : 0 < K.hypSemiMajor :=
  div_pos hk (by linarith)

/-- **Vis-viva equation** for a hyperbolic orbit (`E > 0`): `|v|² = (k/m)(2/r + 1/a)`,
`a = k/(2E)`. -/
theorem vis_viva_hyperbolic (hk : K.k ≠ 0) (hE : 0 < K.E 0) (t : ℝ) :
    K.v t ⬝ᵥ K.v t = K.k / K.m * (2 / K.r t + 1 / K.hypSemiMajor) := by
  have hm := K.m_pos.ne'
  have hr := (K.r_pos t).ne'
  have hE' := hE.ne'
  rw [v_dot_v_eq, hypSemiMajor]
  field_simp
  ring

/-! ### Escape speed -/

/-- **Escape speed**: the motion is unbound (`E ≥ 0`) iff `|v| ≥ √(2k/(m r))`. -/
theorem energy_nonneg_iff (t : ℝ) :
    0 ≤ K.E t ↔ escapeSpeed K.m K.k (K.r t) ≤ radius (K.v t) := by
  have hm := K.m_pos
  have hr := K.r_pos t
  rw [escapeSpeed, radius, Real.sqrt_le_sqrt_iff (show 0 ≤ K.v t ⬝ᵥ K.v t from normSq_nonneg _),
    E, div_le_iff₀ (by positivity)]
  constructor <;> intro h
  · have : K.k / K.r t * K.r t = K.k := div_mul_cancel₀ _ hr.ne'
    nlinarith
  · have : K.k / K.r t * K.r t = K.k := div_mul_cancel₀ _ hr.ne'
    nlinarith

/-! ### Apsides -/

/-- At a local extremum of the distance `r` (an **apsis**), the velocity is perpendicular to the
radius vector: `x · v = 0`. -/
theorem dot_v_eq_zero_of_isLocalExtr {t : ℝ} (h : IsLocalExtr K.r t) : K.x t ⬝ᵥ K.v t = 0 := by
  have := h.hasDerivAt_eq_zero (K.hasDerivAt_r t)
  rwa [div_eq_zero_iff, or_iff_left (K.r_pos t).ne'] at this

/-- When `x · v = 0`, `|L| = m r |v|`. -/
theorem radius_L_of_dot_eq_zero {t : ℝ} (h : K.x t ⬝ᵥ K.v t = 0) :
    radius (K.L 0) = K.m * K.r t * radius (K.v t) := by
  have hm := K.m_pos
  have hr := K.r_pos t
  have hv : 0 ≤ radius (K.v t) := Real.sqrt_nonneg _
  have hL : 0 ≤ radius (K.L 0) := Real.sqrt_nonneg _
  rw [← pow_left_inj₀ hL (by positivity) two_ne_zero, radius_sq, mul_pow,
    mul_pow, radius_sq, K.r_sq, ← K.angMom_const t 0, L, map_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have := lagrange_identity (K.x t) (K.v t)
  rw [h] at this
  linear_combination (-(K.m ^ 2)) * this

/-- The periapsis is a local minimum of `r`. -/
theorem isLocalMin_of_periapsis (hk : 0 < K.k) {t : ℝ} (h : K.r t = K.semiLatus / (1 + K.ecc)) :
    IsLocalMin K.r t :=
  Eventually.of_forall fun s => h ▸ periapsis_le hk s

/-- The apoapsis is a local maximum of `r` (bound orbit). -/
theorem isLocalMax_of_apoapsis (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {t : ℝ}
    (h : K.r t = K.semiLatus / (1 - K.ecc)) : IsLocalMax K.r t :=
  Eventually.of_forall fun s => h ▸ le_apoapsis hk hL hE s

/-- The periapsis distance is `r_p = a (1 - e)`. -/
theorem periapsis_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiLatus / (1 + K.ecc) = K.semiMajor * (1 - K.ecc) := by
  have := ecc_nonneg hk
  rw [semiLatus_eq hk hL hE, div_eq_iff (by linarith)]
  ring

/-- The apoapsis distance is `r_a = a (1 + e)`. -/
theorem apoapsis_eq (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiLatus / (1 - K.ecc) = K.semiMajor * (1 + K.ecc) := by
  have := ecc_lt_one hk hL hE
  rw [semiLatus_eq hk hL hE, div_eq_iff (by linarith)]
  ring

/-- The semi-major axis is the mean of the periapsis and apoapsis distances. -/
theorem semiMajor_eq_apsides (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) :
    K.semiMajor = (K.semiLatus / (1 + K.ecc) + K.semiLatus / (1 - K.ecc)) / 2 := by
  rw [periapsis_eq hk hL hE, apoapsis_eq hk hL hE]
  ring

/-- **Apsidal speeds**: `v_p r_p = v_a r_a`, both equal to `|L| / m`. -/
theorem speed_mul_r_periapsis_eq_apoapsis (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0)
    {tp ta : ℝ} (hp : K.r tp = K.semiLatus / (1 + K.ecc))
    (ha : K.r ta = K.semiLatus / (1 - K.ecc)) :
    radius (K.v tp) * K.r tp = radius (K.v ta) * K.r ta := by
  have h1 := radius_L_of_dot_eq_zero
    (dot_v_eq_zero_of_isLocalExtr (Or.inl (isLocalMin_of_periapsis hk hp)))
  have h2 := radius_L_of_dot_eq_zero
    (dot_v_eq_zero_of_isLocalExtr (Or.inr (isLocalMax_of_apoapsis hk hL hE ha)))
  have hm := K.m_pos.ne'
  refine mul_left_cancel₀ hm ?_
  linear_combination h2 - h1

/-- **Speed at periapsis**: `v_p² = (k/(m a)) (1 + e)/(1 - e)`. -/
theorem speed_sq_periapsis (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {t : ℝ}
    (h : K.r t = K.semiLatus / (1 + K.ecc)) :
    K.v t ⬝ᵥ K.v t = K.k / (K.m * K.semiMajor) * ((1 + K.ecc) / (1 - K.ecc)) := by
  have hm := K.m_pos.ne'
  have ha := (semiMajor_pos hk hL hE).ne'
  have he := ecc_lt_one hk hL hE
  have he' : 1 - K.ecc ≠ 0 := by linarith
  rw [vis_viva hk hL hE, h, periapsis_eq hk hL hE]
  field_simp
  ring

/-- **Speed at apoapsis**: `v_a² = (k/(m a)) (1 - e)/(1 + e)`. -/
theorem speed_sq_apoapsis (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0) {t : ℝ}
    (h : K.r t = K.semiLatus / (1 - K.ecc)) :
    K.v t ⬝ᵥ K.v t = K.k / (K.m * K.semiMajor) * ((1 - K.ecc) / (1 + K.ecc)) := by
  have hm := K.m_pos.ne'
  have ha := (semiMajor_pos hk hL hE).ne'
  have he := ecc_nonneg hk
  have he' : 1 + K.ecc ≠ 0 := by linarith
  rw [vis_viva hk hL hE, h, apoapsis_eq hk hL hE]
  field_simp
  ring

/-! ### Circular orbits -/

section Circular

variable {R : ℝ}

/-- On a circular orbit (`r ≡ R`), `x · v = 0` at all times. -/
theorem dot_v_eq_zero_of_circular (hR : ∀ t, K.r t = R) (t : ℝ) : K.x t ⬝ᵥ K.v t = 0 :=
  dot_v_eq_zero_of_isLocalExtr (Or.inl (Eventually.of_forall fun s => by rw [hR, hR]))

/-- `m (x · a) = -k / r`. -/
theorem m_mul_x_dot_a (t : ℝ) : K.m * (K.x t ⬝ᵥ K.a t) = -(K.k / K.r t) := by
  have h := congrArg (K.x t ⬝ᵥ ·) (K.newton t)
  simp only [dotProduct_smul, smul_eq_mul] at h
  have hr := (K.r_pos t).ne'
  rw [show radius (K.x t) = K.r t from rfl, ← K.r_sq] at h
  rw [h]
  field_simp

/-- **Circular speed**: on a circular orbit of radius `R`, `|v|² = k / (m R)`. -/
theorem v_dot_v_of_circular (hR : ∀ t, K.r t = R) (t : ℝ) :
    K.v t ⬝ᵥ K.v t = K.k / (K.m * R) := by
  have h := hasDerivAt_dot (K.hasDerivAt_x t) (K.hasDerivAt_v t)
  have hfun : (fun s => K.x s ⬝ᵥ K.v s) = fun _ => 0 := funext (dot_v_eq_zero_of_circular hR)
  rw [hfun] at h
  have h0 := h.unique (hasDerivAt_const t 0)
  have h1 := m_mul_x_dot_a (K := K) t
  have hm := K.m_pos.ne'
  have hr := (K.r_pos t).ne'
  rw [hR] at h1 hr
  have h1' : K.m * (K.x t ⬝ᵥ K.a t) * R = -K.k := by rw [h1]; field_simp
  rw [eq_div_iff (mul_ne_zero hm hr)]
  linear_combination K.m * R * h0 - h1'

/-- **Circular speed**: on a circular orbit of radius `R`, `|v| = √(k / (m R))`. -/
theorem speed_of_circular (hR : ∀ t, K.r t = R) (t : ℝ) :
    radius (K.v t) = circularSpeed K.m K.k R := by
  rw [radius, v_dot_v_of_circular hR, circularSpeed]

/-- The energy of a circular orbit of radius `R` is `E = -k / (2R)`. -/
theorem energy_of_circular (hR : ∀ t, K.r t = R) : K.E 0 = -K.k / (2 * R) := by
  have hm := K.m_pos.ne'
  have hr : R ≠ 0 := (hR 0 ▸ K.r_pos 0).ne'
  rw [E, v_dot_v_of_circular hR, hR]
  field_simp
  ring

/-- The angular momentum of a circular orbit of radius `R` satisfies `|L|² = m k R`. -/
theorem L_dot_L_of_circular (hR : ∀ t, K.r t = R) : K.L 0 ⬝ᵥ K.L 0 = K.m * K.k * R := by
  have h := radius_L_of_dot_eq_zero (dot_v_eq_zero_of_circular hR 0)
  have hr := (K.r_pos 0).ne'
  have hm := K.m_pos.ne'
  rw [← radius_sq, h, mul_pow, mul_pow, radius_sq, v_dot_v_of_circular hR, hR]
  rw [hR] at hr
  field_simp

/-- A circular orbit has **eccentricity** `e = 0`. -/
theorem ecc_of_circular (hR : ∀ t, K.r t = R) : K.ecc = 0 := by
  have hr := (K.r_pos 0).ne'
  rw [hR] at hr
  have hAA : K.A 0 ⬝ᵥ K.A 0 = 0 := by
    rw [K.lrl_sq, energy_of_circular hR, L_dot_L_of_circular hR]
    field_simp
    ring
  rw [ecc, radius, hAA, Real.sqrt_zero, zero_div]

/-- A circular orbit with `k > 0` has nonzero angular momentum. -/
theorem L_ne_zero_of_circular (hk : 0 < K.k) (hR : ∀ t, K.r t = R) : K.L 0 ≠ 0 := by
  intro h
  have := L_dot_L_of_circular hR (K := K)
  rw [h, dotProduct_zero] at this
  have := hR 0 ▸ K.r_pos 0
  have := K.m_pos
  have : 0 < K.m * K.k * R := by positivity
  linarith

/-- A circular orbit with `k > 0` is bound: `E < 0`. -/
theorem energy_neg_of_circular (hk : 0 < K.k) (hR : ∀ t, K.r t = R) : K.E 0 < 0 := by
  rw [energy_of_circular hR]
  have := hR 0 ▸ K.r_pos 0
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The semi-major axis of a circular orbit of radius `R` is `R`. -/
theorem semiMajor_of_circular (hk : 0 < K.k) (hR : ∀ t, K.r t = R) : K.semiMajor = R := by
  have := (hR 0 ▸ K.r_pos 0).ne'
  rw [semiMajor_eq hk (L_ne_zero_of_circular hk hR) (energy_neg_of_circular hk hR),
    energy_of_circular hR]
  field_simp

/-- **Period of a circular orbit**: the minimal period of a circular Kepler orbit of radius `R`
is `T = 2π √(m R³ / k)`. -/
theorem period_of_circular (hk : 0 < K.k) (hR : ∀ t, K.r t = R) {T : ℝ} (hT : 0 < T)
    (hper : ∀ t, K.x (t + T) = K.x t)
    (hmin : ∀ T', 0 < T' → (∀ t, K.x (t + T') = K.x t) → T ≤ T') :
    T = 2 * π * √(K.m * R ^ 3 / K.k) := by
  rw [period_eq hk (L_ne_zero_of_circular hk hR) (energy_neg_of_circular hk hR) hT hper hmin,
    meanMotion, semiMajor_of_circular hk hR, div_eq_mul_inv, ← Real.sqrt_inv, inv_div]

end Circular

/-! ### Hohmann transfer -/

section Hohmann

variable {r₁ r₂ : ℝ}

/-- A bound orbit with periapsis `r₁` and apoapsis `r₂` (a **transfer ellipse**) has semi-major
axis `(r₁ + r₂)/2`. -/
theorem semiMajor_of_apsides (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0)
    (h₁ : K.semiLatus / (1 + K.ecc) = r₁) (h₂ : K.semiLatus / (1 - K.ecc) = r₂) :
    K.semiMajor = transferSemiMajor r₁ r₂ := by
  rw [semiMajor_eq_apsides hk hL hE, h₁, h₂, transferSemiMajor]

/-- On the transfer ellipse, the speed at distance `r` is the vis-viva speed with
`a = (r₁ + r₂)/2`; in particular at `r = r₁` and `r = r₂` it is the speed entering
`hohmannDv₁`, `hohmannDv₂`. -/
theorem speed_of_transfer (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0)
    (h₁ : K.semiLatus / (1 + K.ecc) = r₁) (h₂ : K.semiLatus / (1 - K.ecc) = r₂) (t : ℝ) :
    radius (K.v t) = visVivaSpeed K.m K.k (transferSemiMajor r₁ r₂) (K.r t) := by
  rw [speed_eq_visVivaSpeed hk hL hE, semiMajor_of_apsides hk hL hE h₁ h₂]

/-- **Hohmann transfer time**: half the minimal period of the transfer ellipse is
`π √(m a³ / k)`, `a = (r₁ + r₂)/2`. -/
theorem half_period_eq_hohmannTime (hk : 0 < K.k) (hL : K.L 0 ≠ 0) (hE : K.E 0 < 0)
    (h₁ : K.semiLatus / (1 + K.ecc) = r₁) (h₂ : K.semiLatus / (1 - K.ecc) = r₂) {T : ℝ}
    (hT : 0 < T) (hper : ∀ t, K.x (t + T) = K.x t)
    (hmin : ∀ T', 0 < T' → (∀ t, K.x (t + T') = K.x t) → T ≤ T') :
    T / 2 = hohmannTime K.m K.k r₁ r₂ := by
  rw [period_eq hk hL hE hT hper hmin, meanMotion, semiMajor_of_apsides hk hL hE h₁ h₂,
    hohmannTime, div_eq_mul_inv (2 * π), ← Real.sqrt_inv, inv_div]
  ring

end Hohmann

end KeplerMotion

end ClassicalMechanics
