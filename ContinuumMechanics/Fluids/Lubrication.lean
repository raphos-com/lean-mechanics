import ContinuumMechanics.Fluids.Viscous

/-!
# Hydrodynamic lubrication: the Reynolds equation and the plane slider bearing

In a **thin film** of gap `h` between a stationary surface `y = 0` and a surface `y = h` sliding
with speed `U`, inertia is negligible and the pressure is uniform across the film, so the
momentum balance reduces to `μ u'' = dp/dx`. With no slip on both surfaces the velocity is the
superposition of a Couette and a Poiseuille profile,

`u(y) = (1/(2μ)) (dp/dx) (y² - h y) + U y / h`,

and the flow rate per unit width is `q = ∫₀ʰ u dy = U h / 2 - (h³/(12μ)) dp/dx`.

Conservation of mass for a steady film, `dq/dx = 0`, gives the one-dimensional steady
**Reynolds equation**

`d/dx (h³ p' / (12μ)) = (U/2) h'`.

For the **plane slider (tilted-pad) bearing** `h(x) = h₁ - (h₁ - h₂) x / L` with ambient pressure
`p(0) = p(L) = 0`, the Reynolds equation gives `p' = 6μU (h - hₘ)/h³` with
`hₘ = 2h₁h₂/(h₁ + h₂)` and the classical pressure

`p(x) = 6μU L (h₁ - h)(h - h₂) / ((h₁² - h₂²) h²) = 6μU (h₁ - h₂) x (L - x) / (L (h₁ + h₂) h²)`.

A converging wedge (`h₁ > h₂`) generates a positive pressure, with its maximum where `h = hₘ`,
and the **load capacity**

`W = ∫₀ᴸ p dx = 6μU L² / (K² h₂²) · (log(1 + K) - 2K/(2 + K))`,   `K = h₁/h₂ - 1`,

is positive. A diverging wedge (`h₁ < h₂`) gives negative pressure: no load is supported.

## Main results

* `filmVel_second_deriv`, `filmVel_zero`, `filmVel_gap`: the film velocity satisfies
  `μ u'' = dp/dx` and no slip on both surfaces.
* `filmVel_eq_couette_add_poiseuille`: it is Couette plus Poiseuille flow (`Viscous.lean`).
* `integral_filmVel`: `q = U h / 2 - h³ (dp/dx) / (12μ)`.
* `reynolds_of_flux_const`: constant flux implies the Reynolds equation, and
  `flux_const_of_reynolds`: conversely.
* `hasDerivAt_sliderPres`, `sliderPres_zero`, `sliderPres_length`: the slider pressure solves
  `p' = 6μU (h - hₘ)/h³` with `p(0) = p(L) = 0`; `sliderFlux_eq`: its flux is `U hₘ / 2`;
  `sliderPres_eq_classical`: the classical closed form.
* `sliderPres_eq_of_reynolds`: it is the unique such solution.
* `sliderPres_pos`, `sliderPres_neg`: positive pressure for a converging wedge, negative for a
  diverging one; `deriv_sliderPres_eq_zero_iff`, `sliderGap_xm`, `sliderPres_le_max`: the
  maximum `3μUL(h₁ - h₂)/(2h₁h₂(h₁ + h₂))` is attained where `h = hₘ`.
* `sliderLoad_eq`, `sliderLoad_eq_convergence`: the load capacity; `sliderLoad_pos`,
  `sliderLoad_neg`: its sign; `log_div_gt_of_sliderLoad`: `log(h₁/h₂) > 2(h₁ - h₂)/(h₁ + h₂)`.

## References

* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §4.8.
* [Hamrock2004] B. J. Hamrock, S. R. Schmid, B. O. Jacobson, *Fundamentals of Fluid Film
  Lubrication*, 2nd ed., Ch. 7–8.
-/

open MeasureTheory Real Set

noncomputable section

namespace ContinuumMechanics.Fluids.Lubrication

/-! ### Local flow in a thin film -/

section Film

variable {μ G U h : ℝ}

/-- The **film velocity** `u(y) = (1/(2μ)) G (y² - h y) + U y / h` in a gap of width `h` with
pressure gradient `G = dp/dx`, lower surface at rest and upper surface sliding with speed `U`. -/
def filmVel (μ G U h y : ℝ) : ℝ := G / (2 * μ) * (y ^ 2 - h * y) + U * y / h

/-- The shear rate `u'(y) = (1/(2μ)) G (2y - h) + U / h` of the film. -/
def filmShear (μ G U h y : ℝ) : ℝ := G / (2 * μ) * (2 * y - h) + U / h

/-- Derivative of the film velocity. -/
theorem hasDerivAt_filmVel (y : ℝ) :
    HasDerivAt (filmVel μ G U h) (filmShear μ G U h y) y := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - h * y) (2 * y - h) y :=
    ((hasDerivAt_pow 2 y).sub ((hasDerivAt_id' y).const_mul h)).congr_deriv (by simp)
  have h2 : HasDerivAt (fun y : ℝ => U * y / h) (U / h) y :=
    (((hasDerivAt_id' y).const_mul U).div_const h).congr_deriv (by simp)
  exact (h1.const_mul (G / (2 * μ))).add h2

/-- Derivative of the shear rate: `u'' = G / μ`. -/
theorem hasDerivAt_filmShear (hμ : μ ≠ 0) (y : ℝ) :
    HasDerivAt (filmShear μ G U h) (G / μ) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y - h) 2 y :=
    (((hasDerivAt_id' y).const_mul 2).sub_const h).congr_deriv (by simp)
  exact ((h1.const_mul (G / (2 * μ))).add_const (U / h)).congr_deriv (by field_simp)

/-- The **thin-film momentum balance** `μ u'' = dp/dx`. -/
theorem filmVel_second_deriv (hμ : μ ≠ 0) (y : ℝ) :
    μ * deriv (deriv (filmVel μ G U h)) y = G := by
  have e : deriv (filmVel μ G U h) = filmShear μ G U h :=
    funext fun y => (hasDerivAt_filmVel y).deriv
  rw [e, (hasDerivAt_filmShear hμ y).deriv]
  field_simp

/-- **No slip** on the stationary surface: `u(0) = 0`. -/
theorem filmVel_zero : filmVel μ G U h 0 = 0 := by
  simp [filmVel]

/-- **No slip** on the sliding surface: `u(h) = U`. -/
theorem filmVel_gap (hh : h ≠ 0) : filmVel μ G U h h = U := by
  simp [filmVel, hh, sq]

/-- The film flow is the superposition of plane **Couette** flow (speed `U`) and plane
**Poiseuille** flow driven by the pressure gradient `G` (i.e. `poiseuilleVel` with `-G`). -/
theorem filmVel_eq_couette_add_poiseuille (x : Fin 3 → ℝ) :
    filmVel μ G U h (x 1) = couetteVel U h x 0 + poiseuilleVel μ (-G) h x 0 := by
  simp only [filmVel, couetteVel, poiseuilleVel, Matrix.cons_val_zero]
  ring

/-- The **flow rate per unit width** of the film,
`q = ∫₀ʰ u dy = U h / 2 - h³ G / (12μ)`. -/
theorem integral_filmVel (hμ : μ ≠ 0) (hh : h ≠ 0) :
    ∫ y in (0 : ℝ)..h, filmVel μ G U h y = U * h / 2 - h ^ 3 * G / (12 * μ) := by
  have i1 : IntervalIntegrable (fun y : ℝ => G / (2 * μ) * (y ^ 2 - h * y)) volume 0 h :=
    (by fun_prop : Continuous fun y : ℝ => G / (2 * μ) * (y ^ 2 - h * y)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y : ℝ => U * y / h) volume 0 h :=
    (by fun_prop : Continuous fun y : ℝ => U * y / h).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun y : ℝ => y ^ 2) volume 0 h :=
    (continuous_pow 2).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun y : ℝ => h * y) volume 0 h :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  simp only [filmVel]
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub i3 i4, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    integral_pow]
  field_simp
  ring

end Film

/-! ### The Reynolds equation -/

section Reynolds

variable {μ U Q : ℝ} {h p : ℝ → ℝ}

/-- The **film flux** `q(x) = U h(x) / 2 - h(x)³ p'(x) / (12μ)` (flow rate per unit width). -/
def filmFlux (μ U : ℝ) (h p : ℝ → ℝ) (x : ℝ) : ℝ :=
  U * h x / 2 - h x ^ 3 * deriv p x / (12 * μ)

/-- The **Reynolds equation**: if the flux is constant (`dq/dx = 0`, steady continuity), then
`d/dx (h³ p' / (12μ)) = (U/2) h'`. -/
theorem reynolds_of_flux_const (hq : ∀ x, filmFlux μ U h p x = Q) {x : ℝ}
    (hh : DifferentiableAt ℝ h x) :
    deriv (fun x => h x ^ 3 * deriv p x / (12 * μ)) x = U / 2 * deriv h x := by
  have e : (fun x => h x ^ 3 * deriv p x / (12 * μ)) = fun x => U * h x / 2 - Q := by
    funext x
    have := hq x
    simp only [filmFlux] at this
    linarith
  rw [e]
  have : HasDerivAt (fun x => U * h x / 2 - Q) (U * deriv h x / 2) x :=
    ((hh.hasDerivAt.const_mul U).div_const 2).sub_const Q
  rw [this.deriv]
  ring

/-- Conversely, a solution of the Reynolds equation has constant flux. -/
theorem flux_const_of_reynolds (hh : Differentiable ℝ h)
    (hd : Differentiable ℝ fun x => h x ^ 3 * deriv p x / (12 * μ))
    (hR : ∀ x, deriv (fun x => h x ^ 3 * deriv p x / (12 * μ)) x = U / 2 * deriv h x)
    (x y : ℝ) : filmFlux μ U h p x = filmFlux μ U h p y := by
  have hdf : Differentiable ℝ (filmFlux μ U h p) := by
    unfold filmFlux
    exact ((hh.const_mul U).div_const 2).sub hd
  refine is_const_of_deriv_eq_zero hdf (fun z => ?_) x y
  have : HasDerivAt (filmFlux μ U h p) (U * deriv h z / 2 - U / 2 * deriv h z) z := by
    rw [← hR z]
    exact (((hh z).hasDerivAt.const_mul U).div_const 2).sub (hd z).hasDerivAt
  rw [this.deriv]
  ring

end Reynolds

/-! ### The plane slider bearing -/

section Slider

variable {μ U h₁ h₂ L x : ℝ}

/-- The **gap of a plane slider bearing**, `h(x) = h₁ - (h₁ - h₂) x / L`: from `h₁` at the inlet
`x = 0` to `h₂` at the outlet `x = L`. -/
def sliderGap (h₁ h₂ L x : ℝ) : ℝ := h₁ - (h₁ - h₂) * x / L

/-- The gap `hₘ = 2 h₁ h₂ / (h₁ + h₂)` at the point of maximum pressure. -/
def sliderHm (h₁ h₂ : ℝ) : ℝ := 2 * h₁ * h₂ / (h₁ + h₂)

/-- The **slider-bearing pressure**
`p(x) = 6μU (h₁ - h₂) x (L - x) / (L (h₁ + h₂) h(x)²)`. -/
def sliderPres (μ U h₁ h₂ L x : ℝ) : ℝ :=
  6 * μ * U * (h₁ - h₂) * x * (L - x) / (L * (h₁ + h₂) * sliderGap h₁ h₂ L x ^ 2)

/-- The **load capacity** (per unit width) `W = ∫₀ᴸ p dx` of the slider bearing. -/
def sliderLoad (μ U h₁ h₂ L : ℝ) : ℝ := ∫ x in (0 : ℝ)..L, sliderPres μ U h₁ h₂ L x

/-- Derivative of the gap: `h' = -(h₁ - h₂)/L`. -/
theorem hasDerivAt_sliderGap (x : ℝ) :
    HasDerivAt (sliderGap h₁ h₂ L) (-((h₁ - h₂) / L)) x := by
  exact ((((hasDerivAt_id' x).const_mul (h₁ - h₂)).div_const L).const_sub h₁).congr_deriv
    (by simp)

/-- The gap at the inlet is `h₁`. -/
theorem sliderGap_zero : sliderGap h₁ h₂ L 0 = h₁ := by simp [sliderGap]

/-- The gap at the outlet is `h₂`. -/
theorem sliderGap_length (hL : L ≠ 0) : sliderGap h₁ h₂ L L = h₂ := by
  simp [sliderGap, hL]

/-- The gap as a weighted mean: `h(x) = (h₁ (L - x) + h₂ x) / L`. -/
theorem sliderGap_eq (hL : L ≠ 0) : sliderGap h₁ h₂ L x = (h₁ * (L - x) + h₂ * x) / L := by
  unfold sliderGap
  field_simp
  ring

/-- The gap is positive on `[0, L]`. -/
theorem sliderGap_pos (h₁0 : 0 < h₁) (h₂0 : 0 < h₂) (hL : 0 < L) (hx : x ∈ Icc 0 L) :
    0 < sliderGap h₁ h₂ L x := by
  rw [sliderGap_eq hL.ne']
  apply div_pos _ hL
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0; nlinarith
  · nlinarith [mul_nonneg h₁0.le (sub_nonneg.2 hx.2)]

/-- The classical form of the pressure,
`p = 6μU L (h₁ - h)(h - h₂) / ((h₁² - h₂²) h²)`. -/
theorem sliderPres_eq_classical (hL : L ≠ 0) :
    sliderPres μ U h₁ h₂ L x = 6 * μ * U * L * (h₁ - sliderGap h₁ h₂ L x) *
      (sliderGap h₁ h₂ L x - h₂) / ((h₁ ^ 2 - h₂ ^ 2) * sliderGap h₁ h₂ L x ^ 2) := by
  have e1 : h₁ - sliderGap h₁ h₂ L x = (h₁ - h₂) * x / L := by simp [sliderGap]
  have e2 : sliderGap h₁ h₂ L x - h₂ = (h₁ - h₂) * (L - x) / L := by
    unfold sliderGap; field_simp; ring
  rw [e1, e2, sliderPres]
  rcases eq_or_ne h₁ h₂ with h | h
  · subst h; simp
  rcases eq_or_ne (h₁ + h₂) 0 with h' | h'
  · have : h₁ ^ 2 - h₂ ^ 2 = 0 := by
      rw [show h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) by ring, h', mul_zero]
    simp [this, h']
  have hs : h₁ - h₂ ≠ 0 := sub_ne_zero.2 h
  rw [show h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) by ring]
  field_simp

/-- Ambient pressure at the inlet: `p(0) = 0`. -/
theorem sliderPres_zero : sliderPres μ U h₁ h₂ L 0 = 0 := by simp [sliderPres]

/-- Ambient pressure at the outlet: `p(L) = 0`. -/
theorem sliderPres_length : sliderPres μ U h₁ h₂ L L = 0 := by simp [sliderPres]

/-- The slider pressure solves the integrated Reynolds equation
`p' = 6μU (h - hₘ) / h³`. -/
theorem hasDerivAt_sliderPres (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0) (hx : sliderGap h₁ h₂ L x ≠ 0) :
    HasDerivAt (sliderPres μ U h₁ h₂ L)
      (6 * μ * U * (sliderGap h₁ h₂ L x - sliderHm h₁ h₂) / sliderGap h₁ h₂ L x ^ 3) x := by
  have hN : HasDerivAt (fun x => 6 * μ * U * (h₁ - h₂) * x * (L - x))
      (6 * μ * U * (h₁ - h₂) * (L - x) - 6 * μ * U * (h₁ - h₂) * x) x := by
    exact (((hasDerivAt_id' x).const_mul (6 * μ * U * (h₁ - h₂))).mul
      ((hasDerivAt_id' x).const_sub L)).congr_deriv (by ring)
  have hD : HasDerivAt (fun x => L * (h₁ + h₂) * sliderGap h₁ h₂ L x ^ 2)
      (L * (h₁ + h₂) * (2 * sliderGap h₁ h₂ L x * -((h₁ - h₂) / L))) x := by
    have := ((hasDerivAt_sliderGap (h₁ := h₁) (h₂ := h₂) (L := L) x).pow 2).const_mul
      (L * (h₁ + h₂))
    convert this using 2
    simp
  have hD0 : L * (h₁ + h₂) * sliderGap h₁ h₂ L x ^ 2 ≠ 0 := by positivity
  refine HasDerivAt.congr_deriv (f := sliderPres μ U h₁ h₂ L) (hN.div hD hD0) ?_
  unfold sliderHm
  unfold sliderGap at hx ⊢
  field_simp
  ring


/-- The flux of the slider-bearing film is constant, `q = U hₘ / 2`: the pressure satisfies the
Reynolds equation with ambient pressure at both ends. -/
theorem sliderFlux_eq (hμ : μ ≠ 0) (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0) (hx : sliderGap h₁ h₂ L x ≠ 0) :
    filmFlux μ U (sliderGap h₁ h₂ L) (sliderPres μ U h₁ h₂ L) x = U * sliderHm h₁ h₂ / 2 := by
  unfold filmFlux
  rw [(hasDerivAt_sliderPres (μ := μ) (U := U) hL hs hx).deriv]
  field_simp
  ring

/-- The slider pressure is continuous on `[0, L]`. -/
theorem continuousOn_sliderPres (h₁0 : 0 < h₁) (h₂0 : 0 < h₂) (hL : 0 < L) :
    ContinuousOn (sliderPres μ U h₁ h₂ L) (Icc 0 L) := fun x hx =>
  (hasDerivAt_sliderPres hL.ne' (by positivity)
    (sliderGap_pos h₁0 h₂0 hL hx).ne').continuousAt.continuousWithinAt

/-- **Uniqueness**: a pressure with `p' = 6μU (h - H)/h³` on `[0, L]` for some constant `H`
(i.e. with constant flux `q = U H / 2`) and `p(0) = p(L) = 0` has `H = hₘ` and is the slider
pressure. -/
theorem sliderPres_eq_of_reynolds (h₁0 : 0 < h₁) (h₂0 : 0 < h₂) (hL : 0 < L) (hμU : μ * U ≠ 0)
    {p : ℝ → ℝ} {H : ℝ}
    (hp : ∀ x ∈ Icc 0 L, HasDerivAt p
      (6 * μ * U * (sliderGap h₁ h₂ L x - H) / sliderGap h₁ h₂ L x ^ 3) x)
    (hp0 : p 0 = 0) (hpL : p L = 0) :
    H = sliderHm h₁ h₂ ∧ ∀ x ∈ Icc 0 L, p x = sliderPres μ U h₁ h₂ L x := by
  have hs : h₁ + h₂ ≠ 0 := by positivity
  set f := fun x => p x - sliderPres μ U h₁ h₂ L x with hf
  have hg : ∀ x ∈ Icc 0 L, 0 < sliderGap h₁ h₂ L x := fun x hx => sliderGap_pos h₁0 h₂0 hL hx
  have hd : ∀ x ∈ Icc 0 L, HasDerivAt f
      (6 * μ * U * (sliderHm h₁ h₂ - H) / sliderGap h₁ h₂ L x ^ 3) x := by
    intro x hx
    refine ((hp x hx).sub (hasDerivAt_sliderPres hL.ne' hs (hg x hx).ne')).congr_deriv ?_
    have := (hg x hx).ne'
    field_simp
    ring
  have hfc : ContinuousOn f (Icc 0 L) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hL hfc
    (by simp [hf, hp0, hpL, sliderPres_zero, sliderPres_length])
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
  have hgc := (hg c (Ioo_subset_Icc_self hc)).ne'
  have hH : H = sliderHm h₁ h₂ := by
    rw [div_eq_zero_iff] at hc0
    rcases hc0 with h | h
    · have : μ * U * (sliderHm h₁ h₂ - H) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' hμU
      · linarith
    · exact absurd h (pow_ne_zero 3 hgc)
  refine ⟨hH, fun x hx => ?_⟩
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0; simp [hp0, sliderPres_zero]
  obtain ⟨d, hd', hdd⟩ := exists_hasDerivAt_eq_slope f _ h0
    (hfc.mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hd y ⟨hy.1.le, hy.2.le.trans hx.2⟩)
  rw [hH, sub_self, mul_zero, zero_div] at hdd
  have : f x - f 0 = 0 := by
    have := hdd.symm
    rwa [div_eq_zero_iff, or_iff_left (by linarith)] at this
  simp only [hf, hp0, sliderPres_zero, sub_zero] at this
  linarith

/-- A **converging wedge** (`h₁ > h₂ > 0`) generates a **positive pressure** inside the bearing. -/
theorem sliderPres_pos (hμ : 0 < μ) (hU : 0 < U) (h₂0 : 0 < h₂) (h12 : h₂ < h₁) (hL : 0 < L)
    (hx : x ∈ Ioo 0 L) : 0 < sliderPres μ U h₁ h₂ L x := by
  have h₁0 := h₂0.trans h12
  have hg := sliderGap_pos h₁0 h₂0 hL (Ioo_subset_Icc_self hx)
  have h1 : 0 < h₁ - h₂ := sub_pos.2 h12
  have h2 : 0 < L - x := sub_pos.2 hx.2
  have h3 := hx.1
  unfold sliderPres
  exact div_pos (by have := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
    (by norm_num : (0 : ℝ) < 6) hμ) hU) h1) h3) h2; exact this) (by positivity)

/-- A **diverging wedge** (`0 < h₁ < h₂`) gives a **negative pressure**: no load support. -/
theorem sliderPres_neg (hμ : 0 < μ) (hU : 0 < U) (h₁0 : 0 < h₁) (h12 : h₁ < h₂) (hL : 0 < L)
    (hx : x ∈ Ioo 0 L) : sliderPres μ U h₁ h₂ L x < 0 := by
  have h₂0 := h₁0.trans h12
  have hg := sliderGap_pos h₁0 h₂0 hL (Ioo_subset_Icc_self hx)
  have h1 : 0 < h₂ - h₁ := sub_pos.2 h12
  have h2 : 0 < L - x := sub_pos.2 hx.2
  have h3 := hx.1
  have : sliderPres μ U h₁ h₂ L x = -(6 * μ * U * (h₂ - h₁) * x * (L - x) /
      (L * (h₁ + h₂) * sliderGap h₁ h₂ L x ^ 2)) := by
    unfold sliderPres; ring
  rw [this, neg_lt_zero]
  exact div_pos (by have := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
    (by norm_num : (0 : ℝ) < 6) hμ) hU) h1) h3) h2; exact this) (by positivity)

/-- The pressure is stationary exactly where the gap is `hₘ`: `p' = 0 ↔ h = hₘ`. -/
theorem deriv_sliderPres_eq_zero_iff (hμU : μ * U ≠ 0) (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0)
    (hx : sliderGap h₁ h₂ L x ≠ 0) :
    deriv (sliderPres μ U h₁ h₂ L) x = 0 ↔ sliderGap h₁ h₂ L x = sliderHm h₁ h₂ := by
  rw [(hasDerivAt_sliderPres hL hs hx).deriv, div_eq_zero_iff,
    or_iff_left (pow_ne_zero 3 hx), mul_eq_zero, sub_eq_zero]
  have : 6 * μ * U ≠ 0 := by
    rw [mul_assoc]; exact mul_ne_zero (by norm_num) hμU
  simp [this]

/-- The gap equals `hₘ` at `xₘ = L h₁ / (h₁ + h₂)`, the point of maximum pressure. -/
theorem sliderGap_xm (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0) :
    sliderGap h₁ h₂ L (L * h₁ / (h₁ + h₂)) = sliderHm h₁ h₂ := by
  unfold sliderGap sliderHm
  field_simp
  ring

/-- The peak pressure `p_max = 3μU L (h₁ - h₂) / (2 h₁ h₂ (h₁ + h₂))` exceeds the pressure by a
perfect square: `p_max - p = 3μU L ((h₁ + h₂) h - 2h₁h₂)² / (2 h₁ h₂ (h₁² - h₂²) h²)`. -/
theorem sliderPres_max_sub (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0) (h12 : h₁ ≠ h₂) (h₁0 : h₁ ≠ 0)
    (h₂0 : h₂ ≠ 0) (hx : sliderGap h₁ h₂ L x ≠ 0) :
    3 * μ * U * L * (h₁ - h₂) / (2 * h₁ * h₂ * (h₁ + h₂)) - sliderPres μ U h₁ h₂ L x =
      3 * μ * U * L * ((h₁ + h₂) * sliderGap h₁ h₂ L x - 2 * h₁ * h₂) ^ 2 /
        (2 * h₁ * h₂ * (h₁ ^ 2 - h₂ ^ 2) * sliderGap h₁ h₂ L x ^ 2) := by
  have hd : h₁ - h₂ ≠ 0 := sub_ne_zero.2 h12
  rw [sliderPres_eq_classical hL, show h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) by ring]
  field_simp
  ring

/-- For a converging wedge the pressure is at most
`p_max = 3μU L (h₁ - h₂) / (2 h₁ h₂ (h₁ + h₂))`, attained at `xₘ = L h₁ / (h₁ + h₂)`. -/
theorem sliderPres_le_max (hμ : 0 ≤ μ) (hU : 0 ≤ U) (h₂0 : 0 < h₂) (h12 : h₂ < h₁)
    (hL : 0 < L) (hx : x ∈ Icc 0 L) :
    sliderPres μ U h₁ h₂ L x ≤ 3 * μ * U * L * (h₁ - h₂) / (2 * h₁ * h₂ * (h₁ + h₂)) ∧
      sliderPres μ U h₁ h₂ L (L * h₁ / (h₁ + h₂)) =
        3 * μ * U * L * (h₁ - h₂) / (2 * h₁ * h₂ * (h₁ + h₂)) := by
  have h₁0 : 0 < h₁ := h₂0.trans h12
  have hs : h₁ + h₂ ≠ 0 := by positivity
  have hg := sliderGap_pos h₁0 h₂0 hL hx
  have hsq : 0 < h₁ ^ 2 - h₂ ^ 2 := by nlinarith
  have hxm : L * h₁ / (h₁ + h₂) ∈ Icc 0 L := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hgm := sliderGap_pos h₁0 h₂0 hL hxm
  constructor
  · have := sliderPres_max_sub (μ := μ) (U := U) hL.ne' hs h12.ne' h₁0.ne' h₂0.ne' hg.ne'
    have : 0 ≤ 3 * μ * U * L * ((h₁ + h₂) * sliderGap h₁ h₂ L x - 2 * h₁ * h₂) ^ 2 /
        (2 * h₁ * h₂ * (h₁ ^ 2 - h₂ ^ 2) * sliderGap h₁ h₂ L x ^ 2) := by positivity
    linarith
  · have := sliderPres_max_sub (μ := μ) (U := U) hL.ne' hs h12.ne' h₁0.ne' h₂0.ne' hgm.ne'
    rw [sliderGap_xm hL.ne' hs, sliderHm] at this
    have e : (h₁ + h₂) * (2 * h₁ * h₂ / (h₁ + h₂)) - 2 * h₁ * h₂ = 0 := by
      field_simp; ring
    rw [e] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      sub_eq_zero] at this
    rw [sliderGap_xm hL.ne' hs, sliderHm] at hgm
    exact this.symm

/-! ### Load capacity -/

/-- An antiderivative of the slider pressure:
`F(x) = 6μU L / (h₁² - h₂²) · (-x - A log h(x) - B / h(x))` with `A = (h₁ + h₂) L / (h₁ - h₂)`
and `B = h₁ h₂ L / (h₁ - h₂)`. -/
def sliderPrim (μ U h₁ h₂ L x : ℝ) : ℝ :=
  6 * μ * U * L / (h₁ ^ 2 - h₂ ^ 2) * (-x - (h₁ + h₂) * L / (h₁ - h₂) *
    Real.log (sliderGap h₁ h₂ L x) - h₁ * h₂ * L / (h₁ - h₂) / sliderGap h₁ h₂ L x)

/-- `F' = p` where the gap is positive. -/
theorem hasDerivAt_sliderPrim (hL : L ≠ 0) (hs : h₁ + h₂ ≠ 0) (h12 : h₁ ≠ h₂)
    (hx : sliderGap h₁ h₂ L x ≠ 0) :
    HasDerivAt (sliderPrim μ U h₁ h₂ L) (sliderPres μ U h₁ h₂ L x) x := by
  have hd : h₁ - h₂ ≠ 0 := sub_ne_zero.2 h12
  have hg := hasDerivAt_sliderGap (h₁ := h₁) (h₂ := h₂) (L := L) x
  have := ((((hasDerivAt_id' x).neg).sub ((hg.log hx).const_mul
    ((h₁ + h₂) * L / (h₁ - h₂)))).sub ((hg.inv hx).const_mul (h₁ * h₂ * L / (h₁ - h₂)))).const_mul
    (6 * μ * U * L / (h₁ ^ 2 - h₂ ^ 2))
  refine HasDerivAt.congr_deriv (f := sliderPrim μ U h₁ h₂ L) (by
    convert this using 1; funext y
    simp only [sliderPrim, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply]; ring) ?_
  rw [sliderPres_eq_classical hL, show h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) by ring]
  field_simp
  ring

/-- The **load capacity** of the plane slider bearing,
`W = 6μU L² / (h₁ - h₂)² · (log(h₁/h₂) - 2(h₁ - h₂)/(h₁ + h₂))`. -/
theorem sliderLoad_eq (h₁0 : 0 < h₁) (h₂0 : 0 < h₂) (h12 : h₁ ≠ h₂) (hL : 0 < L) :
    sliderLoad μ U h₁ h₂ L = 6 * μ * U * L ^ 2 / (h₁ - h₂) ^ 2 *
      (Real.log (h₁ / h₂) - 2 * (h₁ - h₂) / (h₁ + h₂)) := by
  have hs : h₁ + h₂ ≠ 0 := by positivity
  have hd : h₁ - h₂ ≠ 0 := sub_ne_zero.2 h12
  unfold sliderLoad
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := sliderPrim μ U h₁ h₂ L)
    (fun x hx => hasDerivAt_sliderPrim hL.ne' hs h12 (sliderGap_pos h₁0 h₂0 hL
      (by rwa [uIcc_of_le hL.le] at hx)).ne')
    ((continuousOn_sliderPres h₁0 h₂0 hL).intervalIntegrable_of_Icc hL.le)]
  unfold sliderPrim
  rw [sliderGap_zero, sliderGap_length hL.ne', Real.log_div h₁0.ne' h₂0.ne',
    show h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) by ring]
  field_simp
  ring

/-- The load capacity in terms of the **convergence ratio** `K = h₁/h₂ - 1`:
`W = 6μU L² / (K² h₂²) · (log(1 + K) - 2K/(2 + K))`. -/
theorem sliderLoad_eq_convergence (h₁0 : 0 < h₁) (h₂0 : 0 < h₂) (h12 : h₁ ≠ h₂) (hL : 0 < L) :
    sliderLoad μ U h₁ h₂ L = 6 * μ * U * L ^ 2 / ((h₁ / h₂ - 1) ^ 2 * h₂ ^ 2) *
      (Real.log (1 + (h₁ / h₂ - 1)) - 2 * (h₁ / h₂ - 1) / (2 + (h₁ / h₂ - 1))) := by
  have hs : h₁ + h₂ ≠ 0 := by positivity
  have e1 : (h₁ / h₂ - 1) ^ 2 * h₂ ^ 2 = (h₁ - h₂) ^ 2 := by
    field_simp
  have e2 : 2 * (h₁ / h₂ - 1) / (2 + (h₁ / h₂ - 1)) = 2 * (h₁ - h₂) / (h₁ + h₂) := by
    rw [show h₁ / h₂ - 1 = (h₁ - h₂) / h₂ by field_simp,
      show 2 + (h₁ - h₂) / h₂ = (h₁ + h₂) / h₂ by field_simp; ring]
    field_simp
  rw [sliderLoad_eq h₁0 h₂0 h12 hL, e1, e2, add_sub_cancel]

/-- A converging wedge **supports a positive load**, `W > 0`. -/
theorem sliderLoad_pos (hμ : 0 < μ) (hU : 0 < U) (h₂0 : 0 < h₂) (h12 : h₂ < h₁) (hL : 0 < L) :
    0 < sliderLoad μ U h₁ h₂ L :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuousOn_sliderPres (h₂0.trans h12) h₂0 hL).intervalIntegrable_of_Icc hL.le)
    (fun _ hx => sliderPres_pos hμ hU h₂0 h12 hL hx) hL

/-- A diverging wedge gives a **negative load**, `W < 0`: no load support. -/
theorem sliderLoad_neg (hμ : 0 < μ) (hU : 0 < U) (h₁0 : 0 < h₁) (h12 : h₁ < h₂) (hL : 0 < L) :
    sliderLoad μ U h₁ h₂ L < 0 := by
  have := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuousOn_sliderPres (μ := μ) (U := U) h₁0 (h₁0.trans h12) hL).intervalIntegrable_of_Icc
      hL.le).neg
    (fun _ hx => neg_pos.2 (sliderPres_neg hμ hU h₁0 h12 hL hx)) hL
  simp only [Pi.neg_apply, intervalIntegral.integral_neg, neg_pos] at this
  exact this

/-- As a by-product, `log(h₁/h₂) > 2(h₁ - h₂)/(h₁ + h₂)` for `h₁ > h₂ > 0`. -/
theorem log_div_gt_of_sliderLoad (h₂0 : 0 < h₂) (h12 : h₂ < h₁) :
    2 * (h₁ - h₂) / (h₁ + h₂) < Real.log (h₁ / h₂) := by
  have h := sliderLoad_pos (μ := 1) (U := 1) one_pos one_pos h₂0 h12 one_pos
  rw [sliderLoad_eq (h₂0.trans h12) h₂0 h12.ne' one_pos] at h
  have : 0 < 6 * 1 * 1 * 1 ^ 2 / (h₁ - h₂) ^ 2 := by
    have := sub_pos.2 h12; positivity
  linarith [(pos_iff_pos_of_mul_pos h).1 this]

end Slider

end ContinuumMechanics.Fluids.Lubrication
