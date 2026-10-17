import ContinuumMechanics.Fluids.Viscous

/-!
# Pipe flow and pipe networks

Steady flow of a fluid of density `ρ` and viscosity `μ` through circular pipes of radius `R`
(diameter `D = 2R`) and length `L`, driven by the pressure gradient `G = Δp / L`.

* **Laminar friction.** Hagen–Poiseuille flow (`hagenVel`) has flow rate `Q = π G R⁴/(8μ)`
  (`hagen_flowRate`), hence mean velocity `V = Q/(πR²) = G R²/(8μ)`. The **Darcy friction
  factor** is defined by `Δp = f (L/D)(ρV²/2)` and the **Reynolds number** by `Re = ρVD/μ`;
  for laminar flow `f = 64/Re`. The wall shear stress is `τ_w = G R/2` and `f = 8τ_w/(ρV²)`.
* **Head loss and networks.** The Darcy–Weisbach head loss is `h_f = f (L/D) V²/(2g)`. In
  laminar flow `h_f = R_h Q` with the hydraulic resistance `R_h = 128 μ L/(π ρ g D⁴)`; pipes in
  series (common `Q`) add their resistances, pipes in parallel (common `h_f`) add the inverses.
* **Turbulent friction.** The Blasius correlation `f = 0.316 Re^{-1/4}` gives `h_f ∝ V^{7/4}`.
  At the transition Reynolds number `Re = 2300` the laminar value `64/2300 ≈ 0.0278` is smaller
  than the Blasius value `≈ 0.0456`.
* **Borda–Carnot.** For a sudden expansion from area `A₁` to `A₂`, the momentum balance
  `(p₁ - p₂)A₂ = ρQ(V₂ - V₁)` and Bernoulli's equation with a loss give
  `h_L = (V₁ - V₂)²/(2g) = (1 - A₁/A₂)² V₁²/(2g) ≥ 0`.

## Main results

* `hagen_meanVel`: `V = G R²/(8μ)` for Hagen–Poiseuille flow.
* `hagen_darcyFactor`: the laminar friction law `f = 64/Re`.
* `hagen_wallShear`, `hagen_darcyFactor_eq_wallShear`: `τ_w = G R/2` and `f = 8τ_w/(ρV²)`.
* `laminar_headLoss`: `h_f = 128 μ L Q/(π ρ g D⁴)`.
* `series_headLoss`, `parallel_flowRate`, `parallel_equivResistance`: pipe networks.
* `blasius_headLoss_scaling`: `h_f(λV) = λ^{7/4} h_f(V)`.
* `laminarFactor_lt_blasius_2300`: `64/2300 < 0.316 · 2300^{-1/4}`.
* `bordaCarnot_headLoss`, `bordaCarnot_coeff`, `bordaCarnot_headLoss_nonneg`.

## References

* [White2011] F. M. White, *Fluid Mechanics*, 7th ed., §§3.7, 6.4–6.9.
* [Batchelor1967] G. K. Batchelor, *An Introduction to Fluid Dynamics*, §§4.2, 5.15.
-/

noncomputable section

namespace ContinuumMechanics.Fluids.Pipes

open Real Finset Korn Torsion

/-! ### Laminar friction factor -/

section Laminar

variable {ρ μ G R L V p₀ : ℝ}

/-- The **mean velocity** `V = Q/(π R²)` of a flow rate `Q` through a pipe of radius `R`. -/
def meanVel (Q R : ℝ) : ℝ := Q / (π * R ^ 2)

/-- The **Reynolds number** `Re = ρ V D/μ`. -/
def reynolds (ρ V D μ : ℝ) : ℝ := ρ * V * D / μ

/-- The **Darcy friction factor** `f`, defined by `Δp = f (L/D)(ρ V²/2)`. -/
def darcyFactor (Δp L D ρ V : ℝ) : ℝ := Δp / (L / D * (ρ * V ^ 2 / 2))

/-- The mean velocity of **Hagen–Poiseuille flow** is `V = G R²/(8μ)`. -/
theorem hagen_meanVel (hμ : μ ≠ 0) (hR : 0 < R) :
    meanVel (flowRate (hagenVel μ G R) (disk R)) R = G * R ^ 2 / (8 * μ) := by
  rw [meanVel, hagen_flowRate hμ hR.le]
  have := pi_pos
  field_simp

/-- The **laminar friction law** `f = 64/Re` for Hagen–Poiseuille flow, with `Δp = G L`,
`D = 2R` and `V` the mean velocity. -/
theorem hagen_darcyFactor (hρ : ρ ≠ 0) (hμ : μ ≠ 0) (hG : G ≠ 0) (hR : 0 < R) (hL : L ≠ 0) :
    let V := meanVel (flowRate (hagenVel μ G R) (disk R)) R
    darcyFactor (G * L) L (2 * R) ρ V = 64 / reynolds ρ V (2 * R) μ := by
  intro V
  have hV : V = G * R ^ 2 / (8 * μ) := hagen_meanVel hμ hR
  rw [darcyFactor, reynolds, hV]
  have := hR.ne'
  field_simp
  ring

/-- The **wall shear stress** of Hagen–Poiseuille flow: `σ₃₁ = -G x/2`, so on the wall point
`(R, 0, z)` the fluid exerts the shear `τ_w = G R/2` on the wall in the flow direction. -/
theorem hagen_wallShear (hμ : μ ≠ 0) (x : Fin 3 → ℝ) :
    viscStress μ (hagenPres G p₀) (hagenVel μ G R) 2 0 x = -(G * x 0 / 2) := by
  have h2 : (fun y => hagenVel μ G R y 2) = fun y => G / (4 * μ) * (R ^ 2 - y 0 ^ 2 - y 1 ^ 2) :=
    by ext y; simp [hagenVel]
  have h0 : (fun y => hagenVel μ G R y 0) = fun _ => 0 := by ext y; simp [hagenVel]
  simp only [viscStress, h2, h0]
  simp (disch := fun_prop) [pd_mul, pd_const, pd_coord, pd_sub', pd_sq]
  field_simp
  ring

/-- The friction factor in terms of the wall shear stress: `f = 8 τ_w/(ρ V²)` with
`τ_w = G R/2`, `Δp = G L`, `D = 2R`. -/
theorem hagen_darcyFactor_eq_wallShear (hR : R ≠ 0) (hL : L ≠ 0) :
    darcyFactor (G * L) L (2 * R) ρ V = 8 * (G * R / 2) / (ρ * V ^ 2) := by
  rw [darcyFactor]
  rcases eq_or_ne ρ 0 with h | h
  · simp [h]
  rcases eq_or_ne V 0 with h' | h'
  · simp [h']
  field_simp
  ring

end Laminar

/-! ### Head loss and pipe networks -/

section Networks

variable {ρ μ g L D Q : ℝ}

/-- The **Darcy–Weisbach head loss** `h_f = f (L/D) V²/(2g)`. -/
def headLoss (f L D V g : ℝ) : ℝ := f * (L / D) * V ^ 2 / (2 * g)

/-- The **laminar hydraulic resistance** `R_h = 128 μ L/(π ρ g D⁴)` of a pipe. -/
def laminarResistance (μ L ρ g D : ℝ) : ℝ := 128 * μ * L / (π * ρ * g * D ^ 4)

/-- The head loss equals the pressure drop divided by `ρ g`. -/
theorem headLoss_darcyFactor {Δp V : ℝ} (hρ : ρ ≠ 0) (hg : g ≠ 0) (hL : L ≠ 0) (hD : D ≠ 0)
    (hV : V ≠ 0) : headLoss (darcyFactor Δp L D ρ V) L D V g = Δp / (ρ * g) := by
  rw [headLoss, darcyFactor]
  field_simp

/-- **Laminar head loss is linear in the flow rate**: with `f = 64/Re` and mean velocity
`V = Q/(π D²/4)`, `h_f = R_h Q`, `R_h = 128 μ L/(π ρ g D⁴)`. -/
theorem laminar_headLoss (hρ : ρ ≠ 0) (hμ : μ ≠ 0) (hg : g ≠ 0) (hD : D ≠ 0) (hQ : Q ≠ 0) :
    let V := Q / (π * D ^ 2 / 4)
    headLoss (64 / reynolds ρ V D μ) L D V g = laminarResistance μ L ρ g D * Q := by
  intro V
  simp only [V, headLoss, reynolds, laminarResistance]
  have := pi_pos.ne'
  field_simp
  ring

/-- **Pipes in series** carry the same flow `Q`; if each has head loss `hᵢ = Rᵢ Q`, the total
head loss is `(Σ Rᵢ) Q`, i.e. resistances add. -/
theorem series_headLoss {ι : Type*} (s : Finset ι) (Rh h : ι → ℝ) (Q : ℝ)
    (hh : ∀ i ∈ s, h i = Rh i * Q) : ∑ i ∈ s, h i = (∑ i ∈ s, Rh i) * Q := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl hh

/-- **Pipes in parallel** share the head loss `h`; if `Rᵢ Qᵢ = h` with `Rᵢ ≠ 0`, the total flow
is `Σ Qᵢ = Σ h/Rᵢ`. -/
theorem parallel_flowRate {ι : Type*} (s : Finset ι) (Rh q : ι → ℝ) (h : ℝ)
    (hR : ∀ i ∈ s, Rh i ≠ 0) (hq : ∀ i ∈ s, Rh i * q i = h) :
    ∑ i ∈ s, q i = ∑ i ∈ s, h / Rh i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hq i hi]
  field_simp [hR i hi]

/-- The **equivalent resistance** of pipes in parallel: if `1/R = Σ 1/Rᵢ`, the total flow is
`Q = h/R`, i.e. the network behaves as a single pipe of resistance `R`. -/
theorem parallel_equivResistance {ι : Type*} (s : Finset ι) (Rh q : ι → ℝ) (h Req : ℝ)
    (hR : ∀ i ∈ s, Rh i ≠ 0) (hq : ∀ i ∈ s, Rh i * q i = h)
    (hReq : 1 / Req = ∑ i ∈ s, 1 / Rh i) : ∑ i ∈ s, q i = h / Req := by
  rw [parallel_flowRate s Rh q h hR hq, div_eq_mul_one_div h Req, hReq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => div_eq_mul_one_div h (Rh i)

end Networks

/-! ### Turbulent friction: the Blasius correlation -/

section Turbulent

variable {ρ μ g L D V lam : ℝ}

/-- The **Blasius correlation** `f = 0.316 Re^{-1/4}` for turbulent flow in smooth pipes. -/
def blasius (Re : ℝ) : ℝ := 0.316 * Re ^ (-(1 / 4 : ℝ))

/-- The turbulent head loss `h_f(V)` given by the Blasius friction factor. -/
def blasiusHeadLoss (ρ μ L D g V : ℝ) : ℝ := headLoss (blasius (reynolds ρ V D μ)) L D V g

/-- **Blasius scaling** `h_f ∝ V^{7/4}`: `h_f(λV) = λ^{7/4} h_f(V)` for `λ > 0`. -/
theorem blasius_headLoss_scaling (hρ : 0 < ρ) (hμ : 0 < μ) (hD : 0 < D) (hV : 0 < V)
    (hl : 0 < lam) :
    blasiusHeadLoss ρ μ L D g (lam * V) = lam ^ (7 / 4 : ℝ) * blasiusHeadLoss ρ μ L D g V := by
  simp only [blasiusHeadLoss, headLoss, blasius, reynolds]
  have h1 : ρ * (lam * V) * D / μ = lam * (ρ * V * D / μ) := by ring
  have h2 : 0 ≤ ρ * V * D / μ := by positivity
  rw [h1, mul_rpow hl.le h2]
  have h3 : lam ^ (7 / 4 : ℝ) = lam ^ (-(1 / 4 : ℝ)) * lam ^ (2 : ℝ) := by
    rw [← rpow_add hl]; norm_num
  rw [h3, rpow_two]
  ring

/-- Bounds `6.9 < 2300^{1/4} < 7` on the fourth root of the transition Reynolds number. -/
theorem rpow_2300_bounds : 6.9 < (2300 : ℝ) ^ (1 / 4 : ℝ) ∧ (2300 : ℝ) ^ (1 / 4 : ℝ) < 7 := by
  set x := (2300 : ℝ) ^ (1 / 4 : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have h4 : x ^ 4 = 2300 := by
    rw [hx, ← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
  constructor
  · by_contra h
    push Not at h
    have : x ^ 4 ≤ 6.9 ^ 4 := pow_le_pow_left₀ hx0 h 4
    norm_num at this; linarith
  · by_contra h
    push Not at h
    have : 7 ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this; linarith

/-- At the **transition Reynolds number** `Re = 2300`, the laminar friction factor
`64/2300 ≈ 0.0278` is smaller than the Blasius value `0.316 · 2300^{-1/4} ≈ 0.0456`. -/
theorem laminarFactor_lt_blasius_2300 : (64 / 2300 : ℝ) < blasius 2300 := by
  obtain ⟨-, h7⟩ := rpow_2300_bounds
  have hpos : 0 < (2300 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  rw [blasius, rpow_neg (by norm_num), ← div_eq_mul_inv, lt_div_iff₀ hpos]
  nlinarith

/-- Explicit bounds `0.0451 < 0.316 · 2300^{-1/4} < 0.0458` on the Blasius value at
`Re = 2300`. -/
theorem blasius_2300_bounds : 0.0451 < blasius 2300 ∧ blasius 2300 < 0.0458 := by
  obtain ⟨h6, h7⟩ := rpow_2300_bounds
  have hpos : 0 < (2300 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  rw [blasius, rpow_neg (by norm_num), ← div_eq_mul_inv]
  exact ⟨by rw [lt_div_iff₀ hpos]; nlinarith, by rw [div_lt_iff₀ hpos]; nlinarith⟩

end Turbulent

/-! ### Minor losses: the Borda–Carnot sudden expansion -/

section BordaCarnot

variable {ρ g A₁ A₂ V₁ V₂ p₁ p₂ Q hL : ℝ}

/-- **Borda–Carnot head loss**: from continuity `Q = V₁A₁ = V₂A₂`, the momentum balance
`(p₁ - p₂)A₂ = ρQ(V₂ - V₁)` and Bernoulli's equation with loss
`p₁/(ρg) + V₁²/(2g) = p₂/(ρg) + V₂²/(2g) + h_L`, the loss is `h_L = (V₁ - V₂)²/(2g)`. -/
theorem bordaCarnot_headLoss (hρ : ρ ≠ 0) (hg : g ≠ 0) (hA₂ : A₂ ≠ 0) (hQ : Q = V₂ * A₂)
    (hmom : (p₁ - p₂) * A₂ = ρ * Q * (V₂ - V₁))
    (hen : p₁ / (ρ * g) + V₁ ^ 2 / (2 * g) = p₂ / (ρ * g) + V₂ ^ 2 / (2 * g) + hL) :
    hL = (V₁ - V₂) ^ 2 / (2 * g) := by
  have hp : p₁ - p₂ = ρ * V₂ * (V₂ - V₁) := by
    apply mul_right_cancel₀ hA₂
    rw [hmom, hQ]; ring
  have hL' : hL = (p₁ - p₂) / (ρ * g) + (V₁ ^ 2 - V₂ ^ 2) / (2 * g) := by
    rw [sub_div, sub_div]; linarith
  rw [hL', hp]
  field_simp
  ring

/-- The **loss coefficient** of a sudden expansion: `h_L = K V₁²/(2g)` with
`K = (1 - A₁/A₂)²`. -/
theorem bordaCarnot_coeff (hρ : ρ ≠ 0) (hg : g ≠ 0) (hA₂ : A₂ ≠ 0) (hQ : Q = V₂ * A₂)
    (hcont : V₁ * A₁ = V₂ * A₂) (hmom : (p₁ - p₂) * A₂ = ρ * Q * (V₂ - V₁))
    (hen : p₁ / (ρ * g) + V₁ ^ 2 / (2 * g) = p₂ / (ρ * g) + V₂ ^ 2 / (2 * g) + hL) :
    hL = (1 - A₁ / A₂) ^ 2 * V₁ ^ 2 / (2 * g) := by
  rw [bordaCarnot_headLoss hρ hg hA₂ hQ hmom hen]
  have hV₂ : V₂ = V₁ * A₁ / A₂ := by field_simp; linarith
  rw [hV₂]
  field_simp

/-- The Borda–Carnot loss is **nonnegative**: a sudden expansion always dissipates head. -/
theorem bordaCarnot_headLoss_nonneg (hρ : ρ ≠ 0) (hg : 0 < g) (hA₂ : A₂ ≠ 0)
    (hQ : Q = V₂ * A₂) (hmom : (p₁ - p₂) * A₂ = ρ * Q * (V₂ - V₁))
    (hen : p₁ / (ρ * g) + V₁ ^ 2 / (2 * g) = p₂ / (ρ * g) + V₂ ^ 2 / (2 * g) + hL) :
    0 ≤ hL := by
  rw [bordaCarnot_headLoss hρ hg.ne' hA₂ hQ hmom hen]
  positivity

end BordaCarnot

end ContinuumMechanics.Fluids.Pipes
