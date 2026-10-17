import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import ContinuumMechanics.Beams.EulerBernoulli.Solutions

/-!
# Linear elastic fracture mechanics

**Griffith's energy balance.** A through crack of length `2a` in an infinite plate (plane
stress, per unit thickness) under remote stress `σ` releases the elastic energy `π σ² a² / E`
and creates the surface energy `4 a γₛ`, so the total energy is

`Π(a) = -π σ² a² / E + 4 a γₛ`.

`Π` is concave with a single stationary point, a maximum, at the critical half-length
`a_c = 2 E γₛ / (π σ²)`; the equilibrium is unstable and the crack grows (`dΠ/da < 0`) iff
`a > a_c`. Equivalently the fracture stress is `σ_f = √(2 E γₛ / (π a))` ([Griffith1921]).

**Energy release rate.** With the potential energy `Π_p(a) = -π σ² a² / E` and crack length
`2a`, the energy release rate per crack-tip advance is `G = -dΠ_p/d(2a) = π σ² a / E`. The
mode-I stress intensity factor is `K_I = σ √(π a)`, and **Irwin's relation** reads
`G = K_I² / E'` with `E' = E` (plane stress) or `E' = E / (1 - ν²)` (plane strain); hence
`K_I = K_IC ⇔ G = G_c := K_IC² / E'` ([Irwin1957]).

**Compliance method.** For a body of thickness `B` with load-point compliance `C(a)`
(`δ = C P`), the energy release rate is `G = P² C'(a) / (2B)`, both under fixed load
(`Π = ½ P δ - P δ = -½ P² C`) and under fixed grip (`Π = ½ δ² / C`).

**Double cantilever beam.** Each arm is a cantilever of length `a` with tip deflection
`P a³ / (3 EI)` (`EBBeam.cantileverTip_tip`), so `C(a) = 2 a³ / (3 EI)` and
`G = P² a² / (B EI) = 12 P² a² / (E B² h³)` for `EI = E B h³ / 12`. At fixed load `G` increases
with `a` (unstable growth); at fixed grip `G = 9 EI δ² / (4 B a⁴)` decreases with `a` (stable
growth).

**Crack-tip field.** On the crack line the leading term of the mode-I stress is
`σ_yy = K_I / √(2 π r)`, which scales as `r^{-1/2}` ([Williams1957]).

## Main results

* `hasDerivAt_griffithEnergy`, `griffithEnergy_deriv_criticalHalfLength`: `dΠ/da` vanishes at
  `a_c`; `griffithEnergy_le_criticalHalfLength`: `Π(a) ≤ Π(a_c)`;
  `concaveOn_griffithEnergy`: `Π` is concave.
* `griffithEnergyDeriv_neg_iff`: the crack grows iff `a > a_c`;
  `criticalHalfLength_fractureStress`, `criticalHalfLength_eq_iff`: `σ_f = √(2Eγₛ/(πa))`.
* `hasDerivAt_griffithPotential`: `G = -½ dΠ_p/da = π σ² a / E`;
  `griffithG_eq_sq_stressIntensity`: `G = K_I² / E`; `griffith_criterion`: `dΠ/da = 0 ⇔ G = 2γₛ`.
* `irwin_planeStress`, `irwin_planeStrain`, `fracture_criterion`: `K_I = K_IC ⇔ G = G_c`.
* `hasDerivAt_fixedLoadPotential`, `hasDerivAt_fixedGripPotential`, `fixedLoad_eq_fixedGrip`:
  the compliance formula `G = P² C' / (2B)` under both loading conditions.
* `dcb_deflection`, `dcb_fixedLoad_G`, `dcb_fixedGrip_G`, `dcbLoadG_eq_geometry`,
  `dcbLoadG_strictMonoOn`, `dcbGripG_strictAntiOn`: the double cantilever beam.
* `nearTipStress_scaling`: `σ_yy(λ r) = λ^{-1/2} σ_yy(r)`.

## References

* [Griffith1921] A. A. Griffith, *The phenomena of rupture and flow in solids*, Phil. Trans.
  R. Soc. A 221 (1921).
* [Irwin1957] G. R. Irwin, *Analysis of stresses and strains near the end of a crack traversing
  a plate*, J. Appl. Mech. 24 (1957).
* [Williams1957] M. L. Williams, *On the stress distribution at the base of a stationary crack*,
  J. Appl. Mech. 24 (1957).
* [Anderson2017] T. L. Anderson, *Fracture Mechanics: Fundamentals and Applications*, 4th ed.,
  Ch. 2.
-/

open Real Set

namespace ContinuumMechanics.Fracture

/-! ### Griffith's energy balance -/

/-- The **Griffith total energy** (per unit thickness) of a through crack of length `2a` in an
infinite plate under remote stress `σ`: `Π(a) = -π σ² a² / E + 4 a γₛ`. -/
noncomputable def griffithEnergy (σ E γ a : ℝ) : ℝ := -(π * σ ^ 2 * a ^ 2 / E) + 4 * a * γ

/-- The derivative `dΠ/da = -2 π σ² a / E + 4 γₛ` of the Griffith energy. -/
noncomputable def griffithEnergyDeriv (σ E γ a : ℝ) : ℝ := -(2 * π * σ ^ 2 * a / E) + 4 * γ

/-- The **critical half-length** `a_c = 2 E γₛ / (π σ²)`. -/
noncomputable def criticalHalfLength (σ E γ : ℝ) : ℝ := 2 * E * γ / (π * σ ^ 2)

/-- The **Griffith fracture stress** `σ_f = √(2 E γₛ / (π a))`. -/
noncomputable def fractureStress (E γ a : ℝ) : ℝ := √(2 * E * γ / (π * a))

/-- `dΠ/da = -2 π σ² a / E + 4 γₛ`. -/
theorem hasDerivAt_griffithEnergy (σ E γ a : ℝ) :
    HasDerivAt (griffithEnergy σ E γ) (griffithEnergyDeriv σ E γ a) a := by
  have h := (((hasDerivAt_pow 2 a).const_mul (π * σ ^ 2 / E)).neg).add
    ((hasDerivAt_id a).const_mul (4 * γ))
  convert h using 1
  · funext x; simp only [griffithEnergy, id, Pi.add_apply, Pi.neg_apply]; ring
  · simp only [griffithEnergyDeriv]; ring

/-- The second derivative `d²Π/da² = -2 π σ² / E`. -/
theorem hasDerivAt_griffithEnergyDeriv (σ E γ a : ℝ) :
    HasDerivAt (griffithEnergyDeriv σ E γ) (-(2 * π * σ ^ 2 / E)) a := by
  have h := ((hasDerivAt_id a).const_mul (2 * π * σ ^ 2 / E)).neg.add_const (4 * γ)
  convert h using 1
  · funext x; simp only [griffithEnergyDeriv, id, Pi.neg_apply]; ring
  · ring

/-- The second derivative of the Griffith energy is negative for `σ ≠ 0`, `E > 0`. -/
theorem griffithEnergy_second_deriv_neg {σ E : ℝ} (hσ : σ ≠ 0) (hE : 0 < E) :
    -(2 * π * σ ^ 2 / E) < 0 := by
  have : 0 < 2 * π * σ ^ 2 / E := by positivity
  linarith

/-- Factorisation `dΠ/da = (2 π σ² / E) (a_c - a)`. -/
theorem griffithEnergyDeriv_eq {σ E : ℝ} (hσ : σ ≠ 0) (hE : E ≠ 0) (γ a : ℝ) :
    griffithEnergyDeriv σ E γ a = 2 * π * σ ^ 2 / E * (criticalHalfLength σ E γ - a) := by
  simp only [griffithEnergyDeriv, criticalHalfLength]
  field_simp
  ring

/-- **Griffith's equilibrium**: `dΠ/da = 0` at `a = a_c`. -/
theorem griffithEnergy_deriv_criticalHalfLength {σ E : ℝ} (hσ : σ ≠ 0) (hE : E ≠ 0) (γ : ℝ) :
    HasDerivAt (griffithEnergy σ E γ) 0 (criticalHalfLength σ E γ) := by
  convert hasDerivAt_griffithEnergy σ E γ (criticalHalfLength σ E γ) using 1
  rw [griffithEnergyDeriv_eq hσ hE, sub_self, mul_zero]

/-- `Π(a_c) - Π(a) = (π σ² / E) (a - a_c)²`. -/
theorem griffithEnergy_criticalHalfLength_sub {σ E : ℝ} (hσ : σ ≠ 0) (hE : E ≠ 0) (γ a : ℝ) :
    griffithEnergy σ E γ (criticalHalfLength σ E γ) - griffithEnergy σ E γ a =
      π * σ ^ 2 / E * (a - criticalHalfLength σ E γ) ^ 2 := by
  simp only [griffithEnergy, criticalHalfLength]
  field_simp
  ring

/-- **The Griffith equilibrium is a maximum** of the total energy: `Π(a) ≤ Π(a_c)`. -/
theorem griffithEnergy_le_criticalHalfLength {σ E : ℝ} (hσ : σ ≠ 0) (hE : 0 < E) (γ a : ℝ) :
    griffithEnergy σ E γ a ≤ griffithEnergy σ E γ (criticalHalfLength σ E γ) := by
  have h := griffithEnergy_criticalHalfLength_sub hσ hE.ne' γ a
  have : 0 ≤ π * σ ^ 2 / E * (a - criticalHalfLength σ E γ) ^ 2 := by positivity
  linarith

/-- **The Griffith energy is concave** (for `E > 0`), so its equilibrium is unstable. -/
theorem concaveOn_griffithEnergy (σ γ : ℝ) {E : ℝ} (hE : 0 < E) :
    ConcaveOn ℝ univ (griffithEnergy σ E γ) := by
  have hc : 0 ≤ π * σ ^ 2 / E := by positivity
  have h1 : ConcaveOn ℝ univ fun a : ℝ => -(π * σ ^ 2 / E * a ^ 2) :=
    (even_two.convexOn_pow.smul hc).neg
  have h2 : ConcaveOn ℝ univ fun a : ℝ => 4 * γ * a :=
    (LinearMap.mulLeft ℝ (4 * γ)).concaveOn convex_univ
  convert h1.add h2 using 1
  funext a
  simp only [griffithEnergy, Pi.add_apply]
  ring

/-- **Crack growth criterion**: the energy decreases with crack growth (`dΠ/da < 0`) iff
`a > a_c`. -/
theorem griffithEnergyDeriv_neg_iff {σ E : ℝ} (hσ : σ ≠ 0) (hE : 0 < E) (γ a : ℝ) :
    griffithEnergyDeriv σ E γ a < 0 ↔ criticalHalfLength σ E γ < a := by
  have hc : 0 < 2 * π * σ ^ 2 / E := by positivity
  rw [griffithEnergyDeriv_eq hσ hE.ne', mul_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; left; exact ⟨hc, by linarith⟩

/-- At the **fracture stress** `σ_f(a)` the critical half-length is exactly `a`. -/
theorem criticalHalfLength_fractureStress {E γ a : ℝ} (hE : 0 < E) (hγ : 0 < γ) (ha : 0 < a) :
    criticalHalfLength (fractureStress E γ a) E γ = a := by
  have hpos : 0 ≤ 2 * E * γ / (π * a) := by positivity
  rw [criticalHalfLength, fractureStress, sq_sqrt hpos]
  field_simp

/-- For `σ > 0` the crack of half-length `a` is critical iff `σ` is the fracture stress. -/
theorem criticalHalfLength_eq_iff {σ E γ a : ℝ} (hσ : 0 < σ) (hE : 0 < E) (hγ : 0 < γ)
    (ha : 0 < a) : criticalHalfLength σ E γ = a ↔ σ = fractureStress E γ a := by
  constructor
  · intro h
    rw [fractureStress, ← h, criticalHalfLength]
    have : 2 * E * γ / (π * (2 * E * γ / (π * σ ^ 2))) = σ ^ 2 := by
      field_simp
    rw [this, sqrt_sq hσ.le]
  · rintro rfl; exact criticalHalfLength_fractureStress hE hγ ha

/-! ### Energy release rate and stress intensity -/

/-- The **potential energy** `Π_p(a) = -π σ² a² / E` (per unit thickness) of the Griffith
crack: the elastic energy released by opening the crack of length `2a`. -/
noncomputable def griffithPotential (σ E a : ℝ) : ℝ := -(π * σ ^ 2 * a ^ 2 / E)

/-- The **energy release rate** `G = π σ² a / E` of the Griffith crack. -/
noncomputable def griffithG (σ E a : ℝ) : ℝ := π * σ ^ 2 * a / E

/-- The mode-I **stress intensity factor** `K_I = σ √(π a)` of the Griffith crack. -/
noncomputable def stressIntensity (σ a : ℝ) : ℝ := σ * √(π * a)

/-- **Energy release rate**: `G = -dΠ_p/d(2a)`, i.e. `dΠ_p/da = -2 G`. -/
theorem hasDerivAt_griffithPotential (σ E a : ℝ) :
    HasDerivAt (griffithPotential σ E) (-(2 * griffithG σ E a)) a := by
  have h := ((hasDerivAt_pow 2 a).const_mul (π * σ ^ 2 / E)).neg
  convert h using 1
  · funext x; simp only [griffithPotential, Pi.neg_apply]; ring
  · simp only [griffithG]; ring

/-- The total energy is the potential energy plus the surface energy `4 a γₛ`. -/
theorem griffithEnergy_eq (σ E γ a : ℝ) :
    griffithEnergy σ E γ a = griffithPotential σ E a + 4 * a * γ := rfl

/-- `dΠ/da = 2 (2 γₛ - G)`. -/
theorem griffithEnergyDeriv_eq_G (σ E γ a : ℝ) :
    griffithEnergyDeriv σ E γ a = 2 * (2 * γ - griffithG σ E a) := by
  simp only [griffithEnergyDeriv, griffithG]; ring

/-- **Griffith's criterion**: `dΠ/da = 0` iff `G = G_c := 2 γₛ`. -/
theorem griffith_criterion (σ E γ a : ℝ) :
    griffithEnergyDeriv σ E γ a = 0 ↔ griffithG σ E a = 2 * γ := by
  rw [griffithEnergyDeriv_eq_G]
  constructor <;> intro h <;> linarith

/-- **Irwin's relation** for the Griffith crack (plane stress): `G = K_I² / E`. -/
theorem griffithG_eq_sq_stressIntensity (σ E : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    griffithG σ E a = stressIntensity σ a ^ 2 / E := by
  rw [griffithG, stressIntensity, mul_pow, sq_sqrt (by positivity)]
  ring

/-- At the fracture stress the stress intensity is `K_I = √(2 E γₛ) = √(E G_c)`. -/
theorem stressIntensity_fractureStress {E γ a : ℝ} (hE : 0 < E) (hγ : 0 < γ) (ha : 0 < a) :
    stressIntensity (fractureStress E γ a) a = √(2 * E * γ) := by
  rw [stressIntensity, fractureStress, ← sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- The **effective modulus** `E'`: `E` in plane stress, `E / (1 - ν²)` in plane strain. -/
noncomputable def effectiveModulus (E ν : ℝ) (planeStrain : Bool) : ℝ :=
  if planeStrain then E / (1 - ν ^ 2) else E

/-- The **energy release rate from the stress intensity**: `G = K_I² / E'`. -/
noncomputable def irwinG (K E' : ℝ) : ℝ := K ^ 2 / E'

/-- **Irwin's relation, plane stress**: `G = K_I² / E` for the Griffith crack. -/
theorem irwin_planeStress (σ E ν : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    griffithG σ E a = irwinG (stressIntensity σ a) (effectiveModulus E ν false) := by
  rw [griffithG_eq_sq_stressIntensity σ E ha]; rfl

/-- **Irwin's relation, plane strain**: `K_I² / E' = (1 - ν²) K_I² / E`. -/
theorem irwin_planeStrain (K E ν : ℝ) (hν : ν ^ 2 ≠ 1) :
    irwinG K (effectiveModulus E ν true) = (1 - ν ^ 2) * K ^ 2 / E := by
  have : (1 - ν ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hν)
  simp only [irwinG, effectiveModulus, ite_true]
  rw [div_div_eq_mul_div]
  ring

/-- **Fracture criterion**: for `K_I, K_IC ≥ 0` and `E' > 0`, `K_I = K_IC` iff
`G = G_c := K_IC² / E'`. -/
theorem fracture_criterion {K KIC E' : ℝ} (hK : 0 ≤ K) (hKIC : 0 ≤ KIC) (hE : 0 < E') :
    K = KIC ↔ irwinG K E' = irwinG KIC E' := by
  constructor
  · rintro rfl; rfl
  · intro h
    simp only [irwinG] at h
    rw [div_left_inj' hE.ne'] at h
    exact (sq_eq_sq₀ hK hKIC).mp h

/-! ### The compliance method -/

/-- The **energy release rate from the compliance**: `G = P² C'(a) / (2 B)`. -/
noncomputable def complianceG (P B dC : ℝ) : ℝ := P ^ 2 * dC / (2 * B)

/-- The potential energy under **fixed load** `P`: `Π = ½ P δ - P δ` with `δ = C(a) P`. -/
noncomputable def fixedLoadPotential (C : ℝ → ℝ) (P a : ℝ) : ℝ :=
  1 / 2 * P * (C a * P) - P * (C a * P)

/-- The potential energy under **fixed grip** `δ`: `Π = ½ δ² / C(a)`. -/
noncomputable def fixedGripPotential (C : ℝ → ℝ) (δ a : ℝ) : ℝ := 1 / 2 * δ ^ 2 / C a

/-- **Compliance method, fixed load**: `-(∂Π/∂a)_P = B G` with `G = P² C' / (2B)`. -/
theorem hasDerivAt_fixedLoadPotential {C : ℝ → ℝ} {dC a : ℝ} (hC : HasDerivAt C dC a)
    (P : ℝ) {B : ℝ} (hB : B ≠ 0) :
    HasDerivAt (fixedLoadPotential C P) (-(B * complianceG P B dC)) a := by
  have h := (hC.mul_const (-(1 / 2) * P ^ 2))
  convert h using 1
  · funext x; simp only [fixedLoadPotential]; ring
  · simp only [complianceG]; field_simp

/-- **Compliance method, fixed grip**: with `δ = C(a) P` and `C(a) ≠ 0`,
`-(∂Π/∂a)_δ = B G` with the same `G = P² C' / (2B)`. -/
theorem hasDerivAt_fixedGripPotential {C : ℝ → ℝ} {dC a : ℝ} (hC : HasDerivAt C dC a)
    (hC0 : C a ≠ 0) {P δ : ℝ} (hδ : δ = C a * P) {B : ℝ} (hB : B ≠ 0) :
    HasDerivAt (fixedGripPotential C δ) (-(B * complianceG P B dC)) a := by
  have h := (hC.inv hC0).const_mul (1 / 2 * δ ^ 2)
  convert h using 1
  · funext x; simp only [fixedGripPotential, Pi.inv_apply]; ring
  · simp only [complianceG, hδ]; field_simp

/-- **Fixed load and fixed grip give the same energy release rate**:
`-(∂Π/∂a)_P = -(∂Π/∂a)_δ` at `δ = C(a) P`. -/
theorem fixedLoad_eq_fixedGrip {C : ℝ → ℝ} {dC a : ℝ} (hC : HasDerivAt C dC a)
    (hC0 : C a ≠ 0) (P : ℝ) :
    deriv (fixedLoadPotential C P) a = deriv (fixedGripPotential C (C a * P)) a := by
  rw [(hasDerivAt_fixedLoadPotential hC P one_ne_zero).deriv,
    (hasDerivAt_fixedGripPotential hC hC0 rfl one_ne_zero).deriv]

/-! ### The double cantilever beam -/

/-- The load-point compliance `C(a) = 2 a³ / (3 EI)` of a **double cantilever beam** with arms
of length `a` and bending stiffness `EI`. -/
noncomputable def dcbCompliance (EI a : ℝ) : ℝ := 2 * a ^ 3 / (3 * EI)

/-- The bending stiffness `EI = E B h³ / 12` of a rectangular arm of width `B`, height `h`. -/
noncomputable def armStiffness (E B h : ℝ) : ℝ := E * B * h ^ 3 / 12

/-- The DCB energy release rate at fixed load: `G = P² a² / (B EI)`. -/
noncomputable def dcbLoadG (P B EI a : ℝ) : ℝ := P ^ 2 * a ^ 2 / (B * EI)

/-- The DCB energy release rate at fixed grip: `G = 9 EI δ² / (4 B a⁴)`. -/
noncomputable def dcbGripG (δ B EI a : ℝ) : ℝ := 9 * EI * δ ^ 2 / (4 * B * a ^ 4)

/-- **DCB opening**: the load-point displacement is twice the cantilever tip deflection,
`δ = 2 P a³ / (3 EI) = C(a) P`. -/
theorem dcb_deflection (b : Beams.EBBeam) (P : ℝ) :
    2 * b.cantileverTip P b.L = dcbCompliance b.EI b.L * P := by
  have := b.EI_pos.ne'
  rw [b.cantileverTip_tip, dcbCompliance]
  field_simp

/-- `C'(a) = 2 a² / EI`. -/
theorem hasDerivAt_dcbCompliance {EI : ℝ} (hEI : EI ≠ 0) (a : ℝ) :
    HasDerivAt (dcbCompliance EI) (2 * a ^ 2 / EI) a := by
  have h := (hasDerivAt_pow 3 a).const_mul (2 / (3 * EI))
  convert h using 1
  · funext x; simp only [dcbCompliance]; ring
  · field_simp; ring

/-- **DCB, fixed load**: the compliance method gives `G = P² a² / (B EI)`. -/
theorem dcb_fixedLoad_G {EI B : ℝ} (hEI : EI ≠ 0) (hB : B ≠ 0) (P a : ℝ) :
    HasDerivAt (fixedLoadPotential (dcbCompliance EI) P) (-(B * dcbLoadG P B EI a)) a := by
  convert hasDerivAt_fixedLoadPotential (hasDerivAt_dcbCompliance hEI a) P hB using 3
  simp only [dcbLoadG, complianceG]
  field_simp

/-- For a rectangular arm, `G = P² a² / (B EI) = 12 P² a² / (E B² h³)`. -/
theorem dcbLoadG_eq_geometry {E B h : ℝ} (hE : E ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (P a : ℝ) :
    dcbLoadG P B (armStiffness E B h) a = 12 * P ^ 2 * a ^ 2 / (E * B ^ 2 * h ^ 3) := by
  simp only [dcbLoadG, armStiffness]
  field_simp

/-- At fixed grip `δ`, the load is `P = δ / C(a)` and `G(P) = 9 EI δ² / (4 B a⁴)`. -/
theorem dcbLoadG_eq_dcbGripG {EI B a : ℝ} (hEI : EI ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (δ : ℝ) :
    dcbLoadG (δ / dcbCompliance EI a) B EI a = dcbGripG δ B EI a := by
  simp only [dcbLoadG, dcbGripG, dcbCompliance]
  field_simp
  ring

/-- **DCB, fixed grip**: the compliance method gives `G = 9 EI δ² / (4 B a⁴)`. -/
theorem dcb_fixedGrip_G {EI B a : ℝ} (hEI : EI ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (δ : ℝ) :
    HasDerivAt (fixedGripPotential (dcbCompliance EI) δ) (-(B * dcbGripG δ B EI a)) a := by
  have hC0 : dcbCompliance EI a ≠ 0 := by simp only [dcbCompliance]; positivity
  have hδ : δ = dcbCompliance EI a * (δ / dcbCompliance EI a) := by field_simp
  convert hasDerivAt_fixedGripPotential (hasDerivAt_dcbCompliance hEI a) hC0 hδ hB using 3
  rw [← dcbLoadG_eq_dcbGripG hEI hB ha]
  simp only [dcbLoadG, complianceG]
  field_simp

/-- **Unstable growth at fixed load**: the DCB energy release rate `P² a² / (B EI)` strictly
increases with the crack length. -/
theorem dcbLoadG_strictMonoOn {P B EI : ℝ} (hP : P ≠ 0) (hB : 0 < B) (hEI : 0 < EI) :
    StrictMonoOn (dcbLoadG P B EI) (Ioi 0) := by
  intro a ha a' _ h
  have hk : 0 < P ^ 2 / (B * EI) := by positivity
  have e : ∀ x, dcbLoadG P B EI x = P ^ 2 / (B * EI) * x ^ 2 := fun x => by
    simp only [dcbLoadG]; ring
  rw [e, e]
  exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h (le_of_lt ha) two_ne_zero) hk

/-- **Stable growth at fixed grip**: the DCB energy release rate `9 EI δ² / (4 B a⁴)` strictly
decreases with the crack length. -/
theorem dcbGripG_strictAntiOn {δ B EI : ℝ} (hδ : δ ≠ 0) (hB : 0 < B) (hEI : 0 < EI) :
    StrictAntiOn (dcbGripG δ B EI) (Ioi 0) := by
  intro a ha a' _ h
  have ha0 : (0 : ℝ) < a := ha
  have hk : 0 < 9 * EI * δ ^ 2 / (4 * B) := by positivity
  have e : ∀ x, dcbGripG δ B EI x = 9 * EI * δ ^ 2 / (4 * B) / x ^ 4 := fun x => by
    simp only [dcbGripG]; rw [div_div]
  rw [e, e]
  exact div_lt_div_of_pos_left hk (by positivity) (pow_lt_pow_left₀ h ha0.le (by norm_num))

/-! ### Crack-tip asymptotics -/

/-- The leading mode-I **near-tip stress** on the crack line: `σ_yy(r) = K_I / √(2 π r)`. -/
noncomputable def nearTipStress (K r : ℝ) : ℝ := K / √(2 * π * r)

/-- **Square-root singularity**: `σ_yy(λ r) = λ^{-1/2} σ_yy(r)` for `λ > 0`. -/
theorem nearTipStress_scaling (K : ℝ) {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    nearTipStress K (lam * r) = lam ^ (-(1 / 2 : ℝ)) * nearTipStress K r := by
  have e : 2 * π * (lam * r) = lam * (2 * π * r) := by ring
  rw [nearTipStress, nearTipStress, e, sqrt_mul hlam.le, rpow_neg hlam.le, ← sqrt_eq_rpow]
  rw [div_mul_eq_div_div, inv_mul_eq_div, div_div, mul_comm, div_div]

end ContinuumMechanics.Fracture
