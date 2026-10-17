import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import ContinuumMechanics.Beams.Winkler
import ContinuumMechanics.Elastostatics.LameCylinder

/-!
# Thin shells of revolution: membrane theory and the bending boundary layer

**Membrane theory.** A thin shell (thickness `t` small compared with its radii) carrying a
pressure `p` mainly by in-plane (membrane) stresses `σ₁`, `σ₂`, constant through the thickness.
Equilibrium of a cut gives the classical pressure-vessel formulas: for a closed circular
cylinder of radius `R` the **hoop stress** `σ_θ = pR/t` and the **axial stress**
`σ_x = pR/(2t)`; for a sphere `σ = pR/(2t)`. Normal equilibrium of a shell element gives the
**Laplace (Young–Laplace) equation** `σ₁/R₁ + σ₂/R₂ = p/t` (written with the curvatures
`κᵢ = 1/Rᵢ`, so that the flat generator of a cylinder is `κ = 0`), which specialises to both.
The membrane hoop stress is the thin-wall limit of Lamé's thick-cylinder solution.

**Bending boundary layer.** Near an edge, axisymmetric bending of a circular cylindrical shell
with flexural rigidity `D = Et³/(12(1 - ν²))` is governed by `D w'''' + (Et/R²) w = p`, a beam on
a Winkler foundation of modulus `k = Et/R²` (`ContinuumMechanics.Beams.Winkler`). Its
characteristic parameter satisfies `β⁴ = k/(4D) = 3(1 - ν²)/(R²t²)`, so edge disturbances
`e^{-βx}(A cos βx + B sin βx)` decay over the length `1/β ∝ √(Rt)`.

## Main results

* Cuts: `hoop_of_cut`, `axial_of_cut`, `sphere_of_cut` (`σ_θ = pR/t`, `σ_x = pR/(2t)`,
  `σ = pR/(2t)`), and `hoop_eq_two_mul_axial`.
* Laplace equation: `laplace_cylinder` (`σ_x · 0 + σ_θ/R = p/t ↔ σ_θ = pR/t`),
  `laplace_sphere` (`σ/R + σ/R = p/t ↔ σ = pR/(2t)`), `cylinder_laplace`, `sphere_laplace`.
* Thin-wall limit of Lamé: `lame_div_hoop_sub_one` (the relative error is
  `t(R + t)/((2R + t)R)`) and `tendsto_lame_div_hoop` (`σ_θ^{Lamé}(R)/(pR/t) → 1` as `t → 0⁺`).
* Membrane strains of a closed cylinder: `hoop_strain` (`ε_θ = pR(2 - ν)/(2Et)`),
  `axial_strain` (`ε_x = pR(1 - 2ν)/(2Et)`), `radial_expansion` (`u = Rε_θ = pR²(2 - ν)/(2Et)`);
  sphere: `sphere_radial_expansion` (`u = pR²(1 - ν)/(2Et)`).
* Bending boundary layer: `beta_pow_four_identity` (`Et/(4DR²) = 3(1 - ν²)/(R²t²)`),
  `shell_beta_pow` (for `β = Winkler.beta D k`), `decay_length_pow`
  (`(1/β)⁴ = R²t²/(3(1 - ν²))`), `decay_length_sq` (`(1/β)² = Rt/√(3(1 - ν²))`),
  `shell_solves` (membrane part `pR²/(Et)` plus Winkler homogeneous solutions solve the shell
  equation), `membrane_part_eq` (the particular solution is the unrestrained membrane radial
  displacement `R σ_θ/E`), `edge_decay`, `tendsto_edge`, `edge_small` (beyond `x = π/β` an edge
  disturbance is reduced below `1/20` of its amplitude bound).

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, 2nd ed., §§105 (membrane theory of shells of revolution), 114–116 (axisymmetric
  bending of cylindrical shells).
* [Ventsel2001] E. Ventsel, T. Krauthammer, *Thin Plates and Shells*, Ch. 13, 15.
* [Hetenyi1946] M. Hetényi, *Beams on Elastic Foundation*, Ch. VIII.
-/

open Set Real Filter Topology
open scoped Real

noncomputable section

namespace ContinuumMechanics.Plates.Shells

/-! ### Membrane theory: pressure vessels -/

/-- Membrane **hoop stress** of a thin cylinder, `σ_θ = pR/t`. -/
def cylHoop (p R t : ℝ) : ℝ := p * R / t

/-- Membrane **axial stress** of a closed thin cylinder, `σ_x = pR/(2t)`. -/
def cylAxial (p R t : ℝ) : ℝ := p * R / (2 * t)

/-- Membrane stress of a thin sphere, `σ = pR/(2t)`. -/
def sphStress (p R t : ℝ) : ℝ := p * R / (2 * t)

/-- **Hoop stress from a longitudinal cut**: cutting a length `ℓ` of cylinder along a diametral
plane, the walls carry `2 σ_θ t ℓ` and the pressure pushes with `p (2R) ℓ`; so
`σ_θ = pR/t`. -/
theorem hoop_of_cut {p R t ℓ σ : ℝ} (ht : t ≠ 0) (hℓ : ℓ ≠ 0)
    (h : 2 * (σ * t * ℓ) = p * (2 * R) * ℓ) : σ = cylHoop p R t := by
  unfold cylHoop
  field_simp
  have := mul_right_cancel₀ hℓ (by linear_combination h / 2 : σ * t * ℓ = p * R * ℓ)
  linarith

/-- **Axial stress from a transverse cut** of a closed cylinder: the wall ring `2πRt` carries
the end-cap force `p πR²`; so `σ_x = pR/(2t)`. -/
theorem axial_of_cut {p R t σ : ℝ} (hR : R ≠ 0) (ht : t ≠ 0)
    (h : σ * (2 * π * R * t) = p * (π * R ^ 2)) : σ = cylAxial p R t := by
  unfold cylAxial
  have hπ := pi_ne_zero
  field_simp
  have : (σ * (2 * t) - p * R) * (π * R) = 0 := by linear_combination h
  linarith [(mul_eq_zero.mp this).resolve_right (mul_ne_zero hπ hR)]

/-- **Sphere from a diametral cut**: the ring `2πRt` carries `p πR²`; so `σ = pR/(2t)`. -/
theorem sphere_of_cut {p R t σ : ℝ} (hR : R ≠ 0) (ht : t ≠ 0)
    (h : σ * (2 * π * R * t) = p * (π * R ^ 2)) : σ = sphStress p R t :=
  axial_of_cut hR ht h

/-- The hoop stress is twice the axial stress (why cylinders split lengthwise). -/
theorem hoop_eq_two_mul_axial (p R t : ℝ) (ht : t ≠ 0) :
    cylHoop p R t = 2 * cylAxial p R t := by
  unfold cylHoop cylAxial
  field_simp

/-- The **Laplace (Young–Laplace) equation** of membrane theory,
`σ₁ κ₁ + σ₂ κ₂ = p/t`, with principal curvatures `κᵢ = 1/Rᵢ` (`κ = 0` for a straight
generator). -/
def Laplace (κ₁ κ₂ σ₁ σ₂ p t : ℝ) : Prop := σ₁ * κ₁ + σ₂ * κ₂ = p / t

/-- **Laplace for a cylinder**: with `κ_x = 0`, `κ_θ = 1/R`, the Laplace equation holds iff
`σ_θ = pR/t` (whatever the axial stress). -/
theorem laplace_cylinder {p R t σx σθ : ℝ} (hR : R ≠ 0) (ht : t ≠ 0) :
    Laplace 0 (1 / R) σx σθ p t ↔ σθ = cylHoop p R t := by
  unfold Laplace cylHoop
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp; ring

/-- The membrane cylinder stresses satisfy the Laplace equation. -/
theorem cylinder_laplace (p R t : ℝ) (hR : R ≠ 0) (ht : t ≠ 0) :
    Laplace 0 (1 / R) (cylAxial p R t) (cylHoop p R t) p t :=
  (laplace_cylinder hR ht).mpr rfl

/-- **Laplace for a sphere**: with `κ₁ = κ₂ = 1/R` and equal stresses, the Laplace equation
`σ/R + σ/R = p/t` holds iff `σ = pR/(2t)`. -/
theorem laplace_sphere {p R t σ : ℝ} (hR : R ≠ 0) (ht : t ≠ 0) :
    Laplace (1 / R) (1 / R) σ σ p t ↔ σ = sphStress p R t := by
  unfold Laplace sphStress
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp; ring

/-- The membrane sphere stress satisfies the Laplace equation. -/
theorem sphere_laplace (p R t : ℝ) (hR : R ≠ 0) (ht : t ≠ 0) :
    Laplace (1 / R) (1 / R) (sphStress p R t) (sphStress p R t) p t :=
  (laplace_sphere hR ht).mpr rfl

/-! ### Thin-wall limit of Lamé's thick cylinder -/

/-- Relative error of the membrane hoop stress against Lamé's bore hoop stress for inner radius
`R`, outer radius `R + t`: `σ_θ^{Lamé}(R)/(pR/t) - 1 = t(R + t)/((2R + t)R)`. -/
theorem lame_div_hoop_sub_one {p R t : ℝ} (hp : p ≠ 0) (hR : 0 < R) (ht : 0 < t) :
    LameCylinder.lameT R (R + t) p 0 R / cylHoop p R t - 1 = t * (R + t) / ((2 * R + t) * R) := by
  have h := LameCylinder.barlow_error R t p hR ht
  have h' : LameCylinder.lameT R (R + t) p 0 R / cylHoop p R t
      = (LameCylinder.lameT R (R + t) p 0 R * t / R) / p := by
    unfold cylHoop
    field_simp
  rw [h', div_sub_one hp, h]
  have : 2 * R + t ≠ 0 := by positivity
  field_simp

/-- **Thin-wall limit**: Lamé's hoop stress at the bore divided by the membrane value `pR/t`
tends to `1` as `t/R → 0` (here `t → 0⁺` at fixed `R`). -/
theorem tendsto_lame_div_hoop {p R : ℝ} (hp : p ≠ 0) (hR : 0 < R) :
    Tendsto (fun t => LameCylinder.lameT R (R + t) p 0 R / cylHoop p R t) (𝓝[>] 0) (𝓝 1) := by
  have h := (LameCylinder.tendsto_barlow R p hR).div_const p
  rw [div_self hp] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := (mem_Ioi.mp ht).ne'
  unfold cylHoop
  field_simp

/-! ### Membrane strains and radial expansion -/

/-- Hoop strain of a closed cylinder, `ε_θ = (σ_θ - ν σ_x)/E = pR(2 - ν)/(2Et)`. -/
theorem hoop_strain (p R t E ν : ℝ) (ht : t ≠ 0) (hE : E ≠ 0) :
    (cylHoop p R t - ν * cylAxial p R t) / E = p * R * (2 - ν) / (2 * E * t) := by
  unfold cylHoop cylAxial
  field_simp

/-- Axial strain of a closed cylinder, `ε_x = (σ_x - ν σ_θ)/E = pR(1 - 2ν)/(2Et)`. -/
theorem axial_strain (p R t E ν : ℝ) (ht : t ≠ 0) (hE : E ≠ 0) :
    (cylAxial p R t - ν * cylHoop p R t) / E = p * R * (1 - 2 * ν) / (2 * E * t) := by
  unfold cylHoop cylAxial
  field_simp

/-- **Radial expansion** of a closed pressurized cylinder, `u = R ε_θ = pR²(2 - ν)/(2Et)`. -/
theorem radial_expansion (p R t E ν : ℝ) (ht : t ≠ 0) (hE : E ≠ 0) :
    R * ((cylHoop p R t - ν * cylAxial p R t) / E) = p * R ^ 2 * (2 - ν) / (2 * E * t) := by
  rw [hoop_strain p R t E ν ht hE]
  field_simp

/-- Radial expansion of a pressurized sphere, `u = R (σ - νσ)/E = pR²(1 - ν)/(2Et)`. -/
theorem sphere_radial_expansion (p R t E ν : ℝ) (ht : t ≠ 0) (hE : E ≠ 0) :
    R * ((sphStress p R t - ν * sphStress p R t) / E) = p * R ^ 2 * (1 - ν) / (2 * E * t) := by
  unfold sphStress
  field_simp

/-! ### Axisymmetric bending of a cylindrical shell: the boundary layer -/

/-- Flexural rigidity of the shell wall, `D = Et³/(12(1 - ν²))`. -/
def flexRigidity (E t ν : ℝ) : ℝ := E * t ^ 3 / (12 * (1 - ν ^ 2))

/-- The hoop-stiffness acting as a Winkler foundation modulus, `k = Et/R²`. -/
def hoopModulus (E t R : ℝ) : ℝ := E * t / R ^ 2

/-- The axisymmetric **cylindrical-shell bending equation** `D w'''' + (Et/R²) w = p` is the
Winkler beam equation with `EI = D`, `k = Et/R²`. -/
def ShellEquation (E t ν R p : ℝ) (w : ℝ → ℝ) : Prop :=
  Beams.Winkler.Equation (flexRigidity E t ν) (hoopModulus E t R) (fun _ => p) w univ

/-- The identity `β⁴ = Et/(4DR²) = 3(1 - ν²)/(R²t²)` for `D = Et³/(12(1 - ν²))`. -/
theorem beta_pow_four_identity {E t ν R : ℝ} (hE : E ≠ 0) (ht : t ≠ 0) (hR : R ≠ 0)
    (hν : 1 - ν ^ 2 ≠ 0) :
    hoopModulus E t R / (4 * flexRigidity E t ν) = 3 * (1 - ν ^ 2) / (R ^ 2 * t ^ 2) := by
  unfold hoopModulus flexRigidity
  field_simp
  ring

/-- Positivity of `D` for `E, t > 0`, `ν² < 1`. -/
theorem flexRigidity_pos {E t ν : ℝ} (hE : 0 < E) (ht : 0 < t) (hν : ν ^ 2 < 1) :
    0 < flexRigidity E t ν := by
  unfold flexRigidity
  have : 0 < 1 - ν ^ 2 := by linarith
  positivity

/-- Positivity of `k = Et/R²`. -/
theorem hoopModulus_pos {E t R : ℝ} (hE : 0 < E) (ht : 0 < t) (hR : 0 < R) :
    0 < hoopModulus E t R := by
  unfold hoopModulus
  positivity

/-- The Winkler parameter of the shell, `β = (k/(4D))^{1/4}`, satisfies
`β⁴ = 3(1 - ν²)/(R²t²)`. -/
theorem shell_beta_pow {E t ν R : ℝ} (hE : 0 < E) (ht : 0 < t) (hR : 0 < R) (hν : ν ^ 2 < 1) :
    Beams.Winkler.beta (flexRigidity E t ν) (hoopModulus E t R) ^ 4 =
      3 * (1 - ν ^ 2) / (R ^ 2 * t ^ 2) := by
  have hD := flexRigidity_pos hE ht hν
  have h := Beams.Winkler.four_mul_beta_pow hD (hoopModulus_pos hE ht hR)
  rw [← beta_pow_four_identity hE.ne' ht.ne' hR.ne' (by linarith), eq_div_iff (by positivity)]
  linarith

/-- **Decay length** of the boundary layer: `(1/β)⁴ = R²t²/(3(1 - ν²))`. -/
theorem decay_length_pow {β t ν R : ℝ} (ht : 0 < t) (hR : 0 < R) (hν : ν ^ 2 < 1)
    (hβ : β ^ 4 = 3 * (1 - ν ^ 2) / (R ^ 2 * t ^ 2)) :
    (1 / β) ^ 4 = R ^ 2 * t ^ 2 / (3 * (1 - ν ^ 2)) := by
  rw [div_pow, hβ, one_pow]
  have : 1 - ν ^ 2 ≠ 0 := by linarith
  field_simp

/-- **Decay length** `1/β ∝ √(Rt)`: `(1/β)² = Rt/√(3(1 - ν²))` for `β > 0`. -/
theorem decay_length_sq {β t ν R : ℝ} (hβ0 : 0 < β) (ht : 0 < t) (hR : 0 < R) (hν : ν ^ 2 < 1)
    (hβ : β ^ 4 = 3 * (1 - ν ^ 2) / (R ^ 2 * t ^ 2)) :
    (1 / β) ^ 2 = R * t / √(3 * (1 - ν ^ 2)) := by
  have hc : 0 < 3 * (1 - ν ^ 2) := by linarith
  have hs := sq_sqrt hc.le
  have hs0 := sqrt_pos.mpr hc
  refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  rw [← pow_mul, decay_length_pow ht hR hν hβ, div_pow, hs]
  ring

/-- **Membrane plus edge solutions**: `w = p/k + e^{βx}(…) + e^{-βx}(…)`, with
`β = (k/(4D))^{1/4}`, solves the shell bending equation `D w'''' + (Et/R²) w = p`. -/
theorem shell_solves {E t ν R : ℝ} (hE : 0 < E) (ht : 0 < t) (hR : 0 < R) (hν : ν ^ 2 < 1)
    (p C₁ C₂ C₃ C₄ : ℝ) :
    ShellEquation E t ν R p (fun x => p / hoopModulus E t R +
      Beams.Winkler.homSol (Beams.Winkler.beta (flexRigidity E t ν) (hoopModulus E t R))
        C₁ C₂ C₃ C₄ x) :=
  Beams.Winkler.uniform_add_homSol_solves (hoopModulus_pos hE ht hR).ne'
    (Beams.Winkler.four_mul_beta_pow (flexRigidity_pos hE ht hν) (hoopModulus_pos hE ht hR)) _
    _ _ _ _

/-- The particular (membrane) solution `p/k = pR²/(Et)` is the radial expansion `R σ_θ/E` of an
unrestrained cylinder under the membrane hoop stress `σ_θ = pR/t` (no axial stress). -/
theorem membrane_part_eq (p E t R : ℝ) (hE : E ≠ 0) (ht : t ≠ 0) (hR : R ≠ 0) :
    p / hoopModulus E t R = R * cylHoop p R t / E := by
  unfold hoopModulus cylHoop
  field_simp

/-- **Edge effects decay exponentially**: an edge disturbance
`e^{-βx}(A cos βx + B sin βx)` is bounded by `(|A| + |B|) e^{-βx}`. -/
theorem edge_decay (β A B x : ℝ) :
    |Beams.Winkler.expTrig (-1) β A B x| ≤ (|A| + |B|) * exp (-(β * x)) :=
  Beams.Winkler.abs_expTrig_neg_le β A B x

/-- Edge disturbances vanish far from the edge (`β > 0`). -/
theorem tendsto_edge {β : ℝ} (hβ : 0 < β) (A B : ℝ) :
    Tendsto (Beams.Winkler.expTrig (-1) β A B) atTop (𝓝 0) :=
  Beams.Winkler.tendsto_expTrig_neg hβ A B

/-- `e^{-π} < 1/20`. -/
theorem exp_neg_pi_lt : exp (-π) < 1 / 20 := by
  have h1 := exp_one_gt_d9
  have h3 : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  have h3' : 20 < exp 3 := by
    have := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    rw [h3]; linarith
  have hπ : exp 3 < exp π := exp_lt_exp.mpr pi_gt_three
  rw [exp_neg, inv_eq_one_div, div_lt_div_iff₀ (exp_pos π) (by norm_num)]
  linarith

/-- **Boundary-layer width**: beyond `x = π/β` an edge disturbance is less than `1/20` of its
amplitude bound `|A| + |B|`, i.e. edge effects are confined to a few multiples of
`1/β ∝ √(Rt)`. -/
theorem edge_small {β A B x : ℝ} (hβ : 0 < β) (hx : π / β ≤ x) (hAB : 0 < |A| + |B|) :
    |Beams.Winkler.expTrig (-1) β A B x| < (|A| + |B|) / 20 := by
  have hbx : π ≤ β * x := by rw [div_le_iff₀ hβ] at hx; linarith
  have he : exp (-(β * x)) ≤ exp (-π) := exp_le_exp.mpr (by linarith)
  calc |Beams.Winkler.expTrig (-1) β A B x| ≤ (|A| + |B|) * exp (-(β * x)) := edge_decay _ _ _ _
    _ ≤ (|A| + |B|) * exp (-π) := by gcongr
    _ < (|A| + |B|) * (1 / 20) := by gcongr; exact exp_neg_pi_lt
    _ = (|A| + |B|) / 20 := by ring

end ContinuumMechanics.Plates.Shells
