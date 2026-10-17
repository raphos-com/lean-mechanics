import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Thin-walled beam sections

In a **thin-walled** section the wall thickness `t` is small compared with the other dimensions,
and section properties are computed as integrals along the wall **midline** (arc length `s`),
with the thickness as a weight ([TimoshenkoGere1997], §6.8–6.9; [Megson2013], Ch. 16–18).

* **Second moments of area** (`secondMoment_rect`, `secondMoment_ISection`,
  `secondMoment_parallelAxis`): a rectangle has `I = b h³ / 12`; the thin-wall I-section with
  web `h × t_w` and flanges `b × t_f` has `I = t_w h³ / 12 + 2 b t_f (h/2)²`; and for a
  one-dimensional section integral with centroid at the origin, `I = I_c + A d²`.
* **Shear flow** (`shearFlow`, `channel_flange_shearFlow`, `channel_flange_force`,
  `channel_shearCentre_eq`): in an open section under vertical shear `V`, the shear flow is
  `q(s) = (V/I) ∫₀ˢ y t ds'`. In a flange of a channel (web height `h`, flange width `b`,
  uniform thickness `t`) this is `q = (V/I) t (h/2) s`, with resultant `F = V t h b² / (4 I)`,
  and the **shear centre** lies at `e = F h / V = t h² b² / (4 I)` from the web; with
  `I = t h³/12 + t b h²/2` this is `e = 3 b² / (h + 6 b)`.
* **Bredt–Batho torsion** (`box_torque`, `bredt_twist`, `box_torsionConstant`,
  `tube_torsionConstant`, `tube_polarMoment_exact`): a constant shear flow `q` around a
  rectangular cell `b × h` has torque `2 b h q = 2 A q` about the centre; the twist rate is
  `θ' = T/(4 A² G) ∮ ds/t`, so `J = 4 A² / ∮ ds/t`; for a uniform box `J = 2 t b² h² / (b + h)`,
  and for a thin tube `J = 2 π R³ t`, which agrees with the exact polar moment of the annulus
  `π((R + t/2)⁴ - (R - t/2)⁴)/2 = 2 π R³ t + π R t³ / 2` up to `O(t³)`.
* **Open versus closed** (`slitTube_torsionConstant`, `tube_ratio`, `tendsto_tube_ratio`): a
  slit tube has `J_open = (1/3) ∮ t³ ds = (2π/3) R t³`, so `J_closed / J_open = 3 R² / t²`,
  which tends to `∞` as `t → 0⁺`.

## Main results

* `secondMoment_rect`, `secondMoment_ISection`, `secondMoment_parallelAxis`.
* `channel_flange_force`, `channel_shearCentre_eq`: channel shear centre `e = 3b²/(h + 6b)`.
* `box_torque`: `T = 2 A q` for a rectangular box.
* `box_torsionConstant`, `tube_torsionConstant`, `tube_polarMoment_exact`,
  `tube_polarMoment_sub_le`.
* `slitTube_torsionConstant`, `tube_ratio`, `tendsto_tube_ratio`.

## References

* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §3.8, §6.8–6.9.
* [Megson2013] T. H. G. Megson, *Aircraft Structures for Engineering Students*, Ch. 16–18.
-/

open Real Filter Topology intervalIntegral

noncomputable section

namespace ContinuumMechanics.Beams.ThinWalled

/-! ### (a) Second moments of area -/

/-- The **second moment** `∫_{-h/2}^{h/2} y² w(y) dy` of a section of height `h` whose width at
height `y` is `w y`. -/
def secondMoment (w : ℝ → ℝ) (h : ℝ) : ℝ := ∫ y in (-h / 2)..(h / 2), y ^ 2 * w y

/-- **Rectangle**: `∫_{-h/2}^{h/2} y² b dy = b h³ / 12`. -/
theorem secondMoment_rect (b h : ℝ) : secondMoment (fun _ => b) h = b * h ^ 3 / 12 := by
  unfold secondMoment
  rw [intervalIntegral.integral_mul_const, integral_pow]
  ring

/-- The **thin-wall second moment of an I-section**: the web (thickness `t_w`, `y ∈ [-h/2, h/2]`)
contributes `∫ y² t_w dy`, and each flange midline (length `b`, thickness `t_f`, at `y = ± h/2`)
contributes `∫₀ᵇ (h/2)² t_f ds`. -/
def iSectionMoment (b h tf tw : ℝ) : ℝ :=
  (∫ y in (-h / 2)..(h / 2), y ^ 2 * tw) + (∫ _ in (0 : ℝ)..b, (h / 2) ^ 2 * tf) +
    ∫ _ in (0 : ℝ)..b, (-h / 2) ^ 2 * tf

/-- **I-section**, thin-wall approximation: `I = t_w h³ / 12 + 2 b t_f (h/2)²`. -/
theorem secondMoment_ISection (b h tf tw : ℝ) :
    iSectionMoment b h tf tw = tw * h ^ 3 / 12 + 2 * b * tf * (h / 2) ^ 2 := by
  unfold iSectionMoment
  rw [intervalIntegral.integral_mul_const, integral_pow, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- **Parallel-axis theorem** for a one-dimensional section integral: if the weight `w`
(thickness or width) is continuous and the reference axis passes through the centroid
(`∫ y w = 0`), then the second moment about an axis at distance `d` is `I_c + A d²`, where
`I_c = ∫ y² w` and `A = ∫ w`. -/
theorem secondMoment_parallelAxis {w : ℝ → ℝ} (hw : Continuous w) (a b d : ℝ)
    (hc : ∫ y in a..b, y * w y = 0) :
    ∫ y in a..b, (y + d) ^ 2 * w y =
      (∫ y in a..b, y ^ 2 * w y) + (∫ y in a..b, w y) * d ^ 2 := by
  have h1 : IntervalIntegrable (fun y => y ^ 2 * w y) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun y => y ^ 2 * w y).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun y => 2 * d * (y * w y)) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun y => 2 * d * (y * w y)).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun y => d ^ 2 * w y) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun y => d ^ 2 * w y).intervalIntegrable a b
  have e : (fun y => (y + d) ^ 2 * w y) =
      fun y => (y ^ 2 * w y + 2 * d * (y * w y)) + d ^ 2 * w y := by
    funext y; ring
  rw [e, intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hc]
  ring

/-! ### (b) Shear flow and the shear centre of a channel -/

/-- The **shear flow** in an open thin-walled section under vertical shear `V`:
`q(s) = (V / I) ∫₀ˢ y(s') t(s') ds'`, where `y(s)` is the height of the midline point at arc
length `s` (measured from a free edge) and `t(s)` the wall thickness. -/
def shearFlow (V I : ℝ) (y t : ℝ → ℝ) (s : ℝ) : ℝ := V / I * ∫ s' in (0 : ℝ)..s, y s' * t s'

/-- In the top **flange of a channel** (at height `y = h/2`, uniform thickness `t`, arc length `s`
from the free edge) the shear flow is `q(s) = (V/I) t (h/2) s`. -/
theorem channel_flange_shearFlow (V I h t s : ℝ) :
    shearFlow V I (fun _ => h / 2) (fun _ => t) s = V / I * t * (h / 2) * s := by
  unfold shearFlow
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The **resultant flange force** `F = ∫₀ᵇ q ds = V t h b² / (4 I)` for a channel flange of
width `b`. -/
theorem channel_flange_force (V I h t b : ℝ) :
    ∫ s in (0 : ℝ)..b, shearFlow V I (fun _ => h / 2) (fun _ => t) s =
      V * t * h * b ^ 2 / (4 * I) := by
  simp only [channel_flange_shearFlow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  by_cases hI : I = 0
  · simp [hI]
  · field_simp
    ring

/-- The **shear centre offset** of a channel: the distance `e = F h / V` from the web at which
the vertical shear must act for the flange-force couple `F h` to be balanced (no twist). -/
def channelShearCentre (V I h t b : ℝ) : ℝ := V * t * h * b ^ 2 / (4 * I) * h / V

/-- `e = F h / V = t h² b² / (4 I)` (for `V ≠ 0`). -/
theorem channelShearCentre_eq_moment {V : ℝ} (hV : V ≠ 0) (I h t b : ℝ) :
    channelShearCentre V I h t b = t * h ^ 2 * b ^ 2 / (4 * I) := by
  unfold channelShearCentre
  by_cases hI : I = 0
  · simp [hI]
  · field_simp

/-- The **second moment of a channel** (thin-wall): `I = t h³ / 12 + t b h² / 2`. -/
def channelMoment (h t b : ℝ) : ℝ := t * h ^ 3 / 12 + t * b * h ^ 2 / 2

/-- **Shear centre of a channel**: with `I = t h³/12 + t b h²/2`, `e = 3 b² / (h + 6 b)`. -/
theorem channel_shearCentre_eq {V h t b : ℝ} (hV : V ≠ 0) (hh : 0 < h) (ht : 0 < t)
    (hb : 0 ≤ b) : channelShearCentre V (channelMoment h t b) h t b = 3 * b ^ 2 / (h + 6 * b) := by
  rw [channelShearCentre_eq_moment hV, channelMoment]
  have h6 : 0 < h + 6 * b := by linarith
  rw [div_eq_div_iff (by positivity) h6.ne']
  ring

/-! ### (c) Bredt–Batho torsion of closed thin-walled sections -/

/-- The moment about the origin of a force density `(fx, fy)` acting at `(x, y)`:
`x fy - y fx`. -/
def moment (x y fx fy : ℝ) : ℝ := x * fy - y * fx

/-- The **torque of a constant shear flow** `q` around the rectangular box `[-b/2, b/2] ×
[-h/2, h/2]`, traversed counter-clockwise: the sum over the four sides of `∫ (r × q τ) ds`
with `τ` the unit tangent. -/
def boxTorque (b h q : ℝ) : ℝ :=
  (∫ x in (-b / 2)..(b / 2), moment x (-h / 2) q 0) +
    (∫ y in (-h / 2)..(h / 2), moment (b / 2) y 0 q) +
    (∫ x in (-b / 2)..(b / 2), moment (-x) (h / 2) (-q) 0) +
    ∫ y in (-h / 2)..(h / 2), moment (-b / 2) (-y) 0 (-q)

/-- **Bredt's torque formula** for a rectangular box: `T = 2 b h q = 2 A q`. -/
theorem box_torque (b h q : ℝ) : boxTorque b h q = 2 * (b * h) * q := by
  simp only [boxTorque, moment, mul_zero, zero_sub, sub_zero]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The **Bredt–Batho twist rate** `θ' = T / (4 A² G) ∮ ds/t`, where `L` denotes the line
integral `∮ ds / t`. -/
def twistRate (T A G L : ℝ) : ℝ := T / (4 * A ^ 2 * G) * L

/-- The **torsion constant of a closed cell**: `J = 4 A² / ∮ ds/t`. -/
def torsionConstant (A L : ℝ) : ℝ := 4 * A ^ 2 / L

/-- With `J = 4 A² / ∮ ds/t`, the twist rate satisfies `T = G J θ'`. -/
theorem bredt_twist {T A G L : ℝ} (hA : A ≠ 0) (hG : G ≠ 0) (hL : L ≠ 0) :
    G * torsionConstant A L * twistRate T A G L = T := by
  unfold torsionConstant twistRate
  field_simp

/-- For a uniform box of wall thickness `t`, `∮ ds/t = 2 (b + h) / t`, computed side by side. -/
theorem box_lineIntegral (b h t : ℝ) :
    (∫ _ in (0 : ℝ)..b, 1 / t) + (∫ _ in (0 : ℝ)..h, 1 / t) + (∫ _ in (0 : ℝ)..b, 1 / t) +
      (∫ _ in (0 : ℝ)..h, 1 / t) = 2 * (b + h) / t := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Box section** with uniform thickness: `J = 4 (b h)² / (2 (b + h)/t) = 2 t b² h² / (b + h)`. -/
theorem box_torsionConstant {b h t : ℝ} (hb : 0 < b) (hh : 0 < h) (ht : 0 < t) :
    torsionConstant (b * h) (2 * (b + h) / t) = 2 * t * b ^ 2 * h ^ 2 / (b + h) := by
  unfold torsionConstant
  have : 0 < b + h := by linarith
  field_simp
  ring

/-- For a thin circular tube, `∮ ds/t = ∫₀^{2πR} ds/t = 2 π R / t`. -/
theorem tube_lineIntegral (R t : ℝ) : ∫ _ in (0 : ℝ)..(2 * π * R), 1 / t = 2 * π * R / t := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Thin circular tube**: `J = 4 (π R²)² / (2 π R / t) = 2 π R³ t`. -/
theorem tube_torsionConstant {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    torsionConstant (π * R ^ 2) (2 * π * R / t) = 2 * π * R ^ 3 * t := by
  unfold torsionConstant
  have := pi_pos
  field_simp
  ring

/-- The **exact polar moment** of the annulus with mean radius `R` and thickness `t`:
`π ((R + t/2)⁴ - (R - t/2)⁴) / 2`. -/
def tubePolarMoment (R t : ℝ) : ℝ := π * ((R + t / 2) ^ 4 - (R - t / 2) ^ 4) / 2

/-- The exact polar moment equals `2 π R³ t + π R t³ / 2`: the thin-wall value `2 π R³ t` plus a
correction of order `t³`. -/
theorem tube_polarMoment_exact (R t : ℝ) :
    tubePolarMoment R t = 2 * π * R ^ 3 * t + π * R * t ^ 3 / 2 := by
  unfold tubePolarMoment
  ring

/-- The thin-wall error is `O(t³)`: `|J_exact - 2 π R³ t| ≤ (π |R| / 2) |t|³`. -/
theorem tube_polarMoment_sub_le (R t : ℝ) :
    |tubePolarMoment R t - 2 * π * R ^ 3 * t| ≤ π * |R| / 2 * |t| ^ 3 := by
  rw [tube_polarMoment_exact]
  have e : 2 * π * R ^ 3 * t + π * R * t ^ 3 / 2 - 2 * π * R ^ 3 * t =
      π / 2 * (R * t ^ 3) := by ring
  rw [e, abs_mul, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
  apply le_of_eq
  ring

/-! ### (d) Open versus closed sections -/

/-- The **torsion constant of an open thin-walled section**: `J = (1/3) ∫₀^ℓ t(s)³ ds` over the
midline of length `ℓ`. -/
def openTorsionConstant (ℓ : ℝ) (t : ℝ → ℝ) : ℝ := (1 / 3) * ∫ s in (0 : ℝ)..ℓ, t s ^ 3

/-- **Slit tube**: `J_open = (1/3) ∫₀^{2πR} t³ ds = (2π/3) R t³`. -/
theorem slitTube_torsionConstant (R t : ℝ) :
    openTorsionConstant (2 * π * R) (fun _ => t) = 2 * π / 3 * R * t ^ 3 := by
  unfold openTorsionConstant
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Closed versus open tube**: `J_closed / J_open = 2 π R³ t / ((2π/3) R t³) = 3 R² / t²`. -/
theorem tube_ratio {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    torsionConstant (π * R ^ 2) (2 * π * R / t) / openTorsionConstant (2 * π * R) (fun _ => t) =
      3 * R ^ 2 / t ^ 2 := by
  rw [tube_torsionConstant hR ht, slitTube_torsionConstant]
  have := pi_pos
  field_simp

/-- The ratio `J_closed / J_open = 3 R² / t²` tends to `∞` as `t → 0⁺`: closing a thin section
increases its torsional stiffness without bound. -/
theorem tendsto_tube_ratio {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t => torsionConstant (π * R ^ 2) (2 * π * R / t) /
      openTorsionConstant (2 * π * R) (fun _ => t)) (𝓝[>] 0) atTop := by
  have key : Tendsto (fun t : ℝ => 3 * R ^ 2 / t ^ 2) (𝓝[>] 0) atTop := by
    have h2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) :=
          (continuous_pow 2).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp ht) 2)
    simp only [div_eq_mul_inv]
    exact (tendsto_inv_nhdsGT_zero.comp h2).const_mul_atTop (by positivity)
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (tube_ratio hR (Set.mem_Ioi.mp ht)).symm

end ContinuumMechanics.Beams.ThinWalled
