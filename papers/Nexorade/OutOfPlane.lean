import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The nexorade unit cell: out-of-plane auxiliary problem

We follow the static (complementary-energy) homogenization of a periodic space frame as a
Kirchhoff–Love plate ([LebeeSab2013]; [Caillerie1984]) for the **square nexorade** of
[Greco2013], Appendix 8.

**Geometry.** The unit cell contains two straight beams, `h` along `e₁` and `v` along `e₂`. Each
beam has four contact points at abscissae `0, a, a + b, 2a + b`: its two ends rest on interior
points of beams of the other family, and its two interior points support ends of beams of the
other family. All joints are spherical (forces only). The periodicity lattice is spanned by
`(a + b, -a)` and `(a, a + b)`, so the cell area is `A = (a + b)² + a²`. Following the contacts
through the lattice, the transverse contact forces of `v` are determined by those of `h`
(action–reaction):

`g₀ = -f₁,  g₁ = -f₃,  g₂ = -f₀,  g₃ = -f₂`,

where `fᵢ` (`gᵢ`) is the transverse force applied to `h` (`v`) at its `i`-th contact point.

**Statics.** Without distributed loads, the shear force is constant and the bending moment linear on
each of the three segments (lengths `a, b, a`); the moment vanishes at both (hinged) ends. An
out-of-plane field is **statically admissible** if both beams are in equilibrium.

**Homogenized quantities.** The macroscopic moment is the cell average of `(m × e₃) ⊗ˢ t`
([Greco2013], (3.5b)); for beams along the axes this gives `M₁₁ = (1/A) ∫_h m`,
`M₂₂ = (1/A) ∫_v m`, `M₁₂ = 0`. The complementary energy of the cell is
`Π = Σ ∫ m² / (2 EI) + Σ ∫ r² / (2 G Sₛ)` (Timoshenko beams), computed exactly for piecewise linear
moments.

## Main results

* `OutOfPlane.admissible_iff`: admissible fields form a line: `f = s (1, -1, -1, 1)` (four-point
  bending of both beams; 1 degree of freedom, [Greco2013], App. 8).
* `OutOfPlane.M11_eq_M22`: **degeneracy**: the cell can only carry hydrostatic moments
  `M₁₁ = M₂₂ = M`, `M₁₂ = 0`.
* `OutOfPlane.energy_eq`: `Π / A = ½ d M²` with the **out-of-plane compliance**
  `d = 2A(2a + 3b) / (3 EI (a + b)²) + 4A / (G Sₛ a (a + b)²)` ([Greco2013], (8.10)).
* `OutOfPlane.localization`: the beam shear and moment fields in terms of `M`
  ([Greco2013], (8.8)).

## References

* [Greco2013] L. Greco, *Nexorade* (homogenization of reciprocal systems), draft 2013.
* [LebeeSab2013] A. Lebée, K. Sab, *Homogenization of a space frame as a thick plate*,
  Computers and Structures (2013).
* [Caillerie1984] D. Caillerie, *Thin elastic and periodic plates*, Math. Methods Appl. Sci. 6
  (1984).
-/

open intervalIntegral

noncomputable section

namespace ContinuumMechanics.Nexorade

/-! ### Linear moment on a segment -/

/-- `∫₀^ℓ m = ℓ (m₀ + m₁) / 2` for the linear moment with end values `m₀, m₁`. -/
theorem integral_linear (ℓ m₀ m₁ : ℝ) (hℓ : ℓ ≠ 0) :
    ∫ x in (0 : ℝ)..ℓ, (m₀ + (m₁ - m₀) * x / ℓ) = ℓ * (m₀ + m₁) / 2 := by
  simp only [mul_div_assoc]
  rw [integral_add (by simp) (by
    exact (continuous_const.mul (continuous_id.div_const ℓ)).intervalIntegrable _ _)]
  simp [integral_div, integral_id]
  field_simp
  ring

/-- `∫₀^ℓ m² = ℓ (m₀² + m₀ m₁ + m₁²) / 3` for the linear moment with end values `m₀, m₁`. -/
theorem integral_linear_sq (ℓ m₀ m₁ : ℝ) (hℓ : ℓ ≠ 0) :
    ∫ x in (0 : ℝ)..ℓ, (m₀ + (m₁ - m₀) * x / ℓ) ^ 2 = ℓ * (m₀ ^ 2 + m₀ * m₁ + m₁ ^ 2) / 3 := by
  set k := (m₁ - m₀) / ℓ
  have e : ∀ x : ℝ, (m₀ + (m₁ - m₀) * x / ℓ) ^ 2 = m₀ ^ 2 + (2 * m₀ * k) * x + k ^ 2 * x ^ 2 :=
    fun x => by simp only [k]; field_simp; ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun x : ℝ => m₀ ^ 2 + 2 * m₀ * k * x) MeasureTheory.volume 0 ℓ :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => k ^ 2 * x ^ 2) MeasureTheory.volume 0 ℓ :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x : ℝ => 2 * m₀ * k * x) MeasureTheory.volume 0 ℓ :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_add i1 i2, integral_add intervalIntegrable_const i3,
    integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  simp only [k, smul_eq_mul]
  field_simp
  ring

/-- Geometric and elastic data of the square nexorade cell: lengths `a > 0`, `b ≥ 0`, bending
stiffness `EI`, shear stiffness `G Sₛ`. -/
structure Cell where
  a : ℝ
  b : ℝ
  EI : ℝ
  GS : ℝ
  a_pos : 0 < a
  b_nonneg : 0 ≤ b
  EI_pos : 0 < EI
  GS_pos : 0 < GS

namespace Cell

variable (c : Cell)

/-- The cell area `A = (a + b)² + a²`. -/
def area : ℝ := (c.a + c.b) ^ 2 + c.a ^ 2

theorem area_pos : 0 < c.area := by have := c.a_pos; unfold area; positivity

/-- Contact forces on one beam, at abscissae `0, a, a + b, 2a + b`. -/
structure Forces where
  f₀ : ℝ
  f₁ : ℝ
  f₂ : ℝ
  f₃ : ℝ

/-- Forces on the `v` beam from those on the `h` beam (action–reaction through the lattice). -/
def partner (f : Forces) : Forces := ⟨-f.f₁, -f.f₃, -f.f₀, -f.f₂⟩

/-- Moments at the contact points (`m(0) = 0`, hinged end). -/
def m₁ (f : Forces) : ℝ := f.f₀ * c.a
def m₂ (f : Forces) : ℝ := c.m₁ f + (f.f₀ + f.f₁) * c.b
def m₃ (f : Forces) : ℝ := c.m₂ f + (f.f₀ + f.f₁ + f.f₂) * c.a

/-- Equilibrium of one beam: zero resultant and zero moment at the far (hinged) end. -/
def BeamEq (f : Forces) : Prop := f.f₀ + f.f₁ + f.f₂ + f.f₃ = 0 ∧ c.m₃ f = 0

/-- A statically admissible out-of-plane field: both beams in equilibrium. -/
def Admissible (f : Forces) : Prop := c.BeamEq f ∧ c.BeamEq (partner f)

/-- `∫ m` along one beam (sum over the three segments of `ℓ (mᵢ + mⱼ) / 2`). -/
def intMoment (f : Forces) : ℝ :=
  c.a * (0 + c.m₁ f) / 2 + c.b * (c.m₁ f + c.m₂ f) / 2 + c.a * (c.m₂ f + c.m₃ f) / 2

/-- Macroscopic bending moments `M₁₁ = (1/A) ∫_h m`, `M₂₂ = (1/A) ∫_v m`. -/
def M11 (f : Forces) : ℝ := c.intMoment f / c.area
def M22 (f : Forces) : ℝ := c.intMoment (partner f) / c.area

/-- Complementary energy of one beam: `∫ m²/(2EI) + ∫ r²/(2GSₛ)`, segment by segment. -/
def beamEnergy (f : Forces) : ℝ :=
  (c.a * (0 ^ 2 + 0 * c.m₁ f + c.m₁ f ^ 2) / 3 +
      c.b * (c.m₁ f ^ 2 + c.m₁ f * c.m₂ f + c.m₂ f ^ 2) / 3 +
      c.a * (c.m₂ f ^ 2 + c.m₂ f * c.m₃ f + c.m₃ f ^ 2) / 3) / (2 * c.EI) +
    (c.a * f.f₀ ^ 2 + c.b * (f.f₀ + f.f₁) ^ 2 + c.a * (f.f₀ + f.f₁ + f.f₂) ^ 2) / (2 * c.GS)

/-- The segment formulas are the integrals of the piecewise-linear moment and the
piecewise-constant shear: `beamEnergy = ∫ m² / (2EI) + ∫ r² / (2GSₛ)`. -/
theorem beamEnergy_eq_integral (f : Forces) :
    c.beamEnergy f =
      ((∫ x in (0 : ℝ)..c.a, (0 + (c.m₁ f - 0) * x / c.a) ^ 2) +
          (∫ x in (0 : ℝ)..c.b, (c.m₁ f + (c.m₂ f - c.m₁ f) * x / c.b) ^ 2) +
          (∫ x in (0 : ℝ)..c.a, (c.m₂ f + (c.m₃ f - c.m₂ f) * x / c.a) ^ 2)) / (2 * c.EI) +
        ((∫ _x in (0 : ℝ)..c.a, f.f₀ ^ 2) + (∫ _x in (0 : ℝ)..c.b, (f.f₀ + f.f₁) ^ 2) +
          (∫ _x in (0 : ℝ)..c.a, (f.f₀ + f.f₁ + f.f₂) ^ 2)) / (2 * c.GS) := by
  have ha := c.a_pos.ne'
  have hmid : (∫ x in (0 : ℝ)..c.b, (c.m₁ f + (c.m₂ f - c.m₁ f) * x / c.b) ^ 2) =
      c.b * (c.m₁ f ^ 2 + c.m₁ f * c.m₂ f + c.m₂ f ^ 2) / 3 := by
    rcases eq_or_ne c.b 0 with hb | hb
    · rw [hb]; simp
    · exact integral_linear_sq _ _ _ hb
  rw [integral_linear_sq _ _ _ ha, integral_linear_sq _ _ _ ha, hmid]
  simp [beamEnergy]

/-- `intMoment` is the integral of the piecewise-linear moment. -/
theorem intMoment_eq_integral (f : Forces) :
    c.intMoment f =
      (∫ x in (0 : ℝ)..c.a, (0 + (c.m₁ f - 0) * x / c.a)) +
        (∫ x in (0 : ℝ)..c.b, (c.m₁ f + (c.m₂ f - c.m₁ f) * x / c.b)) +
        (∫ x in (0 : ℝ)..c.a, (c.m₂ f + (c.m₃ f - c.m₂ f) * x / c.a)) := by
  have ha := c.a_pos.ne'
  have hmid : (∫ x in (0 : ℝ)..c.b, (c.m₁ f + (c.m₂ f - c.m₁ f) * x / c.b)) =
      c.b * (c.m₁ f + c.m₂ f) / 2 := by
    rcases eq_or_ne c.b 0 with hb | hb
    · rw [hb]; simp
    · exact integral_linear _ _ _ hb
  rw [integral_linear _ _ _ ha, integral_linear _ _ _ ha, hmid, intMoment]

/-- Complementary energy of the unit cell. -/
def energy (f : Forces) : ℝ := c.beamEnergy f + c.beamEnergy (partner f)

/-- The four-point-bending field `s (1, -1, -1, 1)`. -/
def fourPoint (s : ℝ) : Forces := ⟨s, -s, -s, s⟩

/-- **Admissible out-of-plane fields** are exactly the four-point-bending fields: one degree of
freedom. [Greco2013], App. 8. -/
theorem admissible_iff (f : Forces) : c.Admissible f ↔ ∃ s, f = fourPoint s := by
  have ha := c.a_pos
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩
    obtain ⟨f₀, f₁, f₂, f₃⟩ := f
    simp only [partner, m₃, m₂, m₁] at h1 h2 h4
    -- with `p = f₁ + f₀`, `q = f₃ - f₀`: `b p - a q = 0` and `(2a + b) p + (a + b) q = 0`
    have hb := c.b_nonneg
    have hK : 0 < 2 * c.a ^ 2 + 2 * c.a * c.b + c.b ^ 2 := by positivity
    have hp : (2 * c.a ^ 2 + 2 * c.a * c.b + c.b ^ 2) * (f₁ + f₀) = 0 := by
      linear_combination (c.a + c.b) * h2 - c.a * h4 - (c.a ^ 2 + c.a * c.b) * h1
    have hp' := (mul_eq_zero.mp hp).resolve_left hK.ne'
    have hq : c.a * (f₃ - f₀) = 0 := by linear_combination -h2 + c.a * h1 + c.b * hp'
    have hq' := (mul_eq_zero.mp hq).resolve_left ha.ne'
    refine ⟨f₀, ?_⟩
    rw [fourPoint, show f₁ = -f₀ by linarith, show f₂ = -f₀ by linarith,
      show f₃ = f₀ by linarith]
  · rintro ⟨s, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [fourPoint, partner, m₃, m₂, m₁] <;> ring

theorem partner_fourPoint (s : ℝ) : partner (fourPoint s) = fourPoint s := by
  simp [partner, fourPoint]

/-- **Degeneracy**: every admissible field carries a hydrostatic moment `M₁₁ = M₂₂`
(and `M₁₂ = 0` since the beams are aligned with the axes). [Greco2013], App. 8. -/
theorem M11_eq_M22 {f : Forces} (hf : c.Admissible f) : c.M11 f = c.M22 f := by
  obtain ⟨s, rfl⟩ := (c.admissible_iff f).1 hf
  rw [M22, partner_fourPoint, M11]

theorem M11_fourPoint (s : ℝ) : c.M11 (fourPoint s) = s * c.a * (c.a + c.b) / c.area := by
  simp only [M11, intMoment, m₃, m₂, m₁, fourPoint]
  ring

/-- **Localization**: the admissible field carrying the hydrostatic moment `M` has end shear
`s = M A / (a (a + b))` (shear `s, 0, -s` and moment `0 ↗ s a → s a ↘ 0`: four-point bending).
[Greco2013], (8.8). -/
theorem localization (M : ℝ) :
    c.Admissible (fourPoint (M * c.area / (c.a * (c.a + c.b)))) ∧
      c.M11 (fourPoint (M * c.area / (c.a * (c.a + c.b)))) = M := by
  have ha := c.a_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  have hA := c.area_pos.ne'
  refine ⟨(c.admissible_iff _).2 ⟨_, rfl⟩, ?_⟩
  rw [M11_fourPoint]
  field_simp

/-- The **out-of-plane compliance** `d = 2A(2a + 3b) / (3EI(a + b)²) + 4A / (GSₛ a (a + b)²)`.
[Greco2013], (8.10). -/
def compliance : ℝ :=
  2 * c.area * (2 * c.a + 3 * c.b) / (3 * c.EI * (c.a + c.b) ^ 2) +
    4 * c.area / (c.GS * c.a * (c.a + c.b) ^ 2)

/-- **Hill–Mandel**: the energy density of the cell carrying the hydrostatic moment `M` is
`Π / A = ½ d M²`. [Greco2013], (3.3), (8.10). -/
theorem energy_eq {f : Forces} (hf : c.Admissible f) :
    c.energy f / c.area = c.compliance * c.M11 f ^ 2 / 2 := by
  obtain ⟨s, rfl⟩ := (c.admissible_iff f).1 hf
  have ha := c.a_pos.ne'
  have hab : c.a + c.b ≠ 0 := by have := c.a_pos; have := c.b_nonneg; positivity
  have hA := c.area_pos.ne'
  have hE := c.EI_pos.ne'
  have hG := c.GS_pos.ne'
  rw [M11_fourPoint, energy, partner_fourPoint]
  simp only [beamEnergy, compliance, m₃, m₂, m₁, fourPoint, area]
  field_simp
  ring

/-- The **out-of-plane stiffness** `D = 1/d` of the equivalent (degenerate) plate. -/
def stiffness : ℝ := c.compliance⁻¹

theorem compliance_pos : 0 < c.compliance := by
  have := c.a_pos; have := c.b_nonneg; have := c.EI_pos; have := c.GS_pos; have := c.area_pos
  unfold compliance
  positivity

end Cell

end ContinuumMechanics.Nexorade

end
