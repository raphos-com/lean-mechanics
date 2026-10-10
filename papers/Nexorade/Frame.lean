import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Nexorade.OutOfPlane

/-!
# Convergence of the nexorade frame to the homogenized plate

The homogenized plate of `OutOfPlane`/`Plate` is *defined* by the static cell problem. Here we
check that it describes the actual frame: we model the **infinite square nexorade** (one beam `h`
and one beam `v` per cell, cells indexed by `n ∈ ℤ²`, spherical joints, Timoshenko beams) under a
transverse load of wave vector `k`, solve it exactly, and prove that, as the wavelength becomes
large compared with the cell (`k → 0`), the frame deflection and member forces converge to those
of the plate `D Δ²w = p`, `D = 1/d`.

**Frame.** In cell `n` (origin `n₁ t₁ + n₂ t₂`, `t₁ = (a + b, -a)`, `t₂ = (a, a + b)`) the beam `h`
runs from `(0, 0)` to `(2a + b, 0)`. Its four contact points are four joints of the frame,
numbered `0, …, 3`:

* joint `0` at `(a, 0)`: the end `0` of `v(n)` rests on `h(n)`;
* joint `1` at `(2a + b, 0)`: the end of `h(n)` rests on point `1` of `v(n + (1, 0))`;
* joint `2` at `(0, 0)`: the end of `h(n)` rests on point `2` of `v(n - (0, 1))`;
* joint `3` at `(a + b, 0)`: the end `3` of `v(n + (1, -1))` rests on `h(n)`.

A **frame solution** under the joint loads `q n j` consists of the transverse contact forces of
all beams and the deflections of all joints such that

* every beam is in equilibrium (`BeamEqC`);
* at every joint the forces on the two beams balance the load;
* every beam is **compatible** with its joint deflections: by the principle of complementary
  virtual work (Castigliano–Menabrea), `Σ gᵢ wᵢ = ∫ m_g m_f / EI + ∫ r_g r_f / (G Sₛ)` for every
  self-equilibrated virtual force system `g` on the beam (`Compatible`).

**Bloch reduction.** For a load `q n j = e^{i(n₁ θ₁ + n₂ θ₂)} q⁰ⱼ`, Bloch fields reduce the frame to
a cell problem for the amplitudes (`isFrameSolution_bloch_iff`). Writing the beam forces in the
basis `φ₁ = (1, -1, -1, 1)` (four-point bending), `φ₂` of self-equilibrated systems, the joint
equations are `B(ω) X = Q` and the compatibility equations `K(ω) W = C X`, `ωᵢ = e^{iθᵢ}`, with

`det B = det K = -4a(a + b) ω₁ ω₂ (2 cos θ₁ + 2 cos θ₂ - 4)`,

the symbol of the discrete Laplacian of the lattice. So for `θ ∉ 2πℤ²` the Bloch solution exists
and is unique (`exists_unique_bloch`), and it is explicit.

**Convergence.** For the load `p(x) = p₀ e^{i k·x}` lumped at the joints (`p₀ A / 4` each),
`θᵢ = k · tᵢ` and `θ₁² + θ₂² = A |k|²`. As `k → 0`:

* `|k|² ×` the contact forces of both beams tend to the four-point-bending field
  `s (1, -1, -1, 1)` with `s = -p₀ A / (a (a + b))`: the localization (22) of the plate moment
  `M = p₀ / |k|²` (with `OutOfPlane`'s sign convention for `m`);
* the deflection of every joint divided by the plate deflection `p₀ d e^{i k·x} / |k|⁴` tends to
  `1` (`tendsto_deflection_ratio`).

This proves the scale separation assumed by the paper for the nexorade under single-mode loads;
the general frame-to-plate convergence ([Caillerie1984], [LebeeSab2013]) is not formalised.

## References

* [GrecoLebeeDouthe2013] L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of
  reciprocal systems using homogenization techniques* (2013).
* [Caillerie1984] D. Caillerie, *Thin elastic and periodic plates*, Math. Methods Appl. Sci.
  (1984).
* [LebeeSab2013] A. Lebée, K. Sab, *Homogenization of a space frame as a thick plate*,
  Computers and Structures (2013).
-/

open Matrix Filter Topology

noncomputable section

namespace ContinuumMechanics.Nexorade

/-! ### The Bloch matrices -/

section Algebra

variable (a b ω₁ ω₂ : ℂ)

/-- The joint equations in the coordinates `(s_h, u_h, s_v, u_v)` (rows 3–4 multiplied by `ω₂`). -/
def staticsMat : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-1, 2*a + b, 1, -b;
     1, b, -ω₁, ω₁*(2*a + b);
     ω₂, -b*ω₂, -1, -2*a - b;
     -ω₂, -ω₂*(2*a + b), ω₁, b*ω₁]

/-- The adjugate of `staticsMat`. -/
def staticsAdj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-2*ω₁*(4*a^2*ω₂ + a*b*ω₁*ω₂ + 4*a*b*ω₂ - a*b + b^2*ω₁*ω₂ + b^2*ω₂),
      -2*(2*a^2*ω₁ + 2*a^2*ω₂ + a*b*ω₁ + 3*a*b*ω₂ + b^2*ω₁*ω₂ + b^2*ω₂),
      -2*ω₁*(2*a^2*ω₁ + 2*a^2*ω₂ + 3*a*b*ω₁ + a*b*ω₂ + b^2*ω₁ + b^2),
      2*(-4*a^2*ω₁ + a*b*ω₁*ω₂ - 4*a*b*ω₁ - a*b - b^2*ω₁ - b^2);
    -2*ω₁*(a*ω₁*ω₂ - 2*a*ω₂ + a + b*ω₁*ω₂ - b*ω₂), -2*(a*ω₁ - a*ω₂ + b*ω₁*ω₂ - b*ω₂),
      -2*ω₁*(a*ω₁ - a*ω₂ + b*ω₁ - b), 2*(a*ω₁*ω₂ - 2*a*ω₁ + a - b*ω₁ + b);
    -2*ω₂*(2*a^2*ω₁*ω₂ + 2*a^2 + 3*a*b*ω₁*ω₂ + a*b + b^2*ω₁*ω₂ + b^2*ω₁),
      2*ω₂*(-4*a^2 + a*b*ω₁ - a*b*ω₂ - 4*a*b - b^2*ω₂ - b^2),
      -2*(4*a^2*ω₁*ω₂ + 4*a*b*ω₁*ω₂ + a*b*ω₁ - a*b*ω₂ + b^2*ω₁*ω₂ + b^2*ω₁),
      -2*(2*a^2*ω₁*ω₂ + 2*a^2 + a*b*ω₁*ω₂ + 3*a*b + b^2*ω₂ + b^2);
    -2*ω₂*(a*ω₁*ω₂ - a + b*ω₁*ω₂ - b*ω₁), -2*ω₂*(a*ω₁ + a*ω₂ - 2*a + b*ω₂ - b),
      -2*(2*a*ω₁*ω₂ - a*ω₁ - a*ω₂ + b*ω₁*ω₂ - b*ω₁), -2*(a*ω₁*ω₂ - a + b*ω₂ - b)]

/-- The compatibility equations for the joint deflections (rows 3–4 multiplied by `ω₁`). -/
def compatMat : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-1, 1, 1, -1;
     2*a + b, b, -b, -2*a - b;
     ω₁, -1, -ω₁*ω₂, ω₂;
     -b*ω₁, 2*a + b, -ω₁*ω₂*(2*a + b), b*ω₂]

/-- The adjugate of `compatMat`. -/
def compatAdj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![2*ω₂*(-4*a^2*ω₁ + a*b*ω₁*ω₂ - 4*a*b*ω₁ - a*b - b^2*ω₁ - b^2),
      -2*ω₂*(a*ω₁*ω₂ - 2*a*ω₁ + a - b*ω₁ + b),
      -2*(2*a^2*ω₁*ω₂ + 2*a^2 + a*b*ω₁*ω₂ + 3*a*b + b^2*ω₂ + b^2),
      2*(a*ω₁*ω₂ - a + b*ω₂ - b);
    -2*ω₁*ω₂*(2*a^2*ω₁ + 2*a^2*ω₂ + 3*a*b*ω₁ + a*b*ω₂ + b^2*ω₁ + b^2),
      2*ω₁*ω₂*(a*ω₁ - a*ω₂ + b*ω₁ - b),
      -2*(4*a^2*ω₁*ω₂ + 4*a*b*ω₁*ω₂ + a*b*ω₁ - a*b*ω₂ + b^2*ω₁*ω₂ + b^2*ω₁),
      2*(2*a*ω₁*ω₂ - a*ω₁ - a*ω₂ + b*ω₁*ω₂ - b*ω₁);
    -2*(2*a^2*ω₁ + 2*a^2*ω₂ + a*b*ω₁ + 3*a*b*ω₂ + b^2*ω₁*ω₂ + b^2*ω₂),
      2*(a*ω₁ - a*ω₂ + b*ω₁*ω₂ - b*ω₂),
      2*(-4*a^2 + a*b*ω₁ - a*b*ω₂ - 4*a*b - b^2*ω₂ - b^2),
      2*(a*ω₁ + a*ω₂ - 2*a + b*ω₂ - b);
    -2*ω₁*(4*a^2*ω₂ + a*b*ω₁*ω₂ + 4*a*b*ω₂ - a*b + b^2*ω₁*ω₂ + b^2*ω₂),
      2*ω₁*(a*ω₁*ω₂ - 2*a*ω₂ + a + b*ω₁*ω₂ - b*ω₂),
      -2*(2*a^2*ω₁*ω₂ + 2*a^2 + 3*a*b*ω₁*ω₂ + a*b + b^2*ω₁*ω₂ + b^2*ω₁),
      2*(a*ω₁*ω₂ - a + b*ω₁*ω₂ - b*ω₁)]

/-- `ω₁ ω₂ (ω₁ + ω₁⁻¹ + ω₂ + ω₂⁻¹ - 4)`: the determinants are `-4a(a + b)` times this. -/
def blochDet : ℂ := ω₁ ^ 2 * ω₂ + ω₁ * ω₂ ^ 2 - 4 * ω₁ * ω₂ + ω₁ + ω₂

theorem staticsAdj_mul :
    staticsAdj a b ω₁ ω₂ * staticsMat a b ω₁ ω₂ = (-4 * a * (a + b) * blochDet ω₁ ω₂) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [staticsAdj, staticsMat, blochDet, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem staticsMat_mul :
    staticsMat a b ω₁ ω₂ * staticsAdj a b ω₁ ω₂ = (-4 * a * (a + b) * blochDet ω₁ ω₂) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [staticsAdj, staticsMat, blochDet, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem compatAdj_mul :
    compatAdj a b ω₁ ω₂ * compatMat a b ω₁ ω₂ = (-4 * a * (a + b) * blochDet ω₁ ω₂) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [compatAdj, compatMat, blochDet, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem compatMat_mul :
    compatMat a b ω₁ ω₂ * compatAdj a b ω₁ ω₂ = (-4 * a * (a + b) * blochDet ω₁ ω₂) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [compatAdj, compatMat, blochDet, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem staticsAdj_one_mulVec (P : ℂ) :
    staticsAdj a b 1 1 *ᵥ ![P, P, P, P] =
      ![-16 * P * ((a + b) ^ 2 + a ^ 2), 0, -16 * P * ((a + b) ^ 2 + a ^ 2), 0] := by
  funext i; fin_cases i <;> simp [staticsAdj, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem compatAdj_one_mulVec (x : ℂ) (j : Fin 4) :
    (compatAdj a b 1 1 *ᵥ ![x, 0, x, 0]) j = -8 * x * ((a + b) ^ 2 + a ^ 2) := by
  fin_cases j <;> simp [compatAdj, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Solving `M x = y` with an explicit adjugate. -/
theorem eq_smul_adj_mulVec {M N : Matrix (Fin 4) (Fin 4) ℂ} {δ : ℂ} (hδ : δ ≠ 0)
    (hNM : N * M = δ • 1) {x y : Fin 4 → ℂ} (h : M *ᵥ x = y) : x = δ⁻¹ • N *ᵥ y := by
  rw [← h, mulVec_mulVec, hNM, smul_mulVec, one_mulVec, smul_smul, inv_mul_cancel₀ hδ, one_smul]

theorem mulVec_smul_adj_mulVec {M N : Matrix (Fin 4) (Fin 4) ℂ} {δ : ℂ} (hδ : δ ≠ 0)
    (hMN : M * N = δ • 1) (y : Fin 4 → ℂ) : M *ᵥ (δ⁻¹ • N *ᵥ y) = y := by
  rw [mulVec_smul, mulVec_mulVec, hMN, smul_mulVec, one_mulVec, smul_smul, inv_mul_cancel₀ hδ,
    one_smul]

end Algebra

/-! ### Beams with complex contact forces -/

namespace Cell

variable (c : Cell)

/-- Moments at the contact points `a, a + b, 2a + b` (`m(0) = 0`, hinged end). -/
def mc₁ (f : Fin 4 → ℂ) : ℂ := f 0 * c.a
def mc₂ (f : Fin 4 → ℂ) : ℂ := c.mc₁ f + (f 0 + f 1) * c.b
def mc₃ (f : Fin 4 → ℂ) : ℂ := c.mc₂ f + (f 0 + f 1 + f 2) * c.a

/-- Equilibrium of one beam. -/
def BeamEqC (f : Fin 4 → ℂ) : Prop := f 0 + f 1 + f 2 + f 3 = 0 ∧ c.mc₃ f = 0

/-- `∫₀^ℓ` of the product of two linear functions with end values `p, q` and `p', q'`. -/
def segBil (ℓ p q p' q' : ℂ) : ℂ := ℓ * (2 * p * p' + p * q' + q * p' + 2 * q * q') / 6

/-- The complementary-energy bilinear form of one beam:
`∫ m_g m_f / EI + ∫ r_g r_f / (G Sₛ)`. -/
def bil (g f : Fin 4 → ℂ) : ℂ :=
  (segBil c.a 0 (c.mc₁ g) 0 (c.mc₁ f) + segBil c.b (c.mc₁ g) (c.mc₂ g) (c.mc₁ f) (c.mc₂ f) +
      segBil c.a (c.mc₂ g) (c.mc₃ g) (c.mc₂ f) (c.mc₃ f)) / c.EI +
    (c.a * (g 0 * f 0) + c.b * ((g 0 + g 1) * (f 0 + f 1)) +
      c.a * ((g 0 + g 1 + g 2) * (f 0 + f 1 + f 2))) / c.GS

/-- `bil` is the polarization of the beam complementary energy `beamEnergy`. -/
theorem bil_ofReal (f : Forces) :
    c.bil ![f.f₀, f.f₁, f.f₂, f.f₃] ![f.f₀, f.f₁, f.f₂, f.f₃] = 2 * (c.beamEnergy f : ℂ) := by
  simp only [bil, segBil, mc₁, mc₂, mc₃, beamEnergy, m₁, m₂, m₃]
  push_cast
  simp
  ring

/-- Joint deflections are **compatible** with a beam carrying the contact forces `f`: complementary
virtual work against every self-equilibrated virtual force system. -/
def Compatible (f w : Fin 4 → ℂ) : Prop := ∀ g, c.BeamEqC g → ∑ i, g i * w i = c.bil g f

/-- Four-point bending `(1, -1, -1, 1)`. -/
def φ₁ : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- The second self-equilibrated system `(-b, 2a + b, -(2a + b), b)`. -/
def φ₂ : Fin 4 → ℂ := ![-c.b, 2 * c.a + c.b, -(2 * c.a + c.b), c.b]

/-- Coordinates of a self-equilibrated system in the basis `φ₁, φ₂`. -/
def sCoord (f : Fin 4 → ℂ) : ℂ := -(f 1 + f 2) / 2
def uCoord (f : Fin 4 → ℂ) : ℂ := (f 1 - f 2) / (2 * (2 * c.a + c.b))

/-- The beam flexibilities `bil φ₁ φ₁` and `bil φ₂ φ₂` (and `bil φ₁ φ₂ = 0`). -/
def flexS : ℂ := 2 * c.a / c.GS + c.a ^ 2 * (2 * c.a + 3 * c.b) / (3 * c.EI)
def flexU : ℂ := c.a * c.b * (2 * c.a + c.b) * (6 * c.EI + c.GS * c.a * c.b) / (3 * c.EI * c.GS)

theorem len_ne_zero : (2 * c.a + c.b : ℂ) ≠ 0 := by
  have := c.a_pos; have := c.b_nonneg
  exact_mod_cast (show (2 * c.a + c.b : ℝ) ≠ 0 by positivity)

theorem beamEqC_iff (f : Fin 4 → ℂ) :
    c.BeamEqC f ↔ f = sCoord f • φ₁ + c.uCoord f • c.φ₂ := by
  have hl := c.len_ne_zero
  have hl' : (c.a : ℂ) * 2 + c.b ≠ 0 := by rw [mul_comm]; exact hl
  constructor
  · rintro ⟨h1, h2⟩
    simp only [mc₃, mc₂, mc₁] at h2
    have e0 : f 0 = -((c.a + c.b) * f 1 + c.a * f 2) / (2 * c.a + c.b) := by
      rw [eq_div_iff hl]; linear_combination h2
    have e3 : f 3 = -f 0 - f 1 - f 2 := by linear_combination h1
    funext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cons_val,
        cons_val_zero, cons_val_one, sCoord, neg_add_rev, φ₁, smul_cons, smul_eq_mul,
      mul_one, mul_neg, smul_empty, uCoord, φ₂, Pi.add_apply]
    · rw [e0]; field_simp; ring
    · field_simp; ring
    · field_simp; ring
    · rw [e3, e0]; field_simp; ring
  · intro h
    rw [h]
    constructor <;> simp [mc₃, mc₂, mc₁, φ₁, φ₂] <;> ring

theorem beamEqC_φ₁ : c.BeamEqC φ₁ := by
  constructor <;> simp [mc₃, mc₂, mc₁, φ₁]

theorem beamEqC_φ₂ : c.BeamEqC c.φ₂ := by
  constructor <;> simp [mc₃, mc₂, mc₁, φ₂]
  ring

theorem beamEqC_comb (s u : ℂ) : c.BeamEqC (s • φ₁ + u • c.φ₂) := by
  constructor <;> simp [mc₃, mc₂, mc₁, φ₁, φ₂] <;> ring

theorem bil_comb (s u s' u' : ℂ) :
    c.bil (s' • φ₁ + u' • c.φ₂) (s • φ₁ + u • c.φ₂) =
      s' * (c.flexS * s) + u' * (c.flexU * u) := by
  have hE : (c.EI : ℂ) ≠ 0 := by exact_mod_cast c.EI_pos.ne'
  have hG : (c.GS : ℂ) ≠ 0 := by exact_mod_cast c.GS_pos.ne'
  simp [bil, segBil, mc₁, mc₂, mc₃, φ₁, φ₂, flexS, flexU]
  field_simp
  ring

/-- Compatibility in the basis `φ₁, φ₂`: `φ₁ · w = c_s s`, `φ₂ · w = c_u u`. -/
theorem bil_φ₁ (s u : ℂ) : c.bil φ₁ (s • φ₁ + u • c.φ₂) = c.flexS * s := by
  simpa using c.bil_comb s u 1 0

theorem bil_φ₂ (s u : ℂ) : c.bil c.φ₂ (s • φ₁ + u • c.φ₂) = c.flexU * u := by
  simpa using c.bil_comb s u 0 1

/-- Compatibility in the basis `φ₁, φ₂`: `φ₁ · w = c_s s`, `φ₂ · w = c_u u`. -/
theorem compatible_iff (s u : ℂ) (w : Fin 4 → ℂ) :
    c.Compatible (s • φ₁ + u • c.φ₂) w ↔
      (∑ i, φ₁ i * w i = c.flexS * s ∧ ∑ i, c.φ₂ i * w i = c.flexU * u) := by
  constructor
  · intro h
    exact ⟨(h _ c.beamEqC_φ₁).trans (c.bil_φ₁ s u), (h _ c.beamEqC_φ₂).trans (c.bil_φ₂ s u)⟩
  · rintro ⟨h1, h2⟩ g hg
    rw [(c.beamEqC_iff g).1 hg, bil_comb, ← h1, ← h2]
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### The infinite frame -/

/-- Contact deflections of `h(n)` (contacts at joints `2, 0, 3, 1` of cell `n`). -/
def hDefl (w : ℤ × ℤ → Fin 4 → ℂ) (n : ℤ × ℤ) : Fin 4 → ℂ := ![w n 2, w n 0, w n 3, w n 1]

/-- Contact deflections of `v(n)` (joint `0` of `n`, `1` of `n - (1, 0)`, `2` of `n + (0, 1)`, `3`
of `n - (1, -1)`). -/
def vDefl (w : ℤ × ℤ → Fin 4 → ℂ) (n : ℤ × ℤ) : Fin 4 → ℂ :=
  ![w n 0, w (n - (1, 0)) 1, w (n + (0, 1)) 2, w (n - (1, -1)) 3]

/-- A **solution of the infinite nexorade frame** under the joint loads `q`: contact forces `fh`,
`fv` of the beams `h(n)`, `v(n)` and joint deflections `w`. -/
structure IsFrameSolution (q fh fv w : ℤ × ℤ → Fin 4 → ℂ) : Prop where
  eq_h : ∀ n, c.BeamEqC (fh n)
  eq_v : ∀ n, c.BeamEqC (fv n)
  joint₀ : ∀ n, fh n 1 + fv n 0 = q n 0
  joint₁ : ∀ n, fh n 3 + fv (n + (1, 0)) 1 = q n 1
  joint₂ : ∀ n, fh n 0 + fv (n - (0, 1)) 2 = q n 2
  joint₃ : ∀ n, fh n 2 + fv (n + (1, -1)) 3 = q n 3
  compat_h : ∀ n, c.Compatible (fh n) (hDefl w n)
  compat_v : ∀ n, c.Compatible (fv n) (vDefl w n)

/-! ### Bloch modes -/

/-- The Bloch phase `e^{i(n₁ θ₁ + n₂ θ₂)}` of cell `n`. -/
def phase (θ : ℝ × ℝ) (n : ℤ × ℤ) : ℂ :=
  Complex.exp (((n.1 * θ.1 + n.2 * θ.2 : ℝ) : ℂ) * Complex.I)

theorem phase_add (θ : ℝ × ℝ) (n m : ℤ × ℤ) : phase θ (n + m) = phase θ n * phase θ m := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem phase_ne_zero (θ : ℝ × ℝ) (n : ℤ × ℤ) : phase θ n ≠ 0 := Complex.exp_ne_zero _

theorem phase_zero (θ : ℝ × ℝ) : phase θ 0 = 1 := by simp [phase]

theorem phase_sub (θ : ℝ × ℝ) (n m : ℤ × ℤ) : phase θ (n - m) = phase θ n * (phase θ m)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀ (phase_ne_zero θ m), ← phase_add, sub_add_cancel]

/-- `ω₁ = e^{iθ₁}`, `ω₂ = e^{iθ₂}`. -/
def ω₁ (θ : ℝ × ℝ) : ℂ := phase θ (1, 0)
def ω₂ (θ : ℝ × ℝ) : ℂ := phase θ (0, 1)

theorem ω₁_ne_zero (θ : ℝ × ℝ) : ω₁ θ ≠ 0 := phase_ne_zero _ _
theorem ω₂_ne_zero (θ : ℝ × ℝ) : ω₂ θ ≠ 0 := phase_ne_zero _ _

/-- A Bloch field `n ↦ e^{i n·θ} x`. -/
def bloch (θ : ℝ × ℝ) (x : Fin 4 → ℂ) : ℤ × ℤ → Fin 4 → ℂ := fun n => phase θ n • x

theorem beamEqC_smul {f : Fin 4 → ℂ} (z : ℂ) (h : c.BeamEqC f) : c.BeamEqC (z • f) := by
  obtain ⟨h1, h2⟩ := h
  simp only [BeamEqC, mc₃, mc₂, mc₁, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  exact ⟨by linear_combination z * h1, by linear_combination z * h2⟩

theorem beamEqC_smul_iff {f : Fin 4 → ℂ} {z : ℂ} (hz : z ≠ 0) :
    c.BeamEqC (z • f) ↔ c.BeamEqC f :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hz] using c.beamEqC_smul z⁻¹ h,
    c.beamEqC_smul z⟩

theorem compatible_smul {f w : Fin 4 → ℂ} (z : ℂ) (h : c.Compatible f w) :
    c.Compatible (z • f) (z • w) := by
  intro g hg
  have := h g hg
  simp only [Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul] at this ⊢
  simp only [bil, segBil, mc₁, mc₂, mc₃, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination z * this

theorem compatible_smul_iff {f w : Fin 4 → ℂ} {z : ℂ} (hz : z ≠ 0) :
    c.Compatible (z • f) (z • w) ↔ c.Compatible f w :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hz] using c.compatible_smul z⁻¹ h,
    c.compatible_smul z⟩

/-- The **cell problem for the Bloch amplitudes** `(f, g, w)` of the beam forces and joint
deflections, for the load amplitude `q`. -/
structure IsBloch (θ : ℝ × ℝ) (q f g w : Fin 4 → ℂ) : Prop where
  eq_h : c.BeamEqC f
  eq_v : c.BeamEqC g
  joint₀ : f 1 + g 0 = q 0
  joint₁ : f 3 + ω₁ θ * g 1 = q 1
  joint₂ : f 0 + (ω₂ θ)⁻¹ * g 2 = q 2
  joint₃ : f 2 + ω₁ θ * (ω₂ θ)⁻¹ * g 3 = q 3
  compat_h : c.Compatible f ![w 2, w 0, w 3, w 1]
  compat_v : c.Compatible g ![w 0, (ω₁ θ)⁻¹ * w 1, ω₂ θ * w 2, (ω₁ θ)⁻¹ * ω₂ θ * w 3]

theorem phase_one_neg (θ : ℝ × ℝ) : phase θ (1, -1) = ω₁ θ * (ω₂ θ)⁻¹ := by
  rw [show ((1, -1) : ℤ × ℤ) = (1, 0) - (0, 1) by rfl, phase_sub, ω₁, ω₂]

theorem hDefl_bloch (θ : ℝ × ℝ) (w : Fin 4 → ℂ) (n : ℤ × ℤ) :
    hDefl (bloch θ w) n = phase θ n • ![w 2, w 0, w 3, w 1] := by
  funext i; fin_cases i <;> simp [hDefl, bloch]

theorem vDefl_bloch (θ : ℝ × ℝ) (w : Fin 4 → ℂ) (n : ℤ × ℤ) :
    vDefl (bloch θ w) n =
      phase θ n • ![w 0, (ω₁ θ)⁻¹ * w 1, ω₂ θ * w 2, (ω₁ θ)⁻¹ * ω₂ θ * w 3] := by
  have h1 := phase_sub θ n (1, -1)
  rw [phase_one_neg, mul_inv, inv_inv] at h1
  funext i; fin_cases i <;>
    simp [vDefl, bloch, phase_sub, phase_add, h1, ω₁, ω₂] <;> ring

/-- **Bloch reduction**: Bloch fields solve the infinite frame iff their amplitudes solve the cell
problem. -/
theorem isFrameSolution_bloch_iff (θ : ℝ × ℝ) (q f g w : Fin 4 → ℂ) :
    c.IsFrameSolution (bloch θ q) (bloch θ f) (bloch θ g) (bloch θ w) ↔ c.IsBloch θ q f g w := by
  have hp := phase_ne_zero θ
  have e1 : ∀ n : ℤ × ℤ, phase θ (n + (1, 0)) = phase θ n * ω₁ θ := fun n => phase_add _ _ _
  have e2 : ∀ n : ℤ × ℤ, phase θ (n - (0, 1)) = phase θ n * (ω₂ θ)⁻¹ := fun n => phase_sub _ _ _
  have e3 : ∀ n : ℤ × ℤ, phase θ (n + (1, -1)) = phase θ n * (ω₁ θ * (ω₂ θ)⁻¹) := fun n => by
    rw [phase_add, phase_one_neg]
  constructor
  · intro h
    have j0 := h.joint₀ 0; have j1 := h.joint₁ 0; have j2 := h.joint₂ 0; have j3 := h.joint₃ 0
    simp only [bloch, e1, e2, e3, phase_zero, Pi.smul_apply, smul_eq_mul, one_mul] at j0 j1 j2 j3
    refine ⟨?_, ?_, j0, j1, j2, j3, ?_, ?_⟩
    · simpa [bloch, phase_zero] using h.eq_h 0
    · simpa [bloch, phase_zero] using h.eq_v 0
    · simpa [hDefl_bloch, bloch, phase_zero] using h.compat_h 0
    · simpa [vDefl_bloch, bloch, phase_zero] using h.compat_v 0
  · intro h
    refine ⟨fun n => c.beamEqC_smul _ h.eq_h, fun n => c.beamEqC_smul _ h.eq_v, fun n => ?_,
      fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
    · simp only [bloch, Pi.smul_apply, smul_eq_mul]
      linear_combination phase θ n * h.joint₀
    · simp only [bloch, Pi.smul_apply, smul_eq_mul, e1]
      linear_combination phase θ n * h.joint₁
    · simp only [bloch, Pi.smul_apply, smul_eq_mul, e2]
      linear_combination phase θ n * h.joint₂
    · simp only [bloch, Pi.smul_apply, smul_eq_mul, e3]
      linear_combination phase θ n * h.joint₃
    · rw [hDefl_bloch]; exact c.compatible_smul _ h.compat_h
    · rw [vDefl_bloch]; exact c.compatible_smul _ h.compat_v

/-! ### The explicit Bloch solution -/

/-- Beam forces from the coordinates `X = (s_h, u_h, s_v, u_v)`. -/
def fOf (X : Fin 4 → ℂ) : Fin 4 → ℂ := X 0 • φ₁ + X 1 • c.φ₂
def gOf (X : Fin 4 → ℂ) : Fin 4 → ℂ := X 2 • φ₁ + X 3 • c.φ₂

/-- Right-hand side of the joint equations. -/
def rhsVec (θ : ℝ × ℝ) (q : Fin 4 → ℂ) : Fin 4 → ℂ := ![q 0, q 1, ω₂ θ * q 2, ω₂ θ * q 3]

/-- Right-hand side of the compatibility equations. -/
def compatRhs (θ : ℝ × ℝ) (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![c.flexS * X 0, c.flexU * X 1, ω₁ θ * (c.flexS * X 2), ω₁ θ * (c.flexU * X 3)]

/-- `det B = det K = -4a(a + b) ω₁ ω₂ (ω₁ + ω₁⁻¹ + ω₂ + ω₂⁻¹ - 4)`. -/
def detB (θ : ℝ × ℝ) : ℂ := -4 * c.a * (c.a + c.b) * blochDet (ω₁ θ) (ω₂ θ)

def statics (θ : ℝ × ℝ) : Matrix (Fin 4) (Fin 4) ℂ := staticsMat c.a c.b (ω₁ θ) (ω₂ θ)
def compat (θ : ℝ × ℝ) : Matrix (Fin 4) (Fin 4) ℂ := compatMat c.a c.b (ω₁ θ) (ω₂ θ)

/-- The force coordinates of the Bloch solution. -/
def solX (θ : ℝ × ℝ) (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (c.detB θ)⁻¹ • staticsAdj c.a c.b (ω₁ θ) (ω₂ θ) *ᵥ rhsVec θ q

/-- The joint deflections of the Bloch solution. -/
def solW (θ : ℝ × ℝ) (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (c.detB θ)⁻¹ • compatAdj c.a c.b (ω₁ θ) (ω₂ θ) *ᵥ c.compatRhs θ (c.solX θ q)

theorem joints_iff (θ : ℝ × ℝ) (q X : Fin 4 → ℂ) :
    (c.fOf X 1 + c.gOf X 0 = q 0 ∧ c.fOf X 3 + ω₁ θ * c.gOf X 1 = q 1 ∧
        c.fOf X 0 + (ω₂ θ)⁻¹ * c.gOf X 2 = q 2 ∧
        c.fOf X 2 + ω₁ θ * (ω₂ θ)⁻¹ * c.gOf X 3 = q 3) ↔
      c.statics θ *ᵥ X = rhsVec θ q := by
  have h2 := ω₂_ne_zero θ
  rw [funext_iff, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_one]
  simp only [fOf, gOf, statics, staticsMat, rhsVec, φ₁, φ₂, mulVec, dotProduct,
    Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Fin.isValue, cons_val_one, cons_val_zero, mul_neg, mul_one, neg_add_rev, cons_val,
    neg_mul, of_apply, cons_val', cons_val_fin_one, one_mul, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    Fin.reduceSucc]
  constructor
  · rintro ⟨e0, e1, e2, e3⟩
    refine ⟨by linear_combination e0, by linear_combination e1, ?_, ?_⟩
    · field_simp at e2; linear_combination e2
    · field_simp at e3; linear_combination e3
  · rintro ⟨e0, e1, e2, e3⟩
    refine ⟨by linear_combination e0, by linear_combination e1, ?_, ?_⟩
    · field_simp; linear_combination e2
    · field_simp; linear_combination e3

theorem compats_iff (θ : ℝ × ℝ) (X w : Fin 4 → ℂ) :
    (c.Compatible (c.fOf X) ![w 2, w 0, w 3, w 1] ∧
        c.Compatible (c.gOf X) ![w 0, (ω₁ θ)⁻¹ * w 1, ω₂ θ * w 2, (ω₁ θ)⁻¹ * ω₂ θ * w 3]) ↔
      c.compat θ *ᵥ w = c.compatRhs θ X := by
  have h1 := ω₁_ne_zero θ
  rw [fOf, gOf, compatible_iff, compatible_iff, funext_iff, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one]
  simp only [compat, compatMat, compatRhs, φ₁, φ₂, mulVec, dotProduct, Fin.sum_univ_four]
  simp only [Fin.isValue, cons_val_one, cons_val_zero, neg_add_rev, cons_val,
    neg_mul, of_apply, cons_val', cons_val_fin_one, one_mul, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,
    Fin.reduceSucc]
  constructor
  · rintro ⟨⟨e0, e1⟩, e2, e3⟩
    refine ⟨by linear_combination e0, by linear_combination e1, ?_, ?_⟩
    · field_simp at e2; linear_combination e2
    · field_simp at e3; linear_combination e3
  · rintro ⟨e0, e1, e2, e3⟩
    refine ⟨⟨by linear_combination e0, by linear_combination e1⟩, ?_, ?_⟩
    · field_simp; linear_combination e2
    · field_simp; linear_combination e3

theorem isBloch_iff (θ : ℝ × ℝ) (q f g w : Fin 4 → ℂ) :
    c.IsBloch θ q f g w ↔ ∃ X, f = c.fOf X ∧ g = c.gOf X ∧
      c.statics θ *ᵥ X = rhsVec θ q ∧ c.compat θ *ᵥ w = c.compatRhs θ X := by
  constructor
  · intro h
    refine ⟨![sCoord f, c.uCoord f, sCoord g, c.uCoord g], ?_, ?_, ?_, ?_⟩
    · simpa [fOf] using (c.beamEqC_iff f).1 h.eq_h
    · simpa [gOf] using (c.beamEqC_iff g).1 h.eq_v
    · have hf : f = c.fOf ![sCoord f, c.uCoord f, sCoord g, c.uCoord g] := by
        simpa [fOf] using (c.beamEqC_iff f).1 h.eq_h
      have hg : g = c.gOf ![sCoord f, c.uCoord f, sCoord g, c.uCoord g] := by
        simpa [gOf] using (c.beamEqC_iff g).1 h.eq_v
      rw [← joints_iff, ← hf, ← hg]
      exact ⟨h.joint₀, h.joint₁, h.joint₂, h.joint₃⟩
    · have hf : f = c.fOf ![sCoord f, c.uCoord f, sCoord g, c.uCoord g] := by
        simpa [fOf] using (c.beamEqC_iff f).1 h.eq_h
      have hg : g = c.gOf ![sCoord f, c.uCoord f, sCoord g, c.uCoord g] := by
        simpa [gOf] using (c.beamEqC_iff g).1 h.eq_v
      rw [← compats_iff, ← hf, ← hg]
      exact ⟨h.compat_h, h.compat_v⟩
  · rintro ⟨X, rfl, rfl, hs, hk⟩
    obtain ⟨j0, j1, j2, j3⟩ := (c.joints_iff θ q X).2 hs
    obtain ⟨k0, k1⟩ := (c.compats_iff θ X w).2 hk
    refine ⟨?_, ?_, j0, j1, j2, j3, k0, k1⟩
    · exact c.beamEqC_comb _ _
    · exact c.beamEqC_comb _ _

theorem detB_ne_zero {θ : ℝ × ℝ} (hD : blochDet (ω₁ θ) (ω₂ θ) ≠ 0) : c.detB θ ≠ 0 := by
  have ha : (c.a : ℂ) ≠ 0 := by exact_mod_cast c.a_pos.ne'
  have hab : (c.a + c.b : ℂ) ≠ 0 := by
    have := c.a_pos; have := c.b_nonneg
    exact_mod_cast (show (c.a + c.b : ℝ) ≠ 0 by positivity)
  simp only [detB]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hab) hD

/-- The explicit amplitudes solve the cell problem. -/
theorem isBloch_sol {θ : ℝ × ℝ} (hD : blochDet (ω₁ θ) (ω₂ θ) ≠ 0) (q : Fin 4 → ℂ) :
    c.IsBloch θ q (c.fOf (c.solX θ q)) (c.gOf (c.solX θ q)) (c.solW θ q) :=
  (c.isBloch_iff θ q _ _ _).2 ⟨c.solX θ q, rfl, rfl,
    mulVec_smul_adj_mulVec (c.detB_ne_zero hD) (staticsMat_mul _ _ _ _) _,
    mulVec_smul_adj_mulVec (c.detB_ne_zero hD) (compatMat_mul _ _ _ _) _⟩

/-- Any solution of the cell problem is the explicit one. -/
theorem eq_sol {θ : ℝ × ℝ} (hD : blochDet (ω₁ θ) (ω₂ θ) ≠ 0) {q f g w : Fin 4 → ℂ}
    (h : c.IsBloch θ q f g w) :
    f = c.fOf (c.solX θ q) ∧ g = c.gOf (c.solX θ q) ∧ w = c.solW θ q := by
  obtain ⟨X, rfl, rfl, hs, hk⟩ := (c.isBloch_iff θ q f g w).1 h
  have hX : X = c.solX θ q :=
    eq_smul_adj_mulVec (c.detB_ne_zero hD) (staticsAdj_mul _ _ _ _) hs
  subst hX
  exact ⟨rfl, rfl, eq_smul_adj_mulVec (c.detB_ne_zero hD) (compatAdj_mul _ _ _ _) hk⟩

/-- **Existence and uniqueness of the Bloch solution** of the infinite frame, for
`ω₁ + ω₁⁻¹ + ω₂ + ω₂⁻¹ ≠ 4`. -/
theorem existsUnique_bloch {θ : ℝ × ℝ} (hD : blochDet (ω₁ θ) (ω₂ θ) ≠ 0) (q : Fin 4 → ℂ) :
    ∃! p : (Fin 4 → ℂ) × (Fin 4 → ℂ) × (Fin 4 → ℂ),
      c.IsFrameSolution (bloch θ q) (bloch θ p.1) (bloch θ p.2.1) (bloch θ p.2.2) := by
  refine ⟨(c.fOf (c.solX θ q), c.gOf (c.solX θ q), c.solW θ q),
    (c.isFrameSolution_bloch_iff θ _ _ _ _).2 (c.isBloch_sol hD q), ?_⟩
  rintro ⟨f, g, w⟩ h
  obtain ⟨rfl, rfl, rfl⟩ := c.eq_sol hD ((c.isFrameSolution_bloch_iff θ _ _ _ _).1 h)
  rfl

/-! ### Long-wave limit -/

/-- The Bloch angles `θᵢ = k · tᵢ` of the wave vector `k`, `t₁ = (a + b, -a)`, `t₂ = (a, a + b)`. -/
def θOf (k : ℝ × ℝ) : ℝ × ℝ := (k.1 * (c.a + c.b) - k.2 * c.a, k.1 * c.a + k.2 * (c.a + c.b))

/-- `|k|²`. -/
def nk (k : ℝ × ℝ) : ℝ := k.1 ^ 2 + k.2 ^ 2

theorem θOf_sq (k : ℝ × ℝ) : (c.θOf k).1 ^ 2 + (c.θOf k).2 ^ 2 = c.area * nk k := by
  simp only [θOf, area, nk]; ring

theorem nk_pos {k : ℝ × ℝ} (hk : k ≠ 0) : 0 < nk k := by
  rcases k with ⟨k₁, k₂⟩
  have : k₁ ≠ 0 ∨ k₂ ≠ 0 := by
    by_contra h; push Not at h; exact hk (by rw [h.1, h.2]; rfl)
  rcases this with h | h <;> simp only [nk] <;> positivity

theorem continuous_θOf : Continuous c.θOf := by unfold θOf; fun_prop

theorem continuous_nk : Continuous nk := by unfold nk; fun_prop

theorem continuous_phase (n : ℤ × ℤ) : Continuous fun k => phase (c.θOf k) n := by
  unfold phase θOf; fun_prop

theorem phase_θOf_zero (n : ℤ × ℤ) : phase (c.θOf 0) n = 1 := by simp [phase, θOf]

/-- `ω + ω⁻¹ = 2 cos θ`: the Bloch determinant is `ω₁ ω₂ (2 cos θ₁ + 2 cos θ₂ - 4)`. -/
theorem blochDet_eq (θ : ℝ × ℝ) :
    blochDet (ω₁ θ) (ω₂ θ) = ω₁ θ * ω₂ θ * ((2 * Real.cos θ.1 + 2 * Real.cos θ.2 - 4 : ℝ) : ℂ) := by
  have e1 : ω₁ θ = Complex.exp (θ.1 * Complex.I) := by simp [ω₁, phase]
  have e2 : ω₂ θ = Complex.exp (θ.2 * Complex.I) := by simp [ω₂, phase]
  have c1 : Complex.cos (θ.1 : ℂ) = (ω₁ θ + (ω₁ θ)⁻¹) / 2 := by
    rw [Complex.cos, e1, ← Complex.exp_neg, neg_mul]
  have c2 : Complex.cos (θ.2 : ℂ) = (ω₂ θ + (ω₂ θ)⁻¹) / 2 := by
    rw [Complex.cos, e2, ← Complex.exp_neg, neg_mul]
  have h1 := ω₁_ne_zero θ; have h2 := ω₂_ne_zero θ
  push_cast
  rw [c1, c2, blochDet]
  field_simp
  ring

/-- **Discrete Laplacian**: `(2 cos θ₁ + 2 cos θ₂ - 4) / |k|² → -A` as `k → 0`. -/
theorem tendsto_cos_div :
    Tendsto (fun k => (2 * Real.cos (c.θOf k).1 + 2 * Real.cos (c.θOf k).2 - 4) / nk k)
      (𝓝[≠] 0) (𝓝 (-c.area)) := by
  have h0 : c.θOf 0 = (0, 0) := by simp [θOf]
  have hθ1 : Tendsto (fun k => (c.θOf k).1) (𝓝 0) (𝓝 0) := by
    have := (continuous_fst.comp c.continuous_θOf).tendsto (0 : ℝ × ℝ)
    simp only [Function.comp_def, h0] at this
    exact this
  have hθ2 : Tendsto (fun k => (c.θOf k).2) (𝓝 0) (𝓝 0) := by
    have := (continuous_snd.comp c.continuous_θOf).tendsto (0 : ℝ × ℝ)
    simp only [Function.comp_def, h0] at this
    exact this
  have hI : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hs1 := (hθ1.eventually hI).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))
  have hs2 := (hθ2.eventually hI).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))
  have hnk : Tendsto (fun k => c.area ^ 2 * nk k) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_nk.tendsto (0 : ℝ × ℝ)).const_mul (c.area ^ 2)).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))
    simpa [nk] using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hnk
  filter_upwards [self_mem_nhdsWithin, hs1, hs2] with k hk h1 h2
  have hn := nk_pos hk
  have b1 := Real.cos_bound (abs_le.2 h1)
  have b2 := Real.cos_bound (abs_le.2 h2)
  have hsq := c.θOf_sq k
  set x := (c.θOf k).1
  set y := (c.θOf k).2
  have key : (2 * Real.cos x + 2 * Real.cos y - 4) / nk k - -c.area =
      (2 * (Real.cos x - (1 - x ^ 2 / 2)) + 2 * (Real.cos y - (1 - y ^ 2 / 2))) / nk k := by
    field_simp
    linear_combination -hsq
  rw [key, Real.norm_eq_abs, abs_div, abs_of_pos hn, div_le_iff₀ hn]
  have ax : |x| ^ 4 = x ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
  have ay : |y| ^ 4 = y ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
  rw [ax] at b1; rw [ay] at b2
  calc |2 * (Real.cos x - (1 - x ^ 2 / 2)) + 2 * (Real.cos y - (1 - y ^ 2 / 2))|
      ≤ |2 * (Real.cos x - (1 - x ^ 2 / 2))| + |2 * (Real.cos y - (1 - y ^ 2 / 2))| :=
        abs_add_le _ _
    _ ≤ 2 * (x ^ 4 * (5 / 96)) + 2 * (y ^ 4 * (5 / 96)) := by
        rw [abs_mul, abs_mul, abs_two]; gcongr
    _ ≤ (x ^ 2 + y ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
    _ = c.area ^ 2 * nk k * nk k := by rw [hsq]; ring

theorem continuous_ω₁ : Continuous fun k => ω₁ (c.θOf k) := c.continuous_phase _
theorem continuous_ω₂ : Continuous fun k => ω₂ (c.θOf k) := c.continuous_phase _

/-- `det / |k|² → 4a(a + b)A`. -/
theorem tendsto_detB_div :
    Tendsto (fun k => c.detB (c.θOf k) / (nk k : ℂ)) (𝓝[≠] 0)
      (𝓝 (4 * c.a * (c.a + c.b) * c.area)) := by
  have hω : Tendsto (fun k => ω₁ (c.θOf k) * ω₂ (c.θOf k)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous fun k => ω₁ (c.θOf k) * ω₂ (c.θOf k) :=
      c.continuous_ω₁.mul c.continuous_ω₂
    have := (hc.tendsto (0 : ℝ × ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))
    rwa [show ω₁ (c.θOf 0) * ω₂ (c.θOf 0) = 1 by simp [ω₁, ω₂, phase_θOf_zero]] at this
  have hc := (Complex.continuous_ofReal.tendsto _).comp c.tendsto_cos_div
  have := (hω.mul hc).const_mul (-4 * c.a * (c.a + c.b) : ℂ)
  refine (this.congr fun k => ?_).trans ?_
  · simp only [Function.comp_apply, detB, blochDet_eq, Complex.ofReal_div]
    ring
  · push_cast; ring_nf; exact le_rfl

theorem eventually_blochDet_ne_zero :
    ∀ᶠ k in 𝓝[≠] (0 : ℝ × ℝ), blochDet (ω₁ (c.θOf k)) (ω₂ (c.θOf k)) ≠ 0 := by
  have hA : (4 * c.a * (c.a + c.b) * c.area : ℂ) ≠ 0 := by
    have := c.a_pos; have := c.b_nonneg; have := c.area_pos
    exact_mod_cast (show (4 * c.a * (c.a + c.b) * c.area : ℝ) ≠ 0 by positivity)
  filter_upwards [c.tendsto_detB_div.eventually_ne hA] with k hk hD
  apply hk
  simp [detB, hD]

/-- Abscissae of the joints `0, 1, 2, 3` of cell `0` on the beam `h(0)`. -/
def jointX : Fin 4 → ℝ := ![c.a, 2 * c.a + c.b, 0, c.a + c.b]

/-- Load amplitudes of the pressure `p₀ e^{i k·x}` lumped at the joints (`A / 4` each). -/
def load (p₀ : ℂ) (k : ℝ × ℝ) : Fin 4 → ℂ :=
  fun j => p₀ * c.area / 4 * Complex.exp ((k.1 * c.jointX j : ℝ) * Complex.I)

/-- The plate deflection `p₀ d e^{i k·x} / |k|⁴` (solution of `D Δ²w = p₀ e^{i k·x}`) at joint `j`
of cell `n`, `x = n₁ t₁ + n₂ t₂ + (x_j, 0)`. -/
def plateDefl (p₀ : ℂ) (k : ℝ × ℝ) (n : ℤ × ℤ) (j : Fin 4) : ℂ :=
  p₀ * c.compliance / (nk k : ℂ) ^ 2 *
    (phase (c.θOf k) n * Complex.exp ((k.1 * c.jointX j : ℝ) * Complex.I))

/-- The limit `-p₀ A / (a (a + b))` of `|k|² s`. -/
def sLim (p₀ : ℂ) : ℂ := -(p₀ * c.area) / (c.a * (c.a + c.b))

theorem continuous_load (p₀ : ℂ) (j : Fin 4) : Continuous fun k => c.load p₀ k j := by
  unfold load; fun_prop

theorem load_zero (p₀ : ℂ) (j : Fin 4) : c.load p₀ 0 j = p₀ * c.area / 4 := by simp [load]

theorem continuous_staticsAdj :
    Continuous fun k => staticsAdj c.a c.b (ω₁ (c.θOf k)) (ω₂ (c.θOf k)) := by
  have h1 := c.continuous_ω₁; have h2 := c.continuous_ω₂
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [staticsAdj, neg_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, cons_val, cons_val_zero, cons_val_one, of_apply,
    cons_val', cons_val_fin_one] <;> fun_prop

theorem continuous_rhsVec (p₀ : ℂ) : Continuous fun k => rhsVec (c.θOf k) (c.load p₀ k) := by
  have h2 := c.continuous_ω₂
  have hl := c.continuous_load p₀
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [rhsVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cons_val, cons_val_zero, cons_val_one] <;> fun_prop

theorem continuous_compatG : Continuous fun p : ℂ × ℂ × (Fin 4 → ℂ) =>
    compatAdj c.a c.b p.1 p.2.1 *ᵥ
      ![c.flexS * p.2.2 0, c.flexU * p.2.2 1, p.1 * (c.flexS * p.2.2 2),
        p.1 * (c.flexU * p.2.2 3)] := by
  refine Continuous.matrix_mulVec ?_ ?_
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [compatAdj, neg_mul, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Fin.isValue, cons_val, cons_val_zero, cons_val_one,
      of_apply, cons_val', cons_val_fin_one] <;> fun_prop
  · refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cons_val,
        cons_val_zero, cons_val_one] <;> fun_prop

theorem area_cast : ((c.a : ℂ) + c.b) ^ 2 + (c.a : ℂ) ^ 2 = c.area := by simp [area]

theorem area_ne_zero' : (4 * c.a * (c.a + c.b) * c.area : ℂ) ≠ 0 := by
  have := c.a_pos; have := c.b_nonneg; have := c.area_pos
  exact_mod_cast (show (4 * c.a * (c.a + c.b) * c.area : ℝ) ≠ 0 by positivity)

theorem tendsto_inv_detB_div :
    Tendsto (fun k => (c.detB (c.θOf k) / (nk k : ℂ))⁻¹) (𝓝[≠] 0)
      (𝓝 (4 * c.a * (c.a + c.b) * c.area : ℂ)⁻¹) :=
  c.tendsto_detB_div.inv₀ c.area_ne_zero'

theorem eventually_nk_ne_zero : ∀ᶠ k in 𝓝[≠] (0 : ℝ × ℝ), (nk k : ℂ) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact_mod_cast (nk_pos hk).ne'

/-- **Long-wave limit of the member forces**: `|k|² (s_h, u_h, s_v, u_v) → (s, 0, s, 0)`,
`s = -p₀ A / (a (a + b))`. -/
theorem tendsto_solX (p₀ : ℂ) :
    Tendsto (fun k => (nk k : ℂ) • c.solX (c.θOf k) (c.load p₀ k)) (𝓝[≠] 0)
      (𝓝 ![c.sLim p₀, 0, c.sLim p₀, 0]) := by
  have hV := ((c.continuous_staticsAdj.matrix_mulVec (c.continuous_rhsVec p₀)).tendsto
    (0 : ℝ × ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))
  have := c.tendsto_inv_detB_div.smul hV
  refine (this.congr' ?_).trans (le_of_eq ?_)
  · filter_upwards [eventually_nk_ne_zero] with k hk
    simp only [solX, smul_smul]
    congr 1
    field_simp
  · have hr : rhsVec (c.θOf 0) (c.load p₀ 0) =
        ![p₀ * c.area / 4, p₀ * c.area / 4, p₀ * c.area / 4, p₀ * c.area / 4] := by
      funext i; fin_cases i <;> simp [rhsVec, ω₂, phase_θOf_zero, load_zero]
    rw [show ω₁ (c.θOf 0) = 1 from c.phase_θOf_zero _, show ω₂ (c.θOf 0) = 1 from
      c.phase_θOf_zero _, hr, staticsAdj_one_mulVec, c.area_cast]
    have h := c.area_ne_zero'
    have ha : (c.a : ℂ) ≠ 0 := by exact_mod_cast c.a_pos.ne'
    have hab : (c.a + c.b : ℂ) ≠ 0 := by
      have := c.a_pos; have := c.b_nonneg
      exact_mod_cast (show (c.a + c.b : ℝ) ≠ 0 by positivity)
    have hA : (c.area : ℂ) ≠ 0 := by exact_mod_cast c.area_pos.ne'
    congr 1
    funext i
    fin_cases i <;> simp [sLim] <;> field_simp <;> ring

/-- **Long-wave limit of the joint deflections**: `|k|⁴ wⱼ → p₀ d`. -/
theorem tendsto_solW (p₀ : ℂ) (j : Fin 4) :
    Tendsto (fun k => (nk k : ℂ) ^ 2 * c.solW (c.θOf k) (c.load p₀ k) j) (𝓝[≠] 0)
      (𝓝 (p₀ * c.compliance)) := by
  have hω₁ := ((c.continuous_ω₁.tendsto (0 : ℝ × ℝ)).mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ)))
  have hω₂ := ((c.continuous_ω₂.tendsto (0 : ℝ × ℝ)).mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ)))
  have hG := (c.continuous_compatG.tendsto _).comp
    (hω₁.prodMk_nhds (hω₂.prodMk_nhds (c.tendsto_solX p₀)))
  have := c.tendsto_inv_detB_div.smul hG
  have hj := (continuous_apply j).tendsto _ |>.comp this
  refine (hj.congr' ?_).trans (le_of_eq ?_)
  · filter_upwards [eventually_nk_ne_zero] with k hk
    simp only [Function.comp_apply, solW, compatRhs, Pi.smul_apply, smul_eq_mul, mulVec,
      dotProduct, Fin.sum_univ_four]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
  · rw [show ω₁ (c.θOf 0) = 1 from c.phase_θOf_zero _, show ω₂ (c.θOf 0) = 1 from
      c.phase_θOf_zero _]
    have hv : (![c.flexS * (![c.sLim p₀, 0, c.sLim p₀, 0] : Fin 4 → ℂ) 0,
        c.flexU * (![c.sLim p₀, 0, c.sLim p₀, 0] : Fin 4 → ℂ) 1,
        1 * (c.flexS * (![c.sLim p₀, 0, c.sLim p₀, 0] : Fin 4 → ℂ) 2),
        1 * (c.flexU * (![c.sLim p₀, 0, c.sLim p₀, 0] : Fin 4 → ℂ) 3)] : Fin 4 → ℂ) =
        ![c.flexS * c.sLim p₀, 0, c.flexS * c.sLim p₀, 0] := by
      funext i; fin_cases i <;> simp
    dsimp only
    congr 1
    rw [hv, Pi.smul_apply, smul_eq_mul, compatAdj_one_mulVec, c.area_cast]
    have ha : (c.a : ℂ) ≠ 0 := by exact_mod_cast c.a_pos.ne'
    have hab : (c.a + c.b : ℂ) ≠ 0 := by
      have := c.a_pos; have := c.b_nonneg
      exact_mod_cast (show (c.a + c.b : ℝ) ≠ 0 by positivity)
    have hA : (c.area : ℂ) ≠ 0 := by exact_mod_cast c.area_pos.ne'
    have hE : (c.EI : ℂ) ≠ 0 := by exact_mod_cast c.EI_pos.ne'
    have hG : (c.GS : ℂ) ≠ 0 := by exact_mod_cast c.GS_pos.ne'
    simp only [sLim, flexS, compliance]
    push_cast
    field_simp
    ring

theorem tendsto_exp_jointX (j : Fin 4) :
    Tendsto (fun k : ℝ × ℝ => Complex.exp ((k.1 * c.jointX j : ℝ) * Complex.I)) (𝓝[≠] 0)
      (𝓝 1) := by
  have h : Continuous fun k : ℝ × ℝ => Complex.exp ((k.1 * c.jointX j : ℝ) * Complex.I) := by
    fun_prop
  simpa using (h.tendsto (0 : ℝ × ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ × ℝ)}ᶜ))

/-- **Convergence of the nexorade frame to the homogenized plate.** Let, for every wave vector
`k ≠ 0` near `0`, `(f k, g k, w k)` be Bloch amplitudes of a solution of the infinite frame under
the joint loads of the pressure `p₀ e^{i k·x}` (by `existsUnique_bloch` there is exactly one).
Then, as `k → 0`,

* the deflection of every joint, divided by the deflection `p₀ d e^{i k·x} / |k|⁴` of the
  homogenized plate `D Δ²w = p`, tends to `1`;
* `|k|²` times the contact forces of the beams `h` and `v` tends to the four-point-bending field
  `s (1, -1, -1, 1)`, `s = -p₀ A / (a (a + b))` (localization of the plate moment, (22)–(23)). -/
theorem tendsto_frame {p₀ : ℂ} (hp : p₀ ≠ 0)
    (F : ℝ × ℝ → (Fin 4 → ℂ) × (Fin 4 → ℂ) × (Fin 4 → ℂ))
    (hF : ∀ᶠ k in 𝓝[≠] (0 : ℝ × ℝ), c.IsFrameSolution (bloch (c.θOf k) (c.load p₀ k))
      (bloch (c.θOf k) (F k).1) (bloch (c.θOf k) (F k).2.1) (bloch (c.θOf k) (F k).2.2)) :
    (∀ n j, Tendsto (fun k => bloch (c.θOf k) (F k).2.2 n j / c.plateDefl p₀ k n j)
      (𝓝[≠] 0) (𝓝 1)) ∧
    Tendsto (fun k => (nk k : ℂ) • (F k).1) (𝓝[≠] 0) (𝓝 (c.sLim p₀ • φ₁)) ∧
    Tendsto (fun k => (nk k : ℂ) • (F k).2.1) (𝓝[≠] 0) (𝓝 (c.sLim p₀ • φ₁)) := by
  have hsol : ∀ᶠ k in 𝓝[≠] (0 : ℝ × ℝ),
      F k = (c.fOf (c.solX (c.θOf k) (c.load p₀ k)), c.gOf (c.solX (c.θOf k) (c.load p₀ k)),
        c.solW (c.θOf k) (c.load p₀ k)) := by
    filter_upwards [hF, c.eventually_blochDet_ne_zero] with k hk hD
    obtain ⟨h1, h2, h3⟩ := c.eq_sol hD ((c.isFrameSolution_bloch_iff _ _ _ _ _).1 hk)
    ext1 <;> [exact h1; exact Prod.ext h2 h3]
  have hd : (c.compliance : ℂ) ≠ 0 := by exact_mod_cast c.compliance_pos.ne'
  have hfOf : Continuous c.fOf := by unfold fOf; fun_prop
  have hgOf : Continuous c.gOf := by unfold gOf; fun_prop
  refine ⟨fun n j => ?_, ?_, ?_⟩
  · have := (c.tendsto_solW p₀ j).div ((c.tendsto_exp_jointX j).const_mul (p₀ * c.compliance))
      (by simpa using mul_ne_zero hp hd)
    rw [mul_one, div_self (mul_ne_zero hp hd)] at this
    refine this.congr' ?_
    filter_upwards [hsol, eventually_nk_ne_zero] with k hk hn
    rw [hk]
    simp only [bloch, plateDefl, Pi.smul_apply, smul_eq_mul, Pi.div_apply]
    have := phase_ne_zero (c.θOf k) n
    have he := Complex.exp_ne_zero ((k.1 * c.jointX j : ℝ) * Complex.I)
    generalize Complex.exp ((k.1 * c.jointX j : ℝ) * Complex.I) = e at he ⊢
    field_simp
  · have := (hfOf.tendsto _).comp (c.tendsto_solX p₀)
    refine (this.congr' ?_).trans (le_of_eq ?_)
    · filter_upwards [hsol] with k hk
      rw [hk]
      simp only [Function.comp_apply, fOf, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]
    · simp [fOf]
  · have := (hgOf.tendsto _).comp (c.tendsto_solX p₀)
    refine (this.congr' ?_).trans (le_of_eq ?_)
    · filter_upwards [hsol] with k hk
      rw [hk]
      simp only [Function.comp_apply, gOf, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]
    · simp [gOf]

end Cell

end ContinuumMechanics.Nexorade
