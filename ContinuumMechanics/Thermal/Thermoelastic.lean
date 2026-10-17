import ContinuumMechanics.Constitutive.LinearIsotropic
import ContinuumMechanics.Elastostatics.LameCylinder
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Linear thermoelasticity

A temperature change `ΔT` from a stress-free reference state produces in an isotropic body the
free thermal strain `α ΔT I` ([Boley1960], §1.12; [TimoshenkoGoodier1970], §150). The stress is
given by the elastic response to the excess strain `ε - α ΔT I`, which in dimension `d` is the
**Duhamel–Neumann law**

`σ = λ (tr ε) I + 2μ ε - (dλ + 2μ) α ΔT I`

(`d = 3`: `σ = λ (tr ε) I + 2μ ε - (3λ + 2μ) α ΔT I`). We treat the tensorial law on `Lin E` and
several classical one-dimensional thermal-stress problems.

## Main definitions

* `Thermoelastic.stress lam mu α θ ε`: the Duhamel–Neumann stress (with `θ = ΔT`).
* `Thermoelastic.strain lam mu α θ σ`: the inverse law
  `ε = (1/2μ)(σ - λ/(dλ + 2μ) (tr σ) I) + α ΔT I`.
* `Thermoelastic.Bar.springStress`: stress of a bar restrained by an end spring.
* `Thermoelastic.Bimetal.Equations`, `Thermoelastic.Bimetal.curvature`: Timoshenko's
  bimetallic strip.
* `Thermoelastic.Gradient.temp`, `Thermoelastic.Gradient.curvature`: a beam with a linear
  through-thickness temperature gradient.
* `Thermoelastic.Cylinder.sigR`, `Thermoelastic.Cylinder.sigT`: thermal stresses in a thick
  plane-strain cylinder.

## Main results

* `stress_free_expansion`: the free thermal strain `α ΔT I` is stress-free.
* `strain_stress`, `stress_strain`: for `μ ≠ 0`, `dλ + 2μ ≠ 0` the two laws are mutually
  inverse on symmetric tensors; `stress_of_finrank_three` is the 3D form `(3λ + 2μ)`.
* `Bar.restrained_iff`: a fully restrained heated bar has `σ = -E α ΔT`;
  `Bar.spring_iff`: with an end spring of stiffness `k`, compatibility gives
  `σ = -E α ΔT / (1 + E A/(k L))`; `Bar.tendsto_springStress`: as `k → ∞` this tends to
  `-E α ΔT`.
* `Bimetal.equations_iff`: equilibrium (zero net force and moment) and interface strain
  compatibility of two Euler–Bernoulli layers have the unique solution with Timoshenko's
  curvature `κ = 6(α₂ - α₁)ΔT(1 + m)² / (h(3(1 + m)² + (1 + mn)(m² + 1/(mn))))`;
  `Bimetal.curvature_equal`: equal layers give `κ = 3(α₂ - α₁)ΔT/(2h)`.
* `Gradient.stress_free`, `Gradient.eq_curvature_of_stress_free`: a linear gradient
  produces the stress-free curvature `κ = α(T_top - T_bot)/h`;
  `Gradient.clamped`: a clamped–clamped beam develops the uniform moment
  `M = EI α (T_top - T_bot)/h` and no deflection.
* `Cylinder.equilibrium_eq`, `Cylinder.equilibrium_iff`: the thermoelastic radial equation
  `u'' + u'/r - u/r² = (3λ + 2μ)/(λ + 2μ) α T'`, with `Cylinder.coeff_eq_poisson`:
  `(3λ + 2μ)/(λ + 2μ) = (1 + ν)/(1 - ν)`; `Cylinder.general_solves`: for
  `T = A + B log r` the displacement `c r log r + C₁ r + C₂/r` (`c = K B/2`) solves it.

## References

* [Boley1960] B. A. Boley, J. H. Weiner, *Theory of Thermal Stresses*, §§1.12, 9.10.
* [TimoshenkoGoodier1970] S. P. Timoshenko, J. N. Goodier, *Theory of Elasticity*, 3rd ed.,
  §§150–155.
* [Timoshenko1925] S. Timoshenko, *Analysis of bi-metal thermostats*, J. Opt. Soc. Am. 11
  (1925), 233–255.
-/

open Module Set Filter Topology
open scoped InnerProductSpace ContinuumMechanics

noncomputable section

namespace ContinuumMechanics.Thermoelastic

open Lin Lin4

/-! ### The Duhamel–Neumann law -/

section Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **Duhamel–Neumann law** `σ = λ (tr ε) I + 2μ ε - (dλ + 2μ) α θ I` in dimension
`d = finrank ℝ E`, with temperature change `θ = ΔT` and expansion coefficient `α`. -/
def stress (lam mu α θ : ℝ) (ε : Lin E) : Lin E :=
  isotropic lam mu ε - ((finrank ℝ E * lam + 2 * mu) * α * θ) • (1 : Lin E)

/-- The **inverse Duhamel–Neumann law**
`ε = (1/2μ)(σ - λ/(dλ + 2μ) (tr σ) I) + α θ I`. -/
def strain (lam mu α θ : ℝ) (σ : Lin E) : Lin E :=
  (2 * mu)⁻¹ • (σ - (lam / (finrank ℝ E * lam + 2 * mu) * tr σ) • (1 : Lin E)) +
    (α * θ) • (1 : Lin E)

/-- The Duhamel–Neumann stress is the elastic response to the excess strain `ε - α θ I`. -/
theorem stress_eq_isotropic_sub (lam mu α θ : ℝ) (ε : Lin E) :
    stress lam mu α θ ε = isotropic lam mu (ε - (α * θ) • (1 : Lin E)) := by
  have hs : sym (1 : Lin E) = 1 := sym_eq_self_of_mem (mem_sym_iff.mpr transpose_one)
  rw [stress, map_sub, map_smul, isotropic_apply (A := 1), hs, tr_one]
  match_scalars <;> ring

/-- In dimension 3 the thermal modulus is `3λ + 2μ`:
`σ = λ (tr ε) I + 2μ ε - (3λ + 2μ) α θ I` for symmetric `ε`. -/
theorem stress_of_finrank_three (h3 : finrank ℝ E = 3) (lam mu α θ : ℝ) {ε : Lin E}
    (hε : ε ∈ Sym E) :
    stress lam mu α θ ε =
      (lam * tr ε) • (1 : Lin E) + (2 * mu) • ε - ((3 * lam + 2 * mu) * α * θ) • (1 : Lin E) := by
  rw [stress, isotropic_apply, sym_eq_self_of_mem hε, h3]
  norm_num

/-- **Free thermal expansion is stress-free**: `σ(α θ I) = 0`. -/
theorem stress_free_expansion (lam mu α θ : ℝ) :
    stress lam mu α θ ((α * θ) • (1 : Lin E)) = 0 := by
  rw [stress_eq_isotropic_sub, sub_self, map_zero]

/-- Trace of the Duhamel–Neumann stress: `tr σ = (dλ + 2μ)(tr ε - d α θ)`. -/
theorem tr_stress (lam mu α θ : ℝ) {ε : Lin E} (hε : ε ∈ Sym E) :
    tr (stress lam mu α θ ε) =
      (finrank ℝ E * lam + 2 * mu) * (tr ε - finrank ℝ E * (α * θ)) := by
  rw [stress, isotropic_apply, sym_eq_self_of_mem hε]
  simp only [map_sub, map_add, map_smul, tr_one, smul_eq_mul]
  ring

/-- The inverse law produces symmetric strains from symmetric stresses. -/
theorem strain_mem_sym (lam mu α θ : ℝ) {σ : Lin E} (hσ : σ ∈ Sym E) :
    strain lam mu α θ σ ∈ Sym E := by
  have h1 : (1 : Lin E) ∈ Sym E := mem_sym_iff.mpr transpose_one
  exact (Sym E).add_mem ((Sym E).smul_mem _ ((Sym E).sub_mem hσ ((Sym E).smul_mem _ h1)))
    ((Sym E).smul_mem _ h1)

/-- **Inversion, left inverse**: for `μ ≠ 0`, `dλ + 2μ ≠ 0` and symmetric `ε`,
`ε(σ(ε)) = ε`. -/
theorem strain_stress (lam mu α θ : ℝ) (hmu : mu ≠ 0) (hk : finrank ℝ E * lam + 2 * mu ≠ 0)
    {ε : Lin E} (hε : ε ∈ Sym E) : strain lam mu α θ (stress lam mu α θ ε) = ε := by
  have hk' : lam * (finrank ℝ E : ℝ) + 2 * mu ≠ 0 := by rwa [mul_comm lam]
  rw [strain, tr_stress lam mu α θ hε, stress, isotropic_apply, sym_eq_self_of_mem hε]
  match_scalars
  all_goals field_simp
  ring

/-- **Inversion, right inverse**: for `μ ≠ 0`, `dλ + 2μ ≠ 0` and symmetric `σ`,
`σ(ε(σ)) = σ`. -/
theorem stress_strain (lam mu α θ : ℝ) (hmu : mu ≠ 0) (hk : finrank ℝ E * lam + 2 * mu ≠ 0)
    {σ : Lin E} (hσ : σ ∈ Sym E) : stress lam mu α θ (strain lam mu α θ σ) = σ := by
  have hk' : lam * (finrank ℝ E : ℝ) + 2 * mu ≠ 0 := by rwa [mul_comm lam]
  rw [stress, isotropic_apply, sym_eq_self_of_mem (strain_mem_sym lam mu α θ hσ), strain]
  simp only [map_sub, map_add, map_smul, tr_one, smul_eq_mul]
  match_scalars
  all_goals field_simp
  ring

end Tensor

/-! ### Constrained bars -/

namespace Bar

/-- **Fully restrained bar**: zero total strain `σ/E + α ΔT = 0` forces `σ = -E α ΔT`. -/
theorem restrained_iff {E α θ σ : ℝ} (hE : E ≠ 0) : σ / E + α * θ = 0 ↔ σ = -(E * α * θ) := by
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · rintro rfl
    field_simp
    ring

/-- Stress `σ = -E α ΔT / (1 + E A/(k L))` in a heated bar (length `L`, area `A`) whose
elongation is resisted by an end spring of stiffness `k`. -/
def springStress (E A k L α θ : ℝ) : ℝ := -(E * α * θ) / (1 + E * A / (k * L))

/-- **Bar restrained by a spring**: the bar elongates by `δ = L(σ/E + α ΔT)` and the spring
compressed by `δ` pushes back with the axial force `σ A = -k δ`. This compatibility condition
holds iff `σ = -E α ΔT / (1 + E A/(k L))`. -/
theorem spring_iff {E A k L α θ σ : ℝ} (hE : E ≠ 0) (hk : k ≠ 0) (hL : L ≠ 0)
    (hD : 1 + E * A / (k * L) ≠ 0) :
    σ * A = -(k * (L * (σ / E + α * θ))) ↔ σ = springStress E A k L α θ := by
  rw [springStress, eq_div_iff hD]
  have key : σ * A + k * (L * (σ / E + α * θ)) =
      k * L / E * (σ * (1 + E * A / (k * L)) + E * α * θ) := by
    field_simp
    ring
  have hc : k * L / E ≠ 0 := div_ne_zero (mul_ne_zero hk hL) hE
  constructor
  · intro h
    have h0 : k * L / E * (σ * (1 + E * A / (k * L)) + E * α * θ) = 0 := by
      rw [← key]; linear_combination h
    linear_combination (mul_eq_zero.mp h0).resolve_left hc
  · intro h
    have h0 : σ * A + k * (L * (σ / E + α * θ)) = 0 := by
      rw [key, h]; ring
    linear_combination h0

/-- A rigid spring recovers the fully restrained bar: `springStress → -E α ΔT` as `k → ∞`. -/
theorem tendsto_springStress (E A L α θ : ℝ) :
    Tendsto (fun k => springStress E A k L α θ) atTop (𝓝 (-(E * α * θ))) := by
  have h1 : Tendsto (fun k : ℝ => 1 + E * A / L * k⁻¹) atTop (𝓝 (1 + E * A / L * 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul _)
  rw [mul_zero, add_zero] at h1
  have h2 := (tendsto_const_nhds (x := -(E * α * θ))).div h1 one_ne_zero
  rw [div_one] at h2
  refine h2.congr' (Eventually.of_forall fun k => ?_)
  simp only [Pi.div_apply, springStress]
  congr 2
  ring

end Bar

/-! ### Timoshenko's bimetallic strip -/

namespace Bimetal

variable (h₁ h₂ E₁ E₂ α₁ α₂ θ : ℝ)

/-- Second moment of area `h³/12` of a layer of thickness `h` (unit width). -/
def inertia (h : ℝ) : ℝ := h ^ 3 / 12

/-- **Equations of the bimetallic strip** for the axial forces `P₁`, `P₂` (at the layer
centroids) and the common curvature `κ`: layer 1 (thickness `h₁`, modulus `E₁`, expansion
`α₁`) lies below the interface, layer 2 above, each layer an Euler–Bernoulli beam with bending
moment `Eᵢ Iᵢ κ`.

* zero net force: `P₁ + P₂ = 0`;
* zero net moment about the interface: `-P₁ h₁/2 + P₂ h₂/2 + (E₁ I₁ + E₂ I₂) κ = 0`;
* compatibility (continuity of the axial strain at the interface):
  `α₁ ΔT + P₁/(E₁ h₁) + κ h₁/2 = α₂ ΔT + P₂/(E₂ h₂) - κ h₂/2`. -/
def Equations (P₁ P₂ κ : ℝ) : Prop :=
  P₁ + P₂ = 0 ∧
    -(P₁ * h₁ / 2) + P₂ * h₂ / 2 + (E₁ * inertia h₁ + E₂ * inertia h₂) * κ = 0 ∧
    α₁ * θ + P₁ / (E₁ * h₁) + κ * h₁ / 2 = α₂ * θ + P₂ / (E₂ * h₂) - κ * h₂ / 2

/-- **Timoshenko's curvature** of a bimetallic strip:
`κ = 6(α₂ - α₁)ΔT(1 + m)² / (h(3(1 + m)² + (1 + mn)(m² + 1/(mn))))`,
with `m = h₁/h₂`, `n = E₁/E₂`, `h = h₁ + h₂`. -/
def curvature : ℝ :=
  6 * (α₂ - α₁) * θ * (1 + h₁ / h₂) ^ 2 /
    ((h₁ + h₂) * (3 * (1 + h₁ / h₂) ^ 2 +
      (1 + h₁ / h₂ * (E₁ / E₂)) * ((h₁ / h₂) ^ 2 + 1 / (h₁ / h₂ * (E₁ / E₂)))))

/-- The layer force `P = 2(E₁ I₁ + E₂ I₂) κ / h` balancing the bending moments. -/
def force (κ : ℝ) : ℝ := 2 * (E₁ * inertia h₁ + E₂ * inertia h₂) * κ / (h₁ + h₂)

/-- Polynomial denominator `(E₁h₁³ + E₂h₂³)(E₁h₁ + E₂h₂) + 3h²E₁h₁E₂h₂` of the curvature. -/
def denom : ℝ :=
  (E₁ * h₁ ^ 3 + E₂ * h₂ ^ 3) * (E₁ * h₁ + E₂ * h₂) + 3 * (h₁ + h₂) ^ 2 * (E₁ * h₁ * (E₂ * h₂))

variable {h₁ h₂ E₁ E₂}

/-- The curvature denominator is positive for positive thicknesses and moduli. -/
theorem denom_pos (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂) :
    0 < denom h₁ h₂ E₁ E₂ := by
  unfold denom; positivity

/-- Polynomial form of Timoshenko's curvature:
`κ = 6 h E₁h₁ E₂h₂ (α₂ - α₁)ΔT / ((E₁h₁³ + E₂h₂³)(E₁h₁ + E₂h₂) + 3h²E₁h₁E₂h₂)`. -/
theorem curvature_eq (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂) :
    curvature h₁ h₂ E₁ E₂ α₁ α₂ θ =
      6 * (h₁ + h₂) * (E₁ * h₁ * (E₂ * h₂)) * ((α₂ - α₁) * θ) / denom h₁ h₂ E₁ E₂ := by
  have hd := (denom_pos hh₁ hh₂ hE₁ hE₂).ne'
  have hh : h₁ + h₂ ≠ 0 := by positivity
  unfold curvature
  rw [div_eq_div_iff _ hd]
  · unfold denom
    field_simp
    ring
  · have : 0 < 3 * (1 + h₁ / h₂) ^ 2 +
        (1 + h₁ / h₂ * (E₁ / E₂)) * ((h₁ / h₂) ^ 2 + 1 / (h₁ / h₂ * (E₁ / E₂))) := by
      positivity
    positivity

/-- **Timoshenko's bimetallic strip** (1925): for positive thicknesses and moduli, the
equilibrium and compatibility equations have the unique solution `κ` = Timoshenko's
curvature, `P₁ = 2(E₁I₁ + E₂I₂)κ/h`, `P₂ = -P₁`. -/
theorem equations_iff (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (P₁ P₂ κ : ℝ) :
    Equations h₁ h₂ E₁ E₂ α₁ α₂ θ P₁ P₂ κ ↔
      κ = curvature h₁ h₂ E₁ E₂ α₁ α₂ θ ∧ P₁ = force h₁ h₂ E₁ E₂ κ ∧
        P₂ = -force h₁ h₂ E₁ E₂ κ := by
  have hd := (denom_pos hh₁ hh₂ hE₁ hE₂).ne'
  have hh : h₁ + h₂ ≠ 0 := by positivity
  have h1 := hh₁.ne'
  have h2 := hh₂.ne'
  have e1 := hE₁.ne'
  have e2 := hE₂.ne'
  rw [curvature_eq α₁ α₂ θ hh₁ hh₂ hE₁ hE₂, eq_div_iff hd]
  unfold Equations force
  have key : ∀ κ : ℝ, α₁ * θ + 2 * (E₁ * inertia h₁ + E₂ * inertia h₂) * κ / (h₁ + h₂) /
      (E₁ * h₁) + κ * h₁ / 2 - (α₂ * θ + -(2 * (E₁ * inertia h₁ + E₂ * inertia h₂) * κ /
      (h₁ + h₂)) / (E₂ * h₂) - κ * h₂ / 2) = (κ * denom h₁ h₂ E₁ E₂ -
      6 * (h₁ + h₂) * (E₁ * h₁ * (E₂ * h₂)) * ((α₂ - α₁) * θ)) /
      (6 * (h₁ + h₂) * (E₁ * h₁ * (E₂ * h₂))) := by
    intro κ
    unfold inertia denom
    field_simp
    ring
  have hc0 : 6 * (h₁ + h₂) * (E₁ * h₁ * (E₂ * h₂)) ≠ 0 := by positivity
  constructor
  · rintro ⟨hf, hm, hc⟩
    have hP₂ : P₂ = -P₁ := by linear_combination hf
    subst hP₂
    have hP₁ : P₁ = 2 * (E₁ * inertia h₁ + E₂ * inertia h₂) * κ / (h₁ + h₂) := by
      rw [eq_div_iff hh]
      linear_combination -2 * hm
    subst hP₁
    rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left hc0, sub_eq_zero] at hc
    exact ⟨hc, rfl, rfl⟩
  · rintro ⟨hκ, hP₁, hP₂⟩
    subst hP₁ hP₂
    refine ⟨by ring, by field_simp; ring, ?_⟩
    rw [← sub_eq_zero, key, hκ, sub_self, zero_div]

/-- Existence: Timoshenko's curvature with the forces `±P` solves the strip equations. -/
theorem curvature_solves (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂) :
    Equations h₁ h₂ E₁ E₂ α₁ α₂ θ (force h₁ h₂ E₁ E₂ (curvature h₁ h₂ E₁ E₂ α₁ α₂ θ))
      (-force h₁ h₂ E₁ E₂ (curvature h₁ h₂ E₁ E₂ α₁ α₂ θ)) (curvature h₁ h₂ E₁ E₂ α₁ α₂ θ) :=
  (equations_iff α₁ α₂ θ hh₁ hh₂ hE₁ hE₂ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- **Equal layers** (`h₁ = h₂`, `E₁ = E₂`, so `m = n = 1`): `κ = 3(α₂ - α₁)ΔT/(2h)` with
`h = 2h₁` the total thickness. -/
theorem curvature_equal (hh₁ : 0 < h₁) (hE₁ : 0 < E₁) :
    curvature h₁ h₁ E₁ E₁ α₁ α₂ θ = 3 * (α₂ - α₁) * θ / (2 * (h₁ + h₁)) := by
  rw [curvature_eq α₁ α₂ θ hh₁ hh₁ hE₁ hE₁]
  have := hh₁.ne'
  have := hE₁.ne'
  unfold denom
  field_simp
  ring

end Bimetal

/-! ### Thermal bending of a beam with a linear temperature gradient -/

namespace Gradient

/-- A linear through-thickness temperature `ΔT(z) = T_top (1/2 + z/h) + T_bot (1/2 - z/h)`,
`-h/2 ≤ z ≤ h/2`. -/
def temp (Tt Tb h z : ℝ) : ℝ := Tt * (1 / 2 + z / h) + Tb * (1 / 2 - z / h)

/-- The **free thermal curvature** `κ_T = α (T_top - T_bot)/h`. -/
def curvature (α Tt Tb h : ℝ) : ℝ := α * (Tt - Tb) / h

/-- The temperature takes the face values: `ΔT(h/2) = T_top`, `ΔT(-h/2) = T_bot`. -/
theorem temp_faces (Tt Tb : ℝ) {h : ℝ} (hh : h ≠ 0) :
    temp Tt Tb h (h / 2) = Tt ∧ temp Tt Tb h (-(h / 2)) = Tb := by
  unfold temp
  constructor <;> (field_simp; ring)

/-- The free thermal strain is affine through the thickness:
`α ΔT(z) = α (T_top + T_bot)/2 + κ_T z`. -/
theorem thermal_strain_eq (α Tt Tb h z : ℝ) :
    α * temp Tt Tb h z = α * (Tt + Tb) / 2 + curvature α Tt Tb h * z := by
  unfold temp curvature; ring

/-- **The free beam is stress-free**: the plane-section strain `ε₀ + κ_T z` with
`ε₀ = α (T_top + T_bot)/2` gives `σ = E(ε - α ΔT) = 0` at every fibre. -/
theorem stress_free (E α Tt Tb h z : ℝ) :
    E * (α * (Tt + Tb) / 2 + curvature α Tt Tb h * z - α * temp Tt Tb h z) = 0 := by
  rw [thermal_strain_eq]; ring

/-- Conversely, a plane-section strain `ε₀ + κ z` that is stress-free at every fibre has the
free thermal curvature `κ = α (T_top - T_bot)/h` and mean strain `α (T_top + T_bot)/2`. -/
theorem eq_curvature_of_stress_free {E α Tt Tb h ε₀ κ : ℝ} (hE : E ≠ 0) (hh : h ≠ 0)
    (hσ : ∀ z, E * (ε₀ + κ * z - α * temp Tt Tb h z) = 0) :
    κ = curvature α Tt Tb h ∧ ε₀ = α * (Tt + Tb) / 2 := by
  have h0 := (mul_eq_zero.mp (hσ 0)).resolve_left hE
  have h1 := (mul_eq_zero.mp (hσ h)).resolve_left hE
  rw [thermal_strain_eq] at h0 h1
  refine ⟨?_, by linear_combination h0⟩
  have : (κ - curvature α Tt Tb h) * h = 0 := by linear_combination h1 - h0
  linear_combination (mul_eq_zero.mp this).resolve_right hh

/-- **Clamped–clamped beam with a temperature gradient**: with no transverse load the bending
moment is affine, `M(x) = M₀ + V x`, and the deflection obeys `w'' = κ_T - M/(EI)`. The four
clamped conditions `w = w' = 0` at `x = 0, L` force `V = 0`, the uniform moment
`M₀ = EI κ_T = EI α (T_top - T_bot)/h`, and zero deflection. -/
theorem clamped {w w' : ℝ → ℝ} {κ EI M₀ V L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : ∀ x, HasDerivAt w' (κ - (M₀ + V * x) / EI) x)
    (h0 : w 0 = 0) (h0' : w' 0 = 0) (hL0 : w L = 0) (hL0' : w' L = 0) :
    M₀ = EI * κ ∧ V = 0 ∧ ∀ x, w x = 0 := by
  set a := κ - M₀ / EI
  set b := V / EI
  -- `w' = a x - b x²/2`
  have hg : ∀ x, HasDerivAt (fun x => w' x - (a * x - b * x ^ 2 / 2)) 0 x := by
    intro x
    have := (hw' x).sub (((hasDerivAt_id' x).const_mul a).sub
      ((hasDerivAt_pow 2 x).const_mul b |>.div_const 2))
    refine this.congr_deriv ?_
    simp only [a, b]
    field_simp
    ring
  have hw'x : ∀ x, w' x = a * x - b * x ^ 2 / 2 := by
    intro x
    have := is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
      (fun y => (hg y).deriv) x 0
    simp only [h0'] at this
    linear_combination this
  -- `w = a x²/2 - b x³/6`
  have hf : ∀ x, HasDerivAt (fun x => w x - (a * x ^ 2 / 2 - b * x ^ 3 / 6)) 0 x := by
    intro x
    have := (hw x).sub (((hasDerivAt_pow 2 x).const_mul a |>.div_const 2).sub
      ((hasDerivAt_pow 3 x).const_mul b |>.div_const 6))
    refine this.congr_deriv ?_
    rw [hw'x]
    push_cast
    ring
  have hwx : ∀ x, w x = a * x ^ 2 / 2 - b * x ^ 3 / 6 := by
    intro x
    have := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt)
      (fun y => (hf y).deriv) x 0
    simp only [h0] at this
    linear_combination this
  have e1 : L * (a - b * L / 2) = 0 := by rw [← hL0', hw'x]; ring
  have e2 : L ^ 2 * (a / 2 - b * L / 6) = 0 := by rw [← hL0, hwx]; ring
  have e1' := (mul_eq_zero.mp e1).resolve_left hL
  have e2' := (mul_eq_zero.mp e2).resolve_left (pow_ne_zero 2 hL)
  have hbL : b * L = 0 := by linear_combination 12 * e2' - 6 * e1'
  have hb : b = 0 := (mul_eq_zero.mp hbL).resolve_right hL
  have ha : a = 0 := by rw [hb] at e1'; linear_combination e1'
  refine ⟨?_, ?_, fun x => by rw [hwx, ha, hb]; ring⟩
  · have : κ - M₀ / EI = 0 := ha
    field_simp at this
    linear_combination -this
  · have : V / EI = 0 := hb
    simpa [hEI] using this

/-- The clamped–clamped moment in terms of the temperatures:
`M = EI α (T_top - T_bot)/h`. -/
theorem clamped_moment {w w' : ℝ → ℝ} {α Tt Tb h EI M₀ V L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0)
    (hw : ∀ x, HasDerivAt w (w' x) x)
    (hw' : ∀ x, HasDerivAt w' (curvature α Tt Tb h - (M₀ + V * x) / EI) x)
    (h0 : w 0 = 0) (h0' : w' 0 = 0) (hL0 : w L = 0) (hL0' : w' L = 0) :
    M₀ = EI * α * (Tt - Tb) / h := by
  rw [(clamped hEI hL hw hw' h0 h0' hL0 hL0').1, curvature]
  ring

end Gradient

/-! ### Thick cylinder with a radial temperature field -/

namespace Cylinder

open LameCylinder (odeRes gen genD genDD)

variable (lam μ β : ℝ)

/-- Thermoelastic radial stress (plane strain) `σ_r = (λ + 2μ) u' + λ u/r - β T`, with thermal
modulus `β = (3λ + 2μ) α`. -/
def sigR (du u r T : ℝ) : ℝ := LameCylinder.sigR lam μ du u r - β * T

/-- Thermoelastic hoop stress `σ_θ = λ u' + (λ + 2μ) u/r - β T`. -/
def sigT (du u r T : ℝ) : ℝ := LameCylinder.sigT lam μ du u r - β * T

/-- **Thermoelastic radial equilibrium**:
`σ_r' + (σ_r - σ_θ)/r = (λ + 2μ)(u'' + u'/r - u/r²) - β T'`. -/
theorem equilibrium_eq {u du ddu T dT : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hT : HasDerivAt T (dT r) r) (hr : r ≠ 0) :
    deriv (fun s => sigR lam μ β (du s) (u s) s (T s)) r +
        (sigR lam μ β (du r) (u r) r (T r) - sigT lam μ β (du r) (u r) r (T r)) / r =
      (lam + 2 * μ) * odeRes (ddu r) (du r) (u r) r - β * dT r := by
  have hd : HasDerivAt (fun s => LameCylinder.sigR lam μ (du s) (u s) s - β * T s)
      ((lam + 2 * μ) * ddu r + lam * ((du r * r - u r) / r ^ 2) - β * dT r) r :=
    (LameCylinder.hasDerivAt_sigR lam μ hu hdu hr).sub (hT.const_mul β)
  simp only [sigR, sigT]
  rw [hd.deriv, sub_sub_sub_cancel_right, LameCylinder.sigR_sub_sigT, odeRes]
  field_simp
  ring

/-- For `λ + 2μ ≠ 0`, equilibrium is the inhomogeneous Euler equation
`u'' + u'/r - u/r² = β/(λ + 2μ) T'`. -/
theorem equilibrium_iff {u du ddu T dT : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hT : HasDerivAt T (dT r) r) (hr : r ≠ 0)
    (hlm : lam + 2 * μ ≠ 0) :
    deriv (fun s => sigR lam μ β (du s) (u s) s (T s)) r +
        (sigR lam μ β (du r) (u r) r (T r) - sigT lam μ β (du r) (u r) r (T r)) / r = 0 ↔
      odeRes (ddu r) (du r) (u r) r = β / (lam + 2 * μ) * dT r := by
  rw [equilibrium_eq lam μ β hu hdu hT hr]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- The coefficient of the thermal forcing: `(3λ + 2μ) α/(λ + 2μ) = (1 + ν)/(1 - ν) α` with
Poisson's ratio `ν = λ/(2(λ + μ))`. -/
theorem coeff_eq_poisson (α : ℝ) (h1 : lam + μ ≠ 0) (h2 : lam + 2 * μ ≠ 0) :
    (3 * lam + 2 * μ) * α / (lam + 2 * μ) =
      (1 + (Lame.mk lam μ).poisson) / (1 - (Lame.mk lam μ).poisson) * α := by
  simp only [Lame.poisson]
  have h4 : lam + 2 * μ = 2 * (lam + μ) - lam := by ring
  have h5 : 1 - lam / (2 * (lam + μ)) = (lam + 2 * μ) / (2 * (lam + μ)) := by
    field_simp; ring
  rw [h5]
  field_simp
  ring

/-- The logarithmic steady temperature `T = A + B log r` of a tube. -/
def logTemp (A B r : ℝ) : ℝ := A + B * Real.log r

/-- Its gradient `T' = B/r`. -/
theorem hasDerivAt_logTemp (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (logTemp A B) (B / r) r := by
  have := (hasDerivAt_const r A).add ((Real.hasDerivAt_log hr).const_mul B)
  convert this using 1
  · funext s; simp [logTemp]
  · simp [div_eq_mul_inv]

/-- A particular displacement `u_p = c r log r`. -/
def part (c r : ℝ) : ℝ := c * r * Real.log r

/-- Its derivative `u_p' = c(log r + 1)`. -/
def partD (c r : ℝ) : ℝ := c * (Real.log r + 1)

/-- Its second derivative `u_p'' = c/r`. -/
def partDD (c r : ℝ) : ℝ := c / r

/-- `(c r log r)' = c(log r + 1)` for `r ≠ 0`. -/
theorem hasDerivAt_part (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (part c) (partD c r) r := by
  have := ((hasDerivAt_id r).const_mul c).mul (Real.hasDerivAt_log hr)
  convert this using 1
  · funext s; simp [part]
  · simp only [partD, id]
    field_simp

/-- `(c(log r + 1))' = c/r` for `r ≠ 0`. -/
theorem hasDerivAt_partD (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (partD c) (partDD c r) r := by
  have := ((Real.hasDerivAt_log hr).add_const 1).const_mul c
  convert this using 1
  · funext s; simp [partD]
  · simp [partDD, div_eq_mul_inv]

/-- The particular solution: `u_p = c r log r` has `u'' + u'/r - u/r² = 2c/r`. -/
theorem part_res (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    odeRes (partDD c r) (partD c r) (part c r) r = 2 * c / r := by
  unfold odeRes partDD partD part
  field_simp
  ring

/-- **General radial displacement** for `T = A + B log r`: with `K = β/(λ + 2μ)` and
`c = K B/2`, `u = c r log r + C₁ r + C₂/r` solves `u'' + u'/r - u/r² = K T'`. -/
theorem general_solves (K B C₁ C₂ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    odeRes (partDD (K * B / 2) r + genDD C₂ r) (partD (K * B / 2) r + genD C₁ C₂ r)
      (part (K * B / 2) r + gen C₁ C₂ r) r = K * (B / r) := by
  have h1 := part_res (K * B / 2) hr
  have h2 := LameCylinder.general_solves C₁ C₂ hr
  unfold odeRes at *
  field_simp at h1 h2 ⊢
  linear_combination h1 + h2

/-- Combined with `equilibrium_iff`: the displacement `c r log r + C₁ r + C₂/r` with
`c = β B/(2(λ + 2μ))` is in thermoelastic equilibrium under `T = A + B log r`. -/
theorem equilibrium_general (A B C₁ C₂ : ℝ) (hlm : lam + 2 * μ ≠ 0) {r : ℝ} (hr : 0 < r) :
    deriv (fun s => sigR lam μ β (partD (β / (lam + 2 * μ) * B / 2) s + genD C₁ C₂ s)
        (part (β / (lam + 2 * μ) * B / 2) s + gen C₁ C₂ s) s (logTemp A B s)) r +
      (sigR lam μ β (partD (β / (lam + 2 * μ) * B / 2) r + genD C₁ C₂ r)
          (part (β / (lam + 2 * μ) * B / 2) r + gen C₁ C₂ r) r (logTemp A B r) -
        sigT lam μ β (partD (β / (lam + 2 * μ) * B / 2) r + genD C₁ C₂ r)
          (part (β / (lam + 2 * μ) * B / 2) r + gen C₁ C₂ r) r (logTemp A B r)) / r = 0 := by
  have hr0 := hr.ne'
  set c := β / (lam + 2 * μ) * B / 2
  refine (equilibrium_iff lam μ β (u := fun s => part c s + gen C₁ C₂ s)
    (du := fun s => partD c s + genD C₁ C₂ s) (ddu := fun s => partDD c s + genDD C₂ s)
    (T := logTemp A B) (dT := fun s => B / s) ?_ ?_ (hasDerivAt_logTemp A B hr0) hr0
    hlm).mpr ?_
  · exact (hasDerivAt_part c hr0).add (LameCylinder.hasDerivAt_gen C₁ C₂ hr0)
  · exact (hasDerivAt_partD c hr0).add (LameCylinder.hasDerivAt_genD C₁ C₂ hr0)
  · exact general_solves _ B C₁ C₂ hr0

end Cylinder

end ContinuumMechanics.Thermoelastic
