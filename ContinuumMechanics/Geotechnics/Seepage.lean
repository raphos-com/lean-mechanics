import ContinuumMechanics.Fluids.Ideal
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Darcy flow through porous media and steady seepage

Groundwater flow through a rigid saturated soil in `ℝⁿ = Fin n → ℝ`, with the partial
derivatives `Korn.pd`, the gradient `Fluids.grad`, the divergence `Fluids.divergence` and the
Laplacian `Korn.lap`.

* **Darcy's law** `q = -K ∇h` for the hydraulic head `h = p/γ_w + z`, isotropic (`darcyFlux`)
  or with a conductivity matrix (`darcyFluxAniso`). With the continuity equation `div q = 0` of
  steady incompressible flow, the head satisfies `div(K∇h) = 0`, i.e. Laplace's equation
  `Δh = 0` in the isotropic case. For a diagonal conductivity `diag(k_x, k_z)` the coordinate
  stretch `x' = x √(k_z/k_x)` (the *transformed section*) reduces the seepage equation to
  Laplace's equation.
* **One-dimensional seepage**: through a homogeneous layer the head is linear and the flux is
  `q = K Δh / L`. For **layered soils**, continuity of flux (flow across the layers) gives the
  harmonic-mean conductivity `K_v = Σ dᵢ / Σ (dᵢ/Kᵢ)`, a common gradient (flow along the layers)
  gives the arithmetic mean `K_h = Σ Kᵢ dᵢ / Σ dᵢ`, and `K_v ≤ K_h`.
* **Seepage force and quick condition**: upward flow with gradient `i` reduces the vertical
  effective stress to `σ'_v = (γ' - i γ_w) z`; it vanishes at the critical gradient
  `i_c = γ'/γ_w`, and `FS = i_c / i` is the factor of safety against heave.
* **Dupuit's unconfined flow**: the parabolic free surface
  `h(x) = √(h₁² - (h₁² - h₂²) x / L)` takes the boundary values `h₁`, `h₂`, satisfies
  `d/dx (h dh/dx) = 0` and carries the discharge `q = K (h₁² - h₂²)/(2L)`.
* **Dirichlet principle**: for a harmonic head `h` and a compactly supported perturbation `v`,
  `∫ K (|∇(h + v)|² - |∇h|²) = ∫ K |∇v|² ≥ 0`, and a compactly supported harmonic head vanishes.

## Main results

* `divergence_darcyFlux`, `darcy_continuity_iff_laplace`: `div q = -K Δh`, steady seepage is
  Laplace's equation.
* `divergence_darcyFluxAniso`, `darcyFluxAniso_dot_grad_neg`: anisotropic seepage and positive
  dissipation for positive definite `K`.
* `divergence_darcyFluxAniso_diagonal_stretch`, `divergence_darcyFluxAniso_two`,
  `seepage_two_iff_laplace`: the transformed section.
* `seepage_homogeneous_layer`: linear head and `q = K Δh / L` in 1D.
* `flux_perpendicular`, `flux_parallel`, `kVertical_le_kHorizontal`: layered soils.
* `effStressUpward_eq`, `effStressUpward_eq_zero_iff`, `effStressUpward_pos_iff`,
  `criticalGradient_phase`, `one_lt_heaveSafetyFactor_iff`: seepage force and heave.
* `dupuitHead_zero`, `dupuitHead_L`, `dupuit_discharge`, `dupuit_continuity`: Dupuit flow.
* `integral_grad_dot_grad_eq_zero`, `dissipation_split`, `dissipation_minimal`,
  `eq_zero_of_harmonic_of_hasCompactSupport`: Dirichlet principle and uniqueness.

## References

* [Bear1972] J. Bear, *Dynamics of Fluids in Porous Media*, §§5.1–5.10, 7.1, 8.1.
* [Harr1962] M. E. Harr, *Groundwater and Seepage*, Ch. 1–2.
* [Terzaghi1996] K. Terzaghi, R. B. Peck, G. Mesri, *Soil Mechanics in Engineering Practice*,
  3rd ed., §§7, 11.
-/

open Matrix MeasureTheory

noncomputable section

namespace ContinuumMechanics.Geotechnics

open Korn Fluids

variable {n : ℕ}

/-! ### Darcy's law and the seepage equation -/

/-- The hydraulic head `h = p/γ_w + z`, where `z = x k` is the elevation (coordinate `k` points
upwards), `p` the pore-water pressure and `γ_w` the unit weight of water. -/
def hydraulicHead (γw : ℝ) (p : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  p x / γw + x k

/-- **Darcy's law** for an isotropic soil: the specific discharge is `q = -K ∇h`. -/
def darcyFlux (K : ℝ) (h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := -(K • grad h x)

/-- **Darcy's law** for an anisotropic soil with conductivity matrix `K`: `q = -K ∇h`. -/
def darcyFluxAniso (K : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  -(K *ᵥ grad h x)

/-- The isotropic law is the anisotropic one with `K • 1`. -/
theorem darcyFlux_eq_aniso (K : ℝ) (h : (Fin n → ℝ) → ℝ) :
    darcyFlux K h = darcyFluxAniso (K • 1) h := by
  funext x
  simp [darcyFlux, darcyFluxAniso, smul_mulVec]

/-- Under a hydrostatic pressure `p = γ_w (z₀ - z)` the hydraulic head is the constant `z₀`. -/
theorem hydraulicHead_hydrostatic {γw : ℝ} (hγ : γw ≠ 0) (z₀ : ℝ) (k : Fin n) :
    hydraulicHead γw (fun x => γw * (z₀ - x k)) k = fun _ => z₀ := by
  funext x
  simp only [hydraulicHead]
  field_simp
  ring

/-- No seepage in hydrostatic conditions: a constant head drives no Darcy flux. -/
theorem darcyFlux_const (K c : ℝ) (x : Fin n → ℝ) :
    darcyFlux K (fun _ => c) x = 0 := by
  ext j
  simp [darcyFlux, grad, pd]

/-- `∂ᵢ(-Σⱼ cⱼ Fⱼ) = -Σⱼ cⱼ ∂ᵢFⱼ`. -/
theorem pd_neg_sum_mul {F : Fin n → (Fin n → ℝ) → ℝ} (c : Fin n → ℝ)
    (hF : ∀ j, Differentiable ℝ (F j)) (i : Fin n) (x : Fin n → ℝ) :
    pd (fun y => -∑ j, c j * F j y) i x = -∑ j, c j * pd (F j) i x := by
  have hd : HasFDerivAt (fun y => -∑ j, c j * F j y) (-∑ j, c j • fderiv ℝ (F j) x) x :=
    (HasFDerivAt.fun_sum fun j _ => (hF j x).hasFDerivAt.const_mul (c j)).neg
  rw [pd_eq hd]
  simp [pd]

/-- **Steady seepage, anisotropic**: `div q = -Σᵢⱼ Kᵢⱼ ∂ᵢ∂ⱼh`. -/
theorem divergence_darcyFluxAniso (K : Matrix (Fin n) (Fin n) ℝ) {h : (Fin n → ℝ) → ℝ}
    (hh : ContDiff ℝ 2 h) (x : Fin n → ℝ) :
    divergence (darcyFluxAniso K h) x = -∑ i, ∑ j, K i j * pd (pd h j) i x := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pd_neg_sum_mul (K i) (fun j => (contDiff_pd hh j).differentiable one_ne_zero) i x

/-- **Steady seepage, isotropic**: `div q = -K Δh`. -/
theorem divergence_darcyFlux (K : ℝ) {h : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ 2 h)
    (x : Fin n → ℝ) : divergence (darcyFlux K h) x = -K * lap h x := by
  rw [darcyFlux_eq_aniso, divergence_darcyFluxAniso _ hh, lap, Finset.mul_sum]
  simp [Matrix.one_apply]

/-- **Laplace's equation for the head**: with `K ≠ 0`, the continuity equation `div q = 0` of
steady incompressible seepage holds iff `Δh = 0`. -/
theorem darcy_continuity_iff_laplace {K : ℝ} (hK : K ≠ 0) {h : (Fin n → ℝ) → ℝ}
    (hh : ContDiff ℝ 2 h) (x : Fin n → ℝ) :
    divergence (darcyFlux K h) x = 0 ↔ lap h x = 0 := by
  rw [divergence_darcyFlux K hh]
  constructor
  · intro h0
    have : K * lap h x = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hK
  · intro h0
    simp [h0]

/-- **Water flows down the head gradient**: for a positive definite conductivity matrix and
`∇h ≠ 0`, the dissipation rate `-q·∇h = ∇h·K∇h` is positive. -/
theorem darcyFluxAniso_dot_grad_neg {K : Matrix (Fin n) (Fin n) ℝ} (hK : K.PosDef)
    {h : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : grad h x ≠ 0) :
    darcyFluxAniso K h x ⬝ᵥ grad h x < 0 := by
  have := hK.dotProduct_mulVec_pos hx
  rw [star_trivial] at this
  rw [darcyFluxAniso, neg_dotProduct, dotProduct_comm]
  linarith

/-! ### Transformation of anisotropic seepage to Laplace's equation -/

/-- The diagonal coordinate stretch `x ↦ (cᵢ xᵢ)ᵢ`. -/
def stretch (c : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => c i • ContinuousLinearMap.proj i

/-- Components of the stretch. -/
@[simp] theorem stretch_apply (c x : Fin n → ℝ) (i : Fin n) : stretch c x i = c i * x i := rfl

/-- The stretch maps `eⱼ` to `cⱼ eⱼ`. -/
theorem stretch_single (c : Fin n → ℝ) (j : Fin n) :
    stretch c (Pi.single j 1) = c j • Pi.single j 1 := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- Chain rule for the stretch: `∂ⱼ(g ∘ S) = cⱼ (∂ⱼg) ∘ S`. -/
theorem pd_comp_stretch {g : (Fin n → ℝ) → ℝ} (hg : Differentiable ℝ g) (c : Fin n → ℝ)
    (j : Fin n) (x : Fin n → ℝ) :
    pd (fun y => g (stretch c y)) j x = c j * pd g j (stretch c x) := by
  have hd := (hg (stretch c x)).hasFDerivAt.comp x (stretch c).hasFDerivAt
  rw [show (fun y => g (stretch c y)) = g ∘ stretch c from rfl, pd_eq hd]
  simp [stretch_single, pd]

/-- Second derivatives under the stretch: `∂ⱼ∂ⱼ(g ∘ S) = cⱼ² (∂ⱼ∂ⱼg) ∘ S`. -/
theorem pd_pd_comp_stretch {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 2 g) (c : Fin n → ℝ)
    (j : Fin n) (x : Fin n → ℝ) :
    pd (pd (fun y => g (stretch c y)) j) j x = c j ^ 2 * pd (pd g j) j (stretch c x) := by
  have h1 : pd (fun y => g (stretch c y)) j = fun y => c j * pd g j (stretch c y) :=
    funext fun y => pd_comp_stretch (hg.differentiable (by norm_num)) c j y
  have hd : Differentiable ℝ (pd g j) := (contDiff_pd hg j).differentiable one_ne_zero
  have hd2 := ((hd (stretch c x)).hasFDerivAt.comp x (stretch c).hasFDerivAt).const_mul (c j)
  rw [h1, show (fun y => c j * pd g j (stretch c y)) = fun y => c j * (pd g j ∘ stretch c) y
    from rfl, pd_eq hd2]
  simp [stretch_single, pd]
  ring

/-- **Transformed section**: if `kᵢ cᵢ² = κ` for all `i`, then for `h = g ∘ S` the seepage
operator of the diagonal conductivity `diag k` becomes the Laplacian of `g`:
`div(diag(k) ∇h) = κ (Δg) ∘ S`. -/
theorem divergence_darcyFluxAniso_diagonal_stretch {k c : Fin n → ℝ} {κ : ℝ}
    (hkc : ∀ i, k i * c i ^ 2 = κ) {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 2 g)
    (x : Fin n → ℝ) :
    divergence (darcyFluxAniso (diagonal k) (fun y => g (stretch c y))) x =
      -(κ * lap g (stretch c x)) := by
  have hh : ContDiff ℝ 2 (fun y => g (stretch c y)) := hg.comp (stretch c).contDiff
  rw [divergence_darcyFluxAniso _ hh, lap, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [pd_pd_comp_stretch hg, ← mul_assoc, hkc]

/-- **2D anisotropic seepage** (`K = diag(k_x, k_z)`): with the transformed abscissa
`x' = x √(k_z/k_x)`, i.e. `h(x, z) = g(x √(k_z/k_x), z)`, one has
`div(K∇h) = -k_z (Δg)(x', z)`, so `h` solves the anisotropic seepage equation iff `g` is
harmonic. -/
theorem divergence_darcyFluxAniso_two {kx kz : ℝ} (hkx : 0 < kx) (hkz : 0 < kz)
    {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ 2 g) (x : Fin 2 → ℝ) :
    divergence (darcyFluxAniso (diagonal ![kx, kz])
        (fun y => g (stretch ![√(kz / kx), 1] y))) x =
      -(kz * lap g (stretch ![√(kz / kx), 1] x)) := by
  refine divergence_darcyFluxAniso_diagonal_stretch (fun i => ?_) hg x
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [Real.sq_sqrt (div_nonneg hkz.le hkx.le)]
    field_simp
  · simp

/-- The transformed 2D section: `h` satisfies `div(K∇h) = 0` iff `g` is harmonic at the
transformed point. -/
theorem seepage_two_iff_laplace {kx kz : ℝ} (hkx : 0 < kx) (hkz : 0 < kz)
    {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ 2 g) (x : Fin 2 → ℝ) :
    divergence (darcyFluxAniso (diagonal ![kx, kz])
        (fun y => g (stretch ![√(kz / kx), 1] y))) x = 0 ↔
      lap g (stretch ![√(kz / kx), 1] x) = 0 := by
  rw [divergence_darcyFluxAniso_two hkx hkz hg, neg_eq_zero, mul_eq_zero]
  simp [hkz.ne']

/-! ### One-dimensional seepage and layered soils -/

/-- A head profile with vanishing second derivative is linear. -/
theorem exists_linear_of_deriv_deriv {h : ℝ → ℝ} (hd : Differentiable ℝ h)
    (hd2 : Differentiable ℝ (deriv h)) (h0 : ∀ z, deriv (deriv h) z = 0) :
    ∃ s, ∀ z, h z = h 0 + s * z ∧ deriv h z = s := by
  have hc := is_const_of_deriv_eq_zero hd2 h0
  refine ⟨deriv h 0, fun z => ⟨?_, hc z 0⟩⟩
  have hφ : Differentiable ℝ fun y => h y - deriv h 0 * y :=
    hd.sub ((differentiable_id).const_mul _)
  have hφ' : ∀ y, deriv (fun y => h y - deriv h 0 * y) y = 0 := fun y => by
    rw [((hd y).hasDerivAt.fun_sub ((hasDerivAt_id' y).const_mul (deriv h 0))).deriv, hc y 0]
    ring
  have := is_const_of_deriv_eq_zero hφ hφ' z 0
  simp only [mul_zero, sub_zero] at this
  linarith

/-- **1D steady seepage through a homogeneous layer** of thickness `L`: if the continuity
equation `d/dz (K dh/dz) = 0` holds with `K ≠ 0`, the head is linear,
`h(z) = h(0) + (h(L) - h(0)) z / L`, and the Darcy flux is `q = -K dh/dz = K Δh / L` with the
head loss `Δh = h(0) - h(L)`. -/
theorem seepage_homogeneous_layer {h : ℝ → ℝ} {K L : ℝ} (hK : K ≠ 0) (hL : L ≠ 0)
    (hd : Differentiable ℝ h) (hd2 : Differentiable ℝ (deriv h))
    (hsteady : ∀ z, deriv (fun y => K * deriv h y) z = 0) (z : ℝ) :
    h z = h 0 + (h L - h 0) * z / L ∧ -K * deriv h z = K * (h 0 - h L) / L := by
  have h0 : ∀ z, deriv (deriv h) z = 0 := fun z => by
    have := hsteady z
    rw [deriv_const_mul _ (hd2 z)] at this
    exact (mul_eq_zero.mp this).resolve_left hK
  obtain ⟨s, hs⟩ := exists_linear_of_deriv_deriv hd hd2 h0
  have hsL : s = (h L - h 0) / L := by
    rw [(hs L).1]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [(hs z).1, hsL]
    ring
  · rw [(hs z).2, hsL]
    ring

variable {ι : Type*} [Fintype ι]

/-- Equivalent conductivity of a layered soil for flow **perpendicular** to the layers
(thicknesses `dᵢ`, conductivities `Kᵢ`): the weighted harmonic mean `Σ dᵢ / Σ (dᵢ / Kᵢ)`. -/
def kVertical (d K : ι → ℝ) : ℝ := (∑ i, d i) / ∑ i, d i / K i

/-- Equivalent conductivity of a layered soil for flow **parallel** to the layers: the
weighted arithmetic mean `Σ Kᵢ dᵢ / Σ dᵢ`. -/
def kHorizontal (d K : ι → ℝ) : ℝ := (∑ i, K i * d i) / ∑ i, d i

/-- **Flow perpendicular to the layers**: by continuity of the flux across the interfaces the
same flux `q` crosses every layer, with Darcy's law `q = Kᵢ Δhᵢ / dᵢ` in each layer; then the
total head loss `Δh = Σ Δhᵢ` over the total thickness `Σ dᵢ` drives `q = K_v Δh / Σ dᵢ`. -/
theorem flux_perpendicular [Nonempty ι] {d K Δh : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hK : ∀ i, 0 < K i) {q : ℝ} (hq : ∀ i, q = K i * Δh i / d i) :
    q = kVertical d K * (∑ i, Δh i) / ∑ i, d i := by
  have hΔ : ∀ i, Δh i = q * (d i / K i) := fun i => by
    rw [hq i]
    field_simp [(hd i).ne', (hK i).ne']
  have hD : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  have hR : 0 < ∑ i, d i / K i :=
    Finset.sum_pos (fun i _ => div_pos (hd i) (hK i)) Finset.univ_nonempty
  simp only [kVertical, hΔ, ← Finset.mul_sum]
  field_simp

/-- **Flow parallel to the layers**: all layers share the hydraulic gradient `i`, layer `j`
carries `Qⱼ = Kⱼ i dⱼ`, and the total discharge is `Σ Qⱼ = K_h i Σ dⱼ`. -/
theorem flux_parallel [Nonempty ι] {d K : ι → ℝ} (hd : ∀ i, 0 < d i) (i : ℝ) :
    ∑ j, K j * i * d j = kHorizontal d K * i * ∑ j, d j := by
  have hD : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  simp only [kHorizontal]
  field_simp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`K_v ≤ K_h`**: the weighted harmonic mean of the layer conductivities does not exceed
their weighted arithmetic mean, so a stratified deposit is more permeable along the layers. -/
theorem kVertical_le_kHorizontal [Nonempty ι] {d K : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hK : ∀ i, 0 < K i) : kVertical d K ≤ kHorizontal d K := by
  have hD : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  have hR : 0 < ∑ i, d i / K i :=
    Finset.sum_pos (fun i _ => div_pos (hd i) (hK i)) Finset.univ_nonempty
  have hC : 0 < ∑ i, K i * d i :=
    Finset.sum_pos (fun i _ => mul_pos (hK i) (hd i)) Finset.univ_nonempty
  have hT := Finset.sq_sum_div_le_sum_sq_div Finset.univ d (g := fun i => K i * d i)
    fun i _ => mul_pos (hK i) (hd i)
  have he : ∑ i, d i ^ 2 / (K i * d i) = ∑ i, d i / K i :=
    Finset.sum_congr rfl fun i _ => by field_simp [(hd i).ne', (hK i).ne']
  rw [he, div_le_iff₀ hC] at hT
  rw [kVertical, kHorizontal, div_le_div_iff₀ hR hD]
  nlinarith

/-- For layers of equal conductivity `k` both equivalent conductivities equal `k`. -/
theorem kVertical_const [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) {k : ℝ} (hk : k ≠ 0) :
    kVertical d (fun _ => k) = k ∧ kHorizontal d (fun _ => k) = k := by
  have hD : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  refine ⟨?_, ?_⟩
  · rw [kVertical, ← Finset.sum_div]
    field_simp
  · rw [kHorizontal, ← Finset.mul_sum]
    field_simp

/-! ### Seepage force, quick condition and heave -/

/-- The submerged (buoyant) unit weight `γ' = γ_sat - γ_w`. -/
def submergedUnitWeight (γsat γw : ℝ) : ℝ := γsat - γw

/-- Vertical effective stress at depth `z` below the surface of a saturated soil (free water
level at the surface) under **upward** flow with hydraulic gradient `i`: the total stress
`γ_sat z` minus the pore pressure `γ_w (z + i z)`, the head at depth `z` exceeding the
hydrostatic one by `i z`. -/
def effStressUpward (γsat γw i z : ℝ) : ℝ := γsat * z - γw * (z + i * z)

/-- **Seepage force**: `σ'_v = (γ' - i γ_w) z`; upward flow exerts the seepage force
`j = i γ_w` per unit volume, reducing the effective stress. -/
theorem effStressUpward_eq (γsat γw i z : ℝ) :
    effStressUpward γsat γw i z = (submergedUnitWeight γsat γw - i * γw) * z := by
  simp only [effStressUpward, submergedUnitWeight]
  ring

/-- The critical hydraulic gradient `i_c = γ'/γ_w`. -/
def criticalGradient (γsub γw : ℝ) : ℝ := γsub / γw

/-- **Quick (boiling) condition**: at depth `z > 0` the effective stress vanishes iff the
gradient equals the critical gradient `i_c = γ'/γ_w`. -/
theorem effStressUpward_eq_zero_iff {γsat γw i z : ℝ} (hγ : 0 < γw) (hz : 0 < z) :
    effStressUpward γsat γw i z = 0 ↔ i = criticalGradient (submergedUnitWeight γsat γw) γw := by
  rw [effStressUpward_eq, mul_eq_zero, or_iff_left hz.ne', criticalGradient, eq_div_iff hγ.ne']
  constructor <;> intro h <;> linarith

/-- The soil keeps a positive effective stress at depth `z > 0` iff `i < i_c`. -/
theorem effStressUpward_pos_iff {γsat γw i z : ℝ} (hγ : 0 < γw) (hz : 0 < z) :
    0 < effStressUpward γsat γw i z ↔ i < criticalGradient (submergedUnitWeight γsat γw) γw := by
  rw [effStressUpward_eq, criticalGradient, lt_div_iff₀ hγ, mul_pos_iff_of_pos_right hz]
  constructor <;> intro h <;> linarith

/-- The critical gradient from the phase relations: with
`γ_sat = (G_s + e) γ_w / (1 + e)` one has `i_c = (G_s - 1)/(1 + e)`. -/
theorem criticalGradient_phase {Gs e γw : ℝ} (hγ : γw ≠ 0) (he : 1 + e ≠ 0) :
    criticalGradient (submergedUnitWeight ((Gs + e) * γw / (1 + e)) γw) γw =
      (Gs - 1) / (1 + e) := by
  simp only [criticalGradient, submergedUnitWeight]
  field_simp
  ring

/-- The factor of safety against heave (piping) `FS = i_c / i`. -/
def heaveSafetyFactor (ic i : ℝ) : ℝ := ic / i

/-- `FS > 1` iff the exit gradient is below critical. -/
theorem one_lt_heaveSafetyFactor_iff {ic i : ℝ} (hi : 0 < i) :
    1 < heaveSafetyFactor ic i ↔ i < ic :=
  one_lt_div hi

/-- `FS = 1` exactly at the quick condition. -/
theorem heaveSafetyFactor_eq_one_iff {ic i : ℝ} (hi : 0 < i) :
    heaveSafetyFactor ic i = 1 ↔ i = ic := by
  rw [heaveSafetyFactor, div_eq_one_iff_eq hi.ne', eq_comm]

/-! ### Dupuit's unconfined flow -/

/-- **Dupuit's discharge** per unit width between water levels `h₁`, `h₂` a distance `L`
apart: `q = K (h₁² - h₂²) / (2L)`. -/
def dupuitDischarge (K h₁ h₂ L : ℝ) : ℝ := K * (h₁ ^ 2 - h₂ ^ 2) / (2 * L)

/-- The Dupuit free-surface (parabola) `h(x) = √(h₁² - (h₁² - h₂²) x / L)`. -/
def dupuitHead (h₁ h₂ L x : ℝ) : ℝ := √(h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L)

/-- Upstream boundary value `h(0) = h₁`. -/
theorem dupuitHead_zero {h₁ : ℝ} (h₂ L : ℝ) (h1 : 0 ≤ h₁) : dupuitHead h₁ h₂ L 0 = h₁ := by
  simp [dupuitHead, Real.sqrt_sq h1]

/-- Downstream boundary value `h(L) = h₂`. -/
theorem dupuitHead_L {h₂ L : ℝ} (h₁ : ℝ) (h2 : 0 ≤ h₂) (hL : L ≠ 0) :
    dupuitHead h₁ h₂ L L = h₂ := by
  rw [dupuitHead, mul_div_assoc, div_self hL, mul_one, sub_sub_cancel, Real.sqrt_sq h2]

/-- The radicand of the Dupuit parabola is positive on `[0, L]`. -/
theorem dupuit_radicand_pos {h₁ h₂ L x : ℝ} (h1 : 0 < h₁) (h2 : 0 < h₂) (hL : 0 < L)
    (hx0 : 0 ≤ x) (hxL : x ≤ L) : 0 < h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L := by
  have he : h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L = (h₁ ^ 2 * (L - x) + h₂ ^ 2 * x) / L := by
    field_simp
    ring
  rw [he]
  refine div_pos ?_ hL
  rcases hxL.lt_or_eq with hlt | heq
  · have : 0 < h₁ ^ 2 * (L - x) := by positivity
    have : 0 ≤ h₂ ^ 2 * x := by positivity
    linarith
  · subst heq
    simp only [sub_self, mul_zero, zero_add]
    positivity

/-- Derivative of the Dupuit head where the radicand is positive. -/
theorem hasDerivAt_dupuitHead {h₁ h₂ L x : ℝ} (hr : 0 < h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L) :
    HasDerivAt (dupuitHead h₁ h₂ L)
      (-((h₁ ^ 2 - h₂ ^ 2) / L) / (2 * dupuitHead h₁ h₂ L x)) x := by
  have hr' : HasDerivAt (fun y => h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * y / L)
      (-((h₁ ^ 2 - h₂ ^ 2) * 1 / L)) x :=
    (((hasDerivAt_id' x).const_mul (h₁ ^ 2 - h₂ ^ 2)).div_const L).const_sub (h₁ ^ 2)
  have := hr'.sqrt hr.ne'
  rw [mul_one] at this
  exact this

/-- **Dupuit's equation** `h dh/dx = -(h₁² - h₂²)/(2L)`, i.e. the discharge
`-K h dh/dx` equals `K (h₁² - h₂²)/(2L)`. -/
theorem dupuitHead_mul_deriv {h₁ h₂ L x : ℝ} (hL : L ≠ 0)
    (hr : 0 < h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L) :
    dupuitHead h₁ h₂ L x * deriv (dupuitHead h₁ h₂ L) x = -(h₁ ^ 2 - h₂ ^ 2) / (2 * L) := by
  rw [(hasDerivAt_dupuitHead hr).deriv]
  have hs : dupuitHead h₁ h₂ L x ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  field_simp

/-- **Dupuit discharge**: `-K h dh/dx = K (h₁² - h₂²)/(2L)` at every section. -/
theorem dupuit_discharge {K h₁ h₂ L x : ℝ} (hL : L ≠ 0)
    (hr : 0 < h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L) :
    -K * (dupuitHead h₁ h₂ L x * deriv (dupuitHead h₁ h₂ L) x) = dupuitDischarge K h₁ h₂ L := by
  rw [dupuitHead_mul_deriv hL hr, dupuitDischarge]
  ring

/-- **Continuity for Dupuit flow**: `d/dx (h dh/dx) = 0` wherever the radicand is positive. -/
theorem dupuit_continuity {h₁ h₂ L x : ℝ} (hL : L ≠ 0)
    (hr : 0 < h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * x / L) :
    deriv (fun y => dupuitHead h₁ h₂ L y * deriv (dupuitHead h₁ h₂ L) y) x = 0 := by
  have hc : Continuous fun y => h₁ ^ 2 - (h₁ ^ 2 - h₂ ^ 2) * y / L := by fun_prop
  have hev : (fun y => dupuitHead h₁ h₂ L y * deriv (dupuitHead h₁ h₂ L) y) =ᶠ[nhds x]
      fun _ => -(h₁ ^ 2 - h₂ ^ 2) / (2 * L) :=
    ((isOpen_lt continuous_const hc).eventually_mem hr).mono fun y hy =>
      dupuitHead_mul_deriv hL hy
  rw [hev.deriv_eq, deriv_const]

/-! ### Dirichlet principle for the seepage dissipation -/

/-- The squared head gradient `|∇h|² = Σⱼ (∂ⱼh)²`; `K |∇h|²` is the rate of viscous
dissipation per unit volume of steady isotropic Darcy flow. -/
def gradNormSq (h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ j, pd h j x ^ 2

/-- Integrability of `|∇v|²` for a compactly supported `C¹` field. -/
theorem integrable_gradNormSq {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) : Integrable (gradNormSq v) := by
  have he : gradNormSq v = fun x => ∑ j, pd v j x * pd v j x :=
    funext fun x => Finset.sum_congr rfl fun j _ => sq _
  rw [he]
  exact (continuous_finsetSum _ fun j _ => (continuous_pd hv j).mul
    (continuous_pd hv j)).integrable_of_hasCompactSupport
    (hasCompactSupport_sum _ _ fun j _ => (hasCompactSupport_pd hvc j).mul_left)

/-- **The cross term vanishes**: for a harmonic head `h` and a compactly supported
perturbation `v`, `∫ ∇h · ∇v = -∫ Δh v = 0`. -/
theorem integral_grad_dot_grad_eq_zero {h v : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (hlap : ∀ x, lap h x = 0) :
    ∫ x, ∑ j, pd h j x * pd v j x = 0 := by
  rw [integral_finsetSum _ fun j _ => integrable_mul_cs
    (continuous_pd (hh.of_le (by norm_num)) j) (continuous_pd hv j) (hasCompactSupport_pd hvc j)]
  have hj : ∀ j, ∫ x, pd h j x * pd v j x = -∫ x, pd (pd h j) j x * v x := fun j =>
    integral_mul_pd' (contDiff_pd hh j) hv hvc j
  simp only [hj, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ fun j _ =>
    integrable_mul_cs (continuous_pd_pd hh j j) hv.continuous hvc]
  have h0 : (fun x => ∑ j, pd (pd h j) j x * v x) = fun _ => 0 := funext fun x => by
    rw [← Finset.sum_mul]
    have := hlap x
    rw [lap] at this
    rw [this, zero_mul]
  rw [h0]
  simp

/-- **Energy splitting (Dirichlet principle)**: for a harmonic head `h` and a compactly
supported perturbation `v`,
`∫ K (|∇(h + v)|² - |∇h|²) = ∫ K |∇v|²`. -/
theorem dissipation_split (K : ℝ) {h v : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (hlap : ∀ x, lap h x = 0) :
    ∫ x, K * (gradNormSq (fun y => h y + v y) x - gradNormSq h x) =
      ∫ x, K * gradNormSq v x := by
  have hpd : ∀ j x, pd (fun y => h y + v y) j x = pd h j x + pd v j x := fun j x =>
    congrFun (pd_add (hh.differentiable (by norm_num)) (hv.differentiable one_ne_zero) j) x
  have hpt : ∀ x, K * (gradNormSq (fun y => h y + v y) x - gradNormSq h x) =
      2 * K * (∑ j, pd h j x * pd v j x) + K * gradNormSq v x := fun x => by
    simp only [gradNormSq, hpd]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  have hint : Integrable fun x => ∑ j, pd h j x * pd v j x :=
    integrable_finsetSum _ fun j _ => integrable_mul_cs
      (continuous_pd (hh.of_le (by norm_num)) j) (continuous_pd hv j) (hasCompactSupport_pd hvc j)
  rw [integral_add (hint.const_mul _) ((integrable_gradNormSq hv hvc).const_mul _),
    integral_const_mul, integral_grad_dot_grad_eq_zero hh hv hvc hlap]
  simp

/-- **Minimum dissipation**: among heads `h + v` with the same values outside a compact set,
the harmonic head `h` minimizes the dissipation (`K ≥ 0`). -/
theorem dissipation_minimal {K : ℝ} (hK : 0 ≤ K) {h v : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (hlap : ∀ x, lap h x = 0) :
    0 ≤ ∫ x, K * (gradNormSq (fun y => h y + v y) x - gradNormSq h x) := by
  rw [dissipation_split K hh hv hvc hlap]
  exact integral_nonneg fun x =>
    mul_nonneg hK (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- **Uniqueness**: a compactly supported harmonic head on `ℝⁿ`, `n ≥ 1`, vanishes; so two
steady seepage heads differing by a compactly supported function coincide. -/
theorem eq_zero_of_harmonic_of_hasCompactSupport [NeZero n] {v : (Fin n → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hlap : ∀ x, lap v x = 0) :
    v = 0 := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have h0 := integral_grad_dot_grad_eq_zero hv hv1 hvc hlap
  have hcont : Continuous fun x => ∑ j, pd v j x * pd v j x :=
    continuous_finsetSum _ fun j _ => (continuous_pd hv1 j).mul (continuous_pd hv1 j)
  have hint : Integrable fun x => ∑ j, pd v j x * pd v j x :=
    integrable_finsetSum _ fun j _ =>
      integrable_mul_cs (continuous_pd hv1 j) (continuous_pd hv1 j) (hasCompactSupport_pd hvc j)
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.sum_nonneg fun j _ => mul_self_nonneg (pd v j x)) hint).mp h0
  have hfun := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae
  have hpd : ∀ x j, pd v j x = 0 := fun x j => by
    have hx := congrFun hfun x
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (pd v j x))).mp hx j (Finset.mem_univ j)
    exact mul_self_eq_zero.mp this
  have hf' : ∀ x, fderiv ℝ v x = 0 := fun x => by
    ext1 y
    rw [clm_apply_eq_sum, _root_.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by
      rw [show fderiv ℝ v x (e j) = 0 from hpd x j, mul_zero]
  have hconst := is_const_of_fderiv_eq_zero (hv1.differentiable one_ne_zero) hf'
  funext x
  by_contra hne
  have huniv : tsupport v = Set.univ := Set.eq_univ_of_forall fun y =>
    subset_tsupport _ (show v y ≠ 0 by rw [hconst y x]; exact hne)
  exact noncompact_univ (Fin n → ℝ) (huniv ▸ hvc)

end ContinuumMechanics.Geotechnics
