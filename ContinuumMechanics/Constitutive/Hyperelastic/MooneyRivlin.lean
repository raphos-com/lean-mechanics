import ContinuumMechanics.Constitutive.Hyperelastic.NeoHookean
import ContinuumMechanics.Tensor.Invariants

/-!
# The compressible Mooney–Rivlin material

The **compressible Mooney–Rivlin** stored energy (dimension `d`, `C = FᵀF`, `J = det F`) is

`W(F) = c₁ (I₁(C) - d) + c₂ (I₂(C) - d(d-1)/2) - κ ln J + (λ/2)(ln J)²`,  `κ = 2c₁ + 2c₂(d - 1)`,

the choice of `κ` making the reference configuration stress free ([Ciarlet1988], §4.10;
[Holzapfel2000], §6.5). It splits exactly as

`W = W_neoHooke(λ, κ) + W_SVK(4c₂, -2c₂)`,

so its stress and its linearisation follow from the neo-Hookean and Saint Venant–Kirchhoff
results:

`P = 2c₁ F + 2c₂ (I₁(C) F - F C) + (λ ln J - κ) F⁻ᵀ`,

and `d/dt P(I + tH)|₀ = λ' (tr H) I + 2μ' sym H` with `μ' = 2c₁ + 2c₂(d - 2)` (`= 2(c₁ + c₂)` in
3D) and `λ' = λ + 4c₂`.

## Main results

* `Lin.mooneyRivlinEnergy_eq`: the splitting.
* `Lin.mooneyRivlin_isPiolaOf`: the stress formula.
* `Lin.mooneyRivlin_piola_one`: the reference configuration is stress free.
* `Lin.mooneyRivlin_linearization`: consistency with linear elasticity.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §4.10.
* [Holzapfel2000] G. A. Holzapfel, *Nonlinear Solid Mechanics*, §6.5.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

variable (lam c₁ c₂ : ℝ)

/-- The volumetric coefficient `κ = 2c₁ + 2c₂(d - 1)` making the reference state stress free. -/
noncomputable def mooneyRivlinKappa : ℝ := 2 * c₁ + 2 * c₂ * ((finrank ℝ E : ℝ) - 1)

/-- The **compressible Mooney–Rivlin energy**
`W = c₁ (I₁(C) - d) + c₂ (I₂(C) - d(d-1)/2) - κ ln J + (λ/2)(ln J)²`. [Ciarlet1988], §4.10. -/
noncomputable def mooneyRivlinEnergy (F : Lin E) : ℝ :=
  c₁ * (I₁ (rightCG F) - finrank ℝ E) +
    c₂ * (I₂ (rightCG F) - finrank ℝ E * ((finrank ℝ E : ℝ) - 1) / 2) -
    mooneyRivlinKappa (E := E) c₁ c₂ * Real.log F.det + lam / 2 * Real.log F.det ^ 2

/-- The Mooney–Rivlin energy is the neo-Hookean energy with shear coefficient `κ` plus the SVK
energy with moduli `(4c₂, -2c₂)`. -/
theorem mooneyRivlinEnergy_eq (F : Lin E) :
    mooneyRivlinEnergy lam c₁ c₂ F = neoHookeanEnergy lam (mooneyRivlinKappa (E := E) c₁ c₂) F +
      svkEnergy (4 * c₂) (-2 * c₂) F := by
  have hC : (rightCG F)ᵀ = rightCG F := by rw [rightCG, transpose_mul, transpose_transpose]
  have h1 : tr (rightCG F) = F ⊡ F := rfl
  have hE : greenLagrange F ⊡ greenLagrange F =
      4⁻¹ * (tr (rightCG F * rightCG F) - 2 * tr (rightCG F) + finrank ℝ E) := by
    rw [dcontr_apply, greenLagrange, transpose_smul, star_sub, hC, transpose_one]
    simp only [smul_mul_smul_comm, mul_sub, sub_mul, one_mul, mul_one, map_smul, map_sub,
      tr_one, smul_eq_mul]
    ring
  have htr : tr (greenLagrange F) = 2⁻¹ * (tr (rightCG F) - finrank ℝ E) := by
    rw [greenLagrange, map_smul, map_sub, tr_one, smul_eq_mul]
  simp only [mooneyRivlinEnergy, neoHookeanEnergy, svkEnergy, svkStrainEnergy, mooneyRivlinKappa,
    I₁, I₂, hE, htr, h1]
  ring

/-- The Mooney–Rivlin first Piola–Kirchhoff stress. -/
noncomputable def mooneyRivlinPiola (F : Lin E) : Lin E :=
  neoHookeanPiola lam (mooneyRivlinKappa (E := E) c₁ c₂) F + svkPiola (4 * c₂) (-2 * c₂) F

/-- **Mooney–Rivlin stress**: `P = W_F`. [Holzapfel2000], §6.5. -/
theorem mooneyRivlin_isPiolaOf {F : Lin E} (hF : 0 < F.det) :
    IsPiolaOf (mooneyRivlinEnergy lam c₁ c₂) (mooneyRivlinPiola lam c₁ c₂ F) F := by
  have := (neoHookean_isPiolaOf lam (mooneyRivlinKappa (E := E) c₁ c₂) hF).add
    (svk_isPiolaOf (4 * c₂) (-2 * c₂) F)
  have hfun : mooneyRivlinEnergy lam c₁ c₂ = fun G : Lin E =>
      neoHookeanEnergy lam (mooneyRivlinKappa (E := E) c₁ c₂) G + svkEnergy (4 * c₂) (-2 * c₂) G :=
    funext (mooneyRivlinEnergy_eq lam c₁ c₂)
  have hP : dcontrCLM (mooneyRivlinPiola lam c₁ c₂ F) =
      dcontrCLM (neoHookeanPiola lam (mooneyRivlinKappa (E := E) c₁ c₂) F) +
        dcontrCLM (svkPiola (4 * c₂) (-2 * c₂) F) := by
    ext H; simp [mooneyRivlinPiola]
  rw [IsPiolaOf, hfun, hP]
  exact this

/-- The explicit form `P = 2c₁ F + 2c₂ (I₁(C) F - F C) + (λ ln J - κ) F⁻ᵀ`. -/
theorem mooneyRivlinPiola_eq (F : Lin E) :
    mooneyRivlinPiola lam c₁ c₂ F = (2 * c₁) • F +
      (2 * c₂) • (I₁ (rightCG F) • F - F * rightCG F) +
      (lam * Real.log F.det - mooneyRivlinKappa (E := E) c₁ c₂) • (F⁻¹ʳ)ᵀ := by
  rw [mooneyRivlinPiola, svkPiola, Lin4.isotropic_apply,
    sym_eq_self_of_mem (greenLagrange_mem_sym F),
    neoHookeanPiola, I₁, greenLagrange, map_smul, map_sub, tr_one]
  simp only [mul_add, mul_smul_comm, mul_sub, mul_one, smul_eq_mul, mooneyRivlinKappa]
  module

/-- The reference configuration is **stress free**. -/
theorem mooneyRivlin_piola_one : mooneyRivlinPiola lam c₁ c₂ (1 : Lin E) = 0 := by
  simp [mooneyRivlinPiola, neoHookeanPiola, svkPiola, greenLagrange, rightCG, det_one]

/-- **Consistency with linear elasticity**: `d/dt P(I + tH)|₀ = λ' (tr H) I + 2μ' sym H` with
`λ' = λ + 4c₂`, `μ' = 2c₁ + 2c₂(d - 2)`. [Ciarlet1988], §4.10. -/
theorem mooneyRivlin_linearization (H : Lin E) :
    HasDerivAt (fun t : ℝ => mooneyRivlinPiola lam c₁ c₂ (1 + t • H))
      (Lin4.isotropic (lam + 4 * c₂) (2 * c₁ + 2 * c₂ * ((finrank ℝ E : ℝ) - 2)) H) 0 := by
  have := (neoHookean_linearization lam (mooneyRivlinKappa (E := E) c₁ c₂) H).add
    (svk_linearization (4 * c₂) (-2 * c₂) H)
  refine this.congr_deriv ?_
  simp only [Lin4.isotropic_apply, mooneyRivlinKappa]
  module

end Lin

end ContinuumMechanics
