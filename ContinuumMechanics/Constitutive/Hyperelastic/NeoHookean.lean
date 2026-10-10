import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.Star
import ContinuumMechanics.Constitutive.Hyperelastic.SVK

/-!
# The compressible neo-Hookean material

The **compressible neo-Hookean** stored energy (in dimension `d`, `J = det F`) is
`W(F) = (μ/2)(F : F - d) - μ ln J + (λ/2)(ln J)²`
([Ciarlet1988], §4.10; [Holzapfel2000], §6.5). Its first Piola–Kirchhoff stress is

`P(F) = μ F + (λ ln J - μ) F⁻ᵀ`,

and at small strain it reduces to linear isotropic elasticity with the same Lamé moduli:
`d/dt P(I + tH)|_{t=0} = λ (tr H) I + 2μ sym H = ℂ H`.

## Main results

* `Lin.hasFDerivAt_dcontr_self`: `D(F : F)[H] = 2F : H`.
* `Lin.hasFDerivAt_log_det`: `D(ln J)(F)[H] = F⁻ᵀ : H` for `det F > 0`.
* `Lin.neoHookean_isPiolaOf`: the stress formula.
* `Lin.neoHookean_linearization`: consistency with linear elasticity.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §4.10.
* [Holzapfel2000] G. A. Holzapfel, *Nonlinear Solid Mechanics*, §6.5.
-/

open Module Asymptotics Filter Topology
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- `|H : H| ≤ d ‖H‖²` (Frobenius versus operator norm). -/
theorem abs_dcontr_self_le (H : Lin E) : |H ⊡ H| ≤ finrank ℝ E * ‖H‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  rw [abs_of_nonneg (dcontr_self_nonneg H), dcontr_self_eq_sum b]
  calc ∑ i, ‖H (b i)‖ ^ 2 ≤ ∑ _i : Fin (finrank ℝ E), ‖H‖ ^ 2 := by
        gcongr with i
        calc ‖H (b i)‖ ≤ ‖H‖ * ‖b i‖ := H.le_opNorm _
          _ = ‖H‖ := by rw [b.orthonormal.1, mul_one]
    _ = finrank ℝ E * ‖H‖ ^ 2 := by simp

/-- `D(F : F)[H] = 2F : H`. -/
theorem hasFDerivAt_dcontr_self (F : Lin E) :
    HasFDerivAt (fun G : Lin E => G ⊡ G) (dcontrCLM ((2 : ℝ) • F)) F := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e : ∀ H : Lin E, (F + H) ⊡ (F + H) - F ⊡ F - dcontrCLM ((2 : ℝ) • F) H = H ⊡ H := by
    intro H
    simp only [dcontrCLM_apply, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, dcontr_comm H F]
    ring
  simp only [e]
  refine IsBigO.trans_isLittleO (g := fun H : Lin E => ‖H‖ ^ 2) ?_
    (by simpa using (isLittleO_norm_pow_id (E' := Lin E) one_lt_two))
  refine IsBigO.of_bound (finrank ℝ E) (Eventually.of_forall fun H => ?_)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  exact abs_dcontr_self_le H

/-- `D(ln det)(F)[H] = F⁻ᵀ : H` for `det F > 0`. -/
theorem hasFDerivAt_log_det {F : Lin E} (hF : 0 < F.det) :
    HasFDerivAt (fun G : Lin E => Real.log G.det) (dcontrCLM ((F⁻¹ʳ)ᵀ)) F := by
  have hU : IsUnit F := isUnit_iff_det_ne_zero.mpr hF.ne'
  have := (hasFDerivAt_det hU).log hF.ne'
  refine this.congr_fderiv ?_
  ext H
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    trCLM_apply, ContinuousLinearMap.mul_apply', smul_eq_mul, dcontrCLM_apply, dcontr_apply,
    transpose_transpose]
  field_simp

variable (lam mu : ℝ)

/-- The **compressible neo-Hookean stored energy**
`W(F) = (μ/2)(F : F - d) - μ ln J + (λ/2)(ln J)²`. [Ciarlet1988], §4.10. -/
noncomputable def neoHookeanEnergy (F : Lin E) : ℝ :=
  mu / 2 * (F ⊡ F - finrank ℝ E) - mu * Real.log F.det + lam / 2 * Real.log F.det ^ 2

/-- The neo-Hookean first Piola–Kirchhoff stress `P = μ F + (λ ln J - μ) F⁻ᵀ`. -/
noncomputable def neoHookeanPiola (F : Lin E) : Lin E :=
  mu • F + (lam * Real.log F.det - mu) • (F⁻¹ʳ)ᵀ

/-- **Neo-Hookean stress**: `P = μ F + (λ ln J - μ) F⁻ᵀ` is the first Piola–Kirchhoff stress of
the neo-Hookean energy. [Holzapfel2000], §6.5. -/
theorem neoHookean_isPiolaOf {F : Lin E} (hF : 0 < F.det) :
    IsPiolaOf (neoHookeanEnergy lam mu) (neoHookeanPiola lam mu F) F := by
  have h1 := ((hasFDerivAt_dcontr_self F).sub_const (finrank ℝ E : ℝ)).const_mul (mu / 2)
  have h2 := (hasFDerivAt_log_det hF).const_mul mu
  have h3 := ((hasFDerivAt_log_det hF).pow 2).const_mul (lam / 2)
  have := (h1.sub h2).add h3
  refine (this.congr_fderiv ?_ : HasFDerivAt (neoHookeanEnergy lam mu) _ F)
  ext H
  simp only [add_apply, sub_apply,
    smul_apply, dcontrCLM_apply, smul_eq_mul, neoHookeanPiola, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  ring

/-- **Consistency with linear elasticity**: `d/dt P(I + tH)|_{t=0} = λ (tr H) I + 2μ sym H`.
[Ciarlet1988], §4.10. -/
theorem neoHookean_linearization (H : Lin E) :
    HasDerivAt (fun t : ℝ => neoHookeanPiola lam mu (1 + t • H)) (Lin4.isotropic lam mu H) 0 := by
  -- the curve `G(t) = I + t H`
  have hG : HasDerivAt (fun t : ℝ => (1 : Lin E) + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : Lin E)
  have hG0 : (1 : Lin E) + (0 : ℝ) • H = 1 := by simp
  -- `ln det G(t)`
  have hdet : HasDerivAt (fun t : ℝ => ((1 : Lin E) + t • H).det) (tr H) 0 := by
    exact hasFDerivAt_det_one.comp_hasDerivAt_of_eq (0 : ℝ) hG hG0.symm
  have hlog : HasDerivAt (fun t : ℝ => Real.log ((1 : Lin E) + t • H).det) (tr H) 0 := by
    have := hdet.log (by simp)
    exact this.congr_deriv (by simp)
  -- `G(t)⁻ᵀ`
  have hinv : HasDerivAt (fun t : ℝ => ((1 : Lin E) + t • H)⁻¹ʳ) (-H) 0 := by
    have := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Lin E)ˣ)).comp_hasDerivAt_of_eq (0 : ℝ) hG
      (by simp)
    exact this.congr_deriv (by simp)
  have hinvT : HasDerivAt (fun t : ℝ => (((1 : Lin E) + t • H)⁻¹ʳ)ᵀ) (-Hᵀ) 0 := by
    have := (starL' ℝ : Lin E ≃L[ℝ] Lin E).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv
    exact this.congr_deriv (by simp)
  have hs : HasDerivAt (fun t : ℝ => lam * Real.log ((1 : Lin E) + t • H).det - mu)
      (lam * tr H) 0 := (hlog.const_mul lam).sub_const mu
  have := (hG.const_smul mu).add (hs.smul hinvT)
  refine this.congr_deriv ?_
  · simp only [Lin4.isotropic_apply, sym_apply, zero_smul, add_zero, det_one, Real.log_one,
      mul_zero, zero_sub, Ring.inverse_one, transpose_one, neg_smul, smul_neg, neg_neg]
    module

end Lin

end ContinuumMechanics
