import ContinuumMechanics.Constitutive.Hyperelastic
import ContinuumMechanics.Constitutive.LinearIsotropic
import ContinuumMechanics.Kinematics.Infinitesimal

/-!
# The Saint Venant–Kirchhoff material

The **Saint Venant–Kirchhoff** stored energy is
`W(F) = (λ/2) (tr E)² + μ E : E` with `E = ½ (FᵀF - I)` the Green–Lagrange strain
([Ciarlet1988], §4.4). Its stresses are

* `S = λ (tr E) I + 2μ E = ℂ E` (second Piola–Kirchhoff), and
* `P = F S` (first Piola–Kirchhoff),

and at small strain it reduces to linear isotropic elasticity: `D P(I)[H] = ℂ H`.

## Main results

* `Lin.hasFDerivAt_greenLagrange`: `D E(F)[H] = sym (Fᵀ H)` (from the exact expansion
  `E(F + H) = E(F) + sym(FᵀH) + ½ HᵀH`).
* `Lin.svk_isPiolaOf`: `P = F ℂ E(F)` is the first Piola–Kirchhoff stress of `W`.
* `Lin.svk_linearization`: `d/dt P(I + tH)|_{t=0} = ℂ H`.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §4.4.
-/

open Module Asymptotics Filter Topology
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- `sym` as a continuous linear map. -/
noncomputable def symCLM : Lin E →L[ℝ] Lin E := LinearMap.toContinuousLinearMap sym

@[simp] theorem symCLM_apply (A : Lin E) : symCLM A = sym A := rfl

/-- Exact expansion: `E(F + H) = E(F) + sym(Fᵀ H) + ½ Hᵀ H`. -/
theorem greenLagrange_add (F H : Lin E) :
    greenLagrange (F + H) = greenLagrange F + sym (Fᵀ * H) + (2⁻¹ : ℝ) • (Hᵀ * H) := by
  rw [greenLagrange, greenLagrange, rightCG, rightCG, transpose_add, sym_apply, transpose_mul,
    transpose_transpose]
  noncomm_ring
  module

/-- **Derivative of the Green–Lagrange strain**: `D E(F)[H] = sym(Fᵀ H)`. -/
theorem hasFDerivAt_greenLagrange (F : Lin E) :
    HasFDerivAt greenLagrange (symCLM.comp (ContinuousLinearMap.mul ℝ (Lin E) Fᵀ)) F := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e : ∀ H : Lin E, greenLagrange (F + H) - greenLagrange F -
      (symCLM.comp (ContinuousLinearMap.mul ℝ (Lin E) Fᵀ)) H = (2⁻¹ : ℝ) • (Hᵀ * H) := by
    intro H
    rw [greenLagrange_add]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.mul_apply',
      symCLM_apply]
    abel
  simp only [e]
  refine IsBigO.trans_isLittleO (g := fun H : Lin E => ‖H‖ ^ 2) ?_ ?_
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun H => ?_)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg (by positivity), one_mul]
    calc 2⁻¹ * ‖Hᵀ * H‖ ≤ 1 * (‖Hᵀ‖ * ‖H‖) := by
          gcongr
          · norm_num
          · exact norm_mul_le _ _
      _ = ‖H‖ ^ 2 := by rw [transpose_eq_adjoint, LinearIsometryEquiv.norm_map, one_mul, sq]
  · simpa using (isLittleO_norm_pow_id (E' := Lin E) one_lt_two)

/-! ### The Saint Venant–Kirchhoff energy -/

variable (lam mu : ℝ)

/-- The SVK energy as a function of the strain: `Ŵ(E) = (λ/2) (tr E)² + μ E : E`. -/
noncomputable def svkStrainEnergy (Eg : Lin E) : ℝ := lam / 2 * tr Eg ^ 2 + mu * (Eg ⊡ Eg)

/-- The **Saint Venant–Kirchhoff stored energy** `W(F) = Ŵ(E(F))`. [Ciarlet1988], §4.4. -/
noncomputable def svkEnergy (F : Lin E) : ℝ := svkStrainEnergy lam mu (greenLagrange F)

/-- Derivative of the strain energy: `DŴ(E)[H] = ℂE : H` for symmetric `E`. -/
theorem hasFDerivAt_svkStrainEnergy {Eg : Lin E} (hEg : Eg ∈ Sym E) :
    HasFDerivAt (svkStrainEnergy lam mu) (dcontrCLM (Lin4.isotropic lam mu Eg)) Eg := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e : ∀ H : Lin E, svkStrainEnergy lam mu (Eg + H) - svkStrainEnergy lam mu Eg -
      dcontrCLM (Lin4.isotropic lam mu Eg) H = lam / 2 * tr H ^ 2 + mu * (H ⊡ H) := by
    intro H
    simp only [svkStrainEnergy, dcontrCLM_apply, Lin4.isotropic_apply, sym_eq_self_of_mem hEg,
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, one_dcontr, smul_eq_mul,
      dcontr_comm H Eg]
    ring
  simp only [e]
  -- `|H : H| ≤ d ‖H‖²` and `|tr H| ≤ d ‖H‖`
  set d : ℝ := (finrank ℝ E : ℝ)
  let b := stdOrthonormalBasis ℝ E
  have hHH : ∀ H : Lin E, |H ⊡ H| ≤ d * ‖H‖ ^ 2 := fun H => by
    rw [abs_of_nonneg (dcontr_self_nonneg H), dcontr_self_eq_sum b]
    calc ∑ i, ‖H (b i)‖ ^ 2 ≤ ∑ _i : Fin (finrank ℝ E), ‖H‖ ^ 2 := by
          gcongr with i
          calc ‖H (b i)‖ ≤ ‖H‖ * ‖b i‖ := H.le_opNorm _
            _ = ‖H‖ := by rw [b.orthonormal.1, mul_one]
      _ = d * ‖H‖ ^ 2 := by simp [d]
  have htr : ∀ H : Lin E, |tr H| ≤ d * ‖H‖ := fun H => by
    rw [tr_eq_sum_inner b]
    calc |∑ i, ⟪b i, H (b i)⟫_ℝ| ≤ ∑ i, |⟪b i, H (b i)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (finrank ℝ E), ‖H‖ := by
          gcongr with i
          calc |⟪b i, H (b i)⟫_ℝ| ≤ ‖b i‖ * ‖H (b i)‖ := abs_real_inner_le_norm _ _
            _ = ‖H (b i)‖ := by rw [b.orthonormal.1 i, one_mul]
            _ ≤ ‖H‖ * ‖b i‖ := H.le_opNorm _
            _ = ‖H‖ := by rw [b.orthonormal.1 i, mul_one]
      _ = d * ‖H‖ := by simp [d]
  refine IsBigO.trans_isLittleO (g := fun H : Lin E => ‖H‖ ^ 2) ?_
    (by simpa using (isLittleO_norm_pow_id (E' := Lin E) one_lt_two))
  refine IsBigO.of_bound (|lam| / 2 * d ^ 2 + |mu| * d) (Eventually.of_forall fun H => ?_)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  calc |lam / 2 * tr H ^ 2 + mu * (H ⊡ H)| ≤ |lam / 2 * tr H ^ 2| + |mu * (H ⊡ H)| :=
        abs_add_le _ _
    _ = |lam| / 2 * |tr H| ^ 2 + |mu| * |H ⊡ H| := by
        rw [abs_mul, abs_mul, abs_div, abs_pow, abs_two]
    _ ≤ |lam| / 2 * (d * ‖H‖) ^ 2 + |mu| * (d * ‖H‖ ^ 2) := by
        gcongr
        · exact htr H
        · exact hHH H
    _ = (|lam| / 2 * d ^ 2 + |mu| * d) * ‖H‖ ^ 2 := by ring

/-- The SVK first Piola–Kirchhoff stress `P = F ℂ E(F)`. -/
noncomputable def svkPiola (F : Lin E) : Lin E := F * Lin4.isotropic lam mu (greenLagrange F)

/-- **SVK stress**: `P = F ℂ E(F)` is the first Piola–Kirchhoff stress of the SVK energy
(equivalently `S = ℂ E = λ (tr E) I + 2μ E`). [Ciarlet1988], §4.4. -/
theorem svk_isPiolaOf (F : Lin E) : IsPiolaOf (svkEnergy lam mu) (svkPiola lam mu F) F := by
  have hS := (Lin4.isotropic_hasMinorSymm lam mu).1 (greenLagrange F)
  have := (hasFDerivAt_svkStrainEnergy lam mu (greenLagrange_mem_sym F)).comp F
    (hasFDerivAt_greenLagrange F)
  refine (this.congr_fderiv ?_ : HasFDerivAt (svkEnergy lam mu) _ F)
  ext H
  simp only [dcontrCLM_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, symCLM_apply,
    ContinuousLinearMap.mul_apply']
  rw [← dcontr_sym_of_mem_sym hS, svkPiola, mul_dcontr_left]

/-- **Consistency with linear elasticity**: `d/dt P(I + tH)|_{t=0} = ℂ H`. [Ciarlet1988], §6.2. -/
theorem svk_linearization (H : Lin E) :
    HasDerivAt (fun t : ℝ => svkPiola lam mu (1 + t • H)) (Lin4.isotropic lam mu H) 0 := by
  set C : Lin4 E := Lin4.isotropic lam mu
  -- `P(I + tH) = t ℂ(sym H) + t² (H ℂ(sym H) + ½ ℂ(HᵀH)) + t³ ½ H ℂ(HᵀH)`
  have e : (fun t : ℝ => svkPiola lam mu (1 + t • H)) = fun t =>
      t • C (sym H) + t ^ 2 • (H * C (sym H) + (2⁻¹ : ℝ) • C (Hᵀ * H)) +
        t ^ 3 • ((2⁻¹ : ℝ) • (H * C (Hᵀ * H))) := by
    ext1 t
    simp only [svkPiola, greenLagrange_one_add, map_smul, transpose_smul,
      map_add, add_mul, one_mul, smul_mul_assoc, mul_add, mul_smul_comm, C]
    module
  rw [e]
  have h1 := (hasDerivAt_id (0 : ℝ)).smul_const (C (sym H))
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const (H * C (sym H) + (2⁻¹ : ℝ) • C (Hᵀ * H))
  have h3 := (hasDerivAt_pow 3 (0 : ℝ)).smul_const ((2⁻¹ : ℝ) • (H * C (Hᵀ * H)))
  convert (h1.add h2).add h3 using 1
  · ext t; simp
  · have : C (sym H) = C H := (Lin4.isotropic_hasMinorSymm lam mu).apply_sym H
    simp [this]

end Lin

end ContinuumMechanics
