import ContinuumMechanics.Constitutive.Hyperelastic.MooneyRivlin

/-!
# Symmetries and small-strain limit of the classical hyperelastic models

For the Saint Venant–Kirchhoff, compressible neo-Hookean and compressible Mooney–Rivlin stored
energies we prove

* **frame indifference** `W(Q F) = W(F)` and **isotropy** `W(F Q) = W(F)` for rotations `Q`
  ([Gurtin1981], §§29, 33, 37);
* that the reference configuration is **natural** (`W(I) = 0`, `P(I) = 0`) and that the first
  Piola–Kirchhoff stress is Fréchet differentiable at `I` with `DP(I)[H] = λ (tr H) I + 2μ sym H`,
  the linear isotropic law with the same Lamé moduli ([Ciarlet1988], §§4.10, 6.2);
* the **second-order expansion of the energy**
  `W(I + tH) = t² (λ/2 (tr H)² + μ |sym H|²) + o(t²)`, the stored energy of linear isotropic
  elasticity;
* the **uniaxial tension** response `σ = μ (s² - 1/s) e ⊗ e` of an incompressible neo-Hookean
  solid ([Holzapfel2000], §6.3; [Ogden1984], §5.3).

## Main definitions

* `Lin.IsIsotropicEnergy W`: `W(F Q) = W(F)` for every rotation `Q` and `det F > 0`.
* `Lin.uniaxialStretch e s = s e ⊗ e + s^{-1/2} (I - e ⊗ e)`.

## Main results

* `Lin.svk_isFrameIndifferent`, `Lin.neoHookean_isFrameIndifferent`,
  `Lin.mooneyRivlin_isFrameIndifferent` and the `isIsotropicEnergy` counterparts.
* `Lin.svkPiola_hasFDerivAt_one`, `Lin.neoHookeanPiola_hasFDerivAt_one`,
  `Lin.mooneyRivlinPiola_hasFDerivAt_one`: `DP(I) = ℂ(λ, μ)` (Fréchet form).
* `Lin.hasDerivAt_deriv_energy_ray`: `d²/dt² W(I + tH)|₀ = ℂH : H`.
* `Lin.isLittleO_sub_half_mul_sq`: a one-dimensional second-order Taylor estimate.
* `Lin.svkEnergy_expansion`, `Lin.neoHookeanEnergy_expansion`,
  `Lin.mooneyRivlinEnergy_expansion`: the second-order energy expansions.
* `Lin.neoHookean_uniaxial_cauchy`, `Lin.neoHookean_uniaxial_pressure`: uniaxial tension.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§29–37.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §§4.10, 6.2.
* [Holzapfel2000] G. A. Holzapfel, *Nonlinear Solid Mechanics*, §§6.3, 6.5.
* [Ogden1984] R. W. Ogden, *Non-Linear Elastic Deformations*, §5.3.
-/

open Module Asymptotics Filter Topology
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-! ### Invariance lemmas -/

/-- `(Q F) : (Q F) = F : F` for orthogonal `Q`. -/
theorem dcontr_self_orth_mul {Q : Lin E} (hQ : Q ∈ Orth E) (F : Lin E) :
    (Q * F) ⊡ (Q * F) = F ⊡ F := by
  rw [dcontr_apply, dcontr_apply, transpose_mul, mul_assoc, ← mul_assoc Qᵀ,
    transpose_mul_self_of_mem_orth hQ, one_mul]

/-- `(F Q) : (F Q) = F : F` for orthogonal `Q`. -/
theorem dcontr_self_mul_orth {Q : Lin E} (hQ : Q ∈ Orth E) (F : Lin E) :
    (F * Q) ⊡ (F * Q) = F ⊡ F := by
  rw [dcontr_apply, dcontr_apply, transpose_mul, mul_assoc, tr_mul_comm, mul_assoc, mul_assoc,
    mul_transpose_self_of_mem_orth hQ, mul_one]

/-- `tr (Qᵀ A Q) = tr A` for orthogonal `Q`. -/
theorem tr_transpose_mul_mul_orth {Q : Lin E} (hQ : Q ∈ Orth E) (A : Lin E) :
    tr (Qᵀ * A * Q) = tr A := by
  rw [tr_mul_comm, ← mul_assoc, mul_transpose_self_of_mem_orth hQ, one_mul]

/-- `(Qᵀ A Q) : (Qᵀ A Q) = A : A` for orthogonal `Q`. -/
theorem dcontr_self_conj_orth {Q : Lin E} (hQ : Q ∈ Orth E) (A : Lin E) :
    (Qᵀ * A * Q) ⊡ (Qᵀ * A * Q) = A ⊡ A := by
  rw [dcontr_self_mul_orth hQ, dcontr_self_orth_mul (transpose_mem_orth hQ)]

/-- `C(F Q) = Qᵀ C(F) Q`. -/
theorem rightCG_mul_orth (F Q : Lin E) : rightCG (F * Q) = Qᵀ * rightCG F * Q := by
  rw [rightCG, rightCG, transpose_mul]; simp only [mul_assoc]

/-- `E(F Q) = Qᵀ E(F) Q` for orthogonal `Q`. -/
theorem greenLagrange_mul_orth {Q : Lin E} (hQ : Q ∈ Orth E) (F : Lin E) :
    greenLagrange (F * Q) = Qᵀ * greenLagrange F * Q := by
  rw [greenLagrange, greenLagrange, rightCG_mul_orth, mul_smul_comm, smul_mul_assoc, mul_sub,
    sub_mul, mul_one, transpose_mul_self_of_mem_orth hQ]

/-! ### Material symmetry -/

/-- A stored energy is **isotropic** (its symmetry group contains all rotations) if
`W(F Q) = W(F)` for every rotation `Q` and every admissible `F`. [Gurtin1981], §§33, 37. -/
def IsIsotropicEnergy (W : Lin E → ℝ) : Prop :=
  ∀ Q ∈ Orth E, Q.det = 1 → ∀ F : Lin E, 0 < F.det → W (F * Q) = W F

variable (lam mu c₁ c₂ : ℝ)

/-- The SVK energy is invariant under every orthogonal change of observer, `W(Q F) = W(F)`. -/
theorem svkEnergy_orth_mul {Q : Lin E} (hQ : Q ∈ Orth E) (F : Lin E) :
    svkEnergy lam mu (Q * F) = svkEnergy lam mu F := by
  rw [svkEnergy, svkEnergy, greenLagrange_orth_mul F hQ]

/-- The SVK energy is invariant under every orthogonal change of reference, `W(F Q) = W(F)`. -/
theorem svkEnergy_mul_orth {Q : Lin E} (hQ : Q ∈ Orth E) (F : Lin E) :
    svkEnergy lam mu (F * Q) = svkEnergy lam mu F := by
  rw [svkEnergy, svkEnergy, greenLagrange_mul_orth hQ, svkStrainEnergy, svkStrainEnergy,
    tr_transpose_mul_mul_orth hQ, dcontr_self_conj_orth hQ]

/-- `W(Q F) = W(F)` for the neo-Hookean energy and every rotation `Q`. -/
theorem neoHookeanEnergy_rot_mul {Q : Lin E} (hQ : Q ∈ Orth E) (hQdet : Q.det = 1)
    (F : Lin E) : neoHookeanEnergy lam mu (Q * F) = neoHookeanEnergy lam mu F := by
  rw [neoHookeanEnergy, neoHookeanEnergy, dcontr_self_orth_mul hQ, det_mul, hQdet, one_mul]

/-- `W(F Q) = W(F)` for the neo-Hookean energy and every rotation `Q`. -/
theorem neoHookeanEnergy_mul_rot {Q : Lin E} (hQ : Q ∈ Orth E) (hQdet : Q.det = 1)
    (F : Lin E) : neoHookeanEnergy lam mu (F * Q) = neoHookeanEnergy lam mu F := by
  rw [neoHookeanEnergy, neoHookeanEnergy, dcontr_self_mul_orth hQ, det_mul, hQdet, mul_one]

/-- `W(Q F) = W(F)` for the Mooney–Rivlin energy and every rotation `Q`. -/
theorem mooneyRivlinEnergy_rot_mul {Q : Lin E} (hQ : Q ∈ Orth E) (hQdet : Q.det = 1)
    (F : Lin E) : mooneyRivlinEnergy lam c₁ c₂ (Q * F) = mooneyRivlinEnergy lam c₁ c₂ F := by
  rw [mooneyRivlinEnergy_eq, mooneyRivlinEnergy_eq, neoHookeanEnergy_rot_mul _ _ hQ hQdet,
    svkEnergy_orth_mul _ _ hQ]

/-- `W(F Q) = W(F)` for the Mooney–Rivlin energy and every rotation `Q`. -/
theorem mooneyRivlinEnergy_mul_rot {Q : Lin E} (hQ : Q ∈ Orth E) (hQdet : Q.det = 1)
    (F : Lin E) : mooneyRivlinEnergy lam c₁ c₂ (F * Q) = mooneyRivlinEnergy lam c₁ c₂ F := by
  rw [mooneyRivlinEnergy_eq, mooneyRivlinEnergy_eq, neoHookeanEnergy_mul_rot _ _ hQ hQdet,
    svkEnergy_mul_orth _ _ hQ]

/-- The **SVK material is frame-indifferent**. -/
theorem svk_isFrameIndifferent : IsFrameIndifferent (svkEnergy lam mu : Lin E → ℝ) :=
  fun _ hQ _ F _ => svkEnergy_orth_mul lam mu hQ F

/-- The **SVK material is isotropic**. -/
theorem svk_isIsotropicEnergy : IsIsotropicEnergy (svkEnergy lam mu : Lin E → ℝ) :=
  fun _ hQ _ F _ => svkEnergy_mul_orth lam mu hQ F

/-- The **neo-Hookean material is frame-indifferent**. -/
theorem neoHookean_isFrameIndifferent :
    IsFrameIndifferent (neoHookeanEnergy lam mu : Lin E → ℝ) :=
  fun _ hQ hQdet F _ => neoHookeanEnergy_rot_mul lam mu hQ hQdet F

/-- The **neo-Hookean material is isotropic**. -/
theorem neoHookean_isIsotropicEnergy : IsIsotropicEnergy (neoHookeanEnergy lam mu : Lin E → ℝ) :=
  fun _ hQ hQdet F _ => neoHookeanEnergy_mul_rot lam mu hQ hQdet F

/-- The **Mooney–Rivlin material is frame-indifferent**. -/
theorem mooneyRivlin_isFrameIndifferent :
    IsFrameIndifferent (mooneyRivlinEnergy lam c₁ c₂ : Lin E → ℝ) :=
  fun _ hQ hQdet F _ => mooneyRivlinEnergy_rot_mul lam c₁ c₂ hQ hQdet F

/-- The **Mooney–Rivlin material is isotropic**. -/
theorem mooneyRivlin_isIsotropicEnergy :
    IsIsotropicEnergy (mooneyRivlinEnergy lam c₁ c₂ : Lin E → ℝ) :=
  fun _ hQ hQdet F _ => mooneyRivlinEnergy_mul_rot lam c₁ c₂ hQ hQdet F

/-! ### Fréchet linearisation of the stress at the reference configuration -/

/-- The SVK reference configuration is stress free: `P(I) = 0`. -/
theorem svkPiola_one : svkPiola lam mu (1 : Lin E) = 0 := by
  simp [svkPiola, greenLagrange, rightCG]

/-- The neo-Hookean reference configuration is stress free: `P(I) = 0`. -/
theorem neoHookeanPiola_one : neoHookeanPiola lam mu (1 : Lin E) = 0 := by
  simp [neoHookeanPiola, det_one]

/-- **SVK linearisation (Fréchet form)**: the first Piola–Kirchhoff stress is differentiable at
`F = I` with derivative the isotropic elasticity tensor, `DP(I)[H] = λ (tr H) I + 2μ sym H`.
[Ciarlet1988], §6.2. -/
theorem svkPiola_hasFDerivAt_one :
    HasFDerivAt (svkPiola lam mu) (Lin4.isotropic lam mu : Lin4 E) 1 := by
  have hE := (Lin4.isotropic lam mu : Lin4 E).hasFDerivAt.comp (1 : Lin E)
    (hasFDerivAt_greenLagrange (1 : Lin E))
  have := (hasFDerivAt_id (1 : Lin E)).mul' hE
  refine this.congr_fderiv ?_
  ext1 H
  have hS := (Lin4.isotropic_hasMinorSymm lam mu : (Lin4.isotropic lam mu : Lin4 E).HasMinorSymm)
  have h0 : greenLagrange (1 : Lin E) = 0 := by simp [greenLagrange, rightCG]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [h0, map_zero, MulOpposite.op_zero, zero_smul, add_zero, id, one_smul]
  simp only [ContinuousLinearMap.mul_apply', transpose_one, one_mul, symCLM_apply, hS.apply_sym]

/-- **Neo-Hookean linearisation (Fréchet form)**: `DP(I)[H] = λ (tr H) I + 2μ sym H`, the
linear isotropic law with the same Lamé moduli. [Ciarlet1988], §4.10. -/
theorem neoHookeanPiola_hasFDerivAt_one :
    HasFDerivAt (neoHookeanPiola lam mu) (Lin4.isotropic lam mu : Lin4 E) 1 := by
  have hlog := hasFDerivAt_log_det (E := E) (F := 1) (by rw [det_one]; exact one_pos)
  have hinv : HasFDerivAt (fun G : Lin E => G⁻¹ʳ)
      (-(ContinuousLinearMap.mulLeftRight ℝ (Lin E) (1 : Lin E) (1 : Lin E))) 1 := by
    simpa using hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Lin E)ˣ)
  have hinvT := (starL' ℝ : Lin E ≃L[ℝ] Lin E).hasFDerivAt.comp (1 : Lin E) hinv
  have hs := (hlog.const_mul lam).sub_const mu
  have := ((hasFDerivAt_id (1 : Lin E)).const_smul mu).add (hs.smul hinvT)
  refine this.congr_fderiv ?_
  ext1 H
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, det_one, Real.log_one,
    ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.smulRight_apply,
    Ring.inverse_one, transpose_one, dcontrCLM_apply, one_dcontr, mul_one, one_mul, mul_zero,
    zero_sub, Lin4.isotropic_apply, sym_apply, starL'_apply, smul_eq_mul, star_neg]
  module

/-- **Mooney–Rivlin linearisation (Fréchet form)**: `DP(I) = ℂ(λ + 4c₂, 2c₁ + 2c₂(d - 2))`. -/
theorem mooneyRivlinPiola_hasFDerivAt_one :
    HasFDerivAt (mooneyRivlinPiola lam c₁ c₂)
      (Lin4.isotropic (lam + 4 * c₂) (2 * c₁ + 2 * c₂ * ((finrank ℝ E : ℝ) - 2)) : Lin4 E) 1 := by
  have := (neoHookeanPiola_hasFDerivAt_one lam (mooneyRivlinKappa (E := E) c₁ c₂)).add
    (svkPiola_hasFDerivAt_one (E := E) (4 * c₂) (-2 * c₂))
  refine this.congr_fderiv ?_
  ext1 H
  simp only [add_apply, Lin4.isotropic_apply, mooneyRivlinKappa]
  module

/-! ### Second-order expansion of the energy -/

/-- Along the ray `t ↦ F + t H`, a hyperelastic energy has derivative `P : H`. -/
theorem hasDerivAt_energy_ray {W : Lin E → ℝ} {P F H : Lin E} {t : ℝ}
    (h : IsPiolaOf W P (F + t • H)) : HasDerivAt (fun s : ℝ => W (F + s • H)) (P ⊡ H) t := by
  have hG : HasDerivAt (fun s : ℝ => F + s • H) H t := by
    simpa using ((hasDerivAt_id t).smul_const H).const_add F
  exact (show HasFDerivAt W (dcontrCLM P) (F + t • H) from h).comp_hasDerivAt t hG

/-- **Second derivative of the energy along a ray**: if `P` is the stress of `W` near `I` along
`I + tH` and `d/dt P(I + tH)|₀ = ℂH`, then `d²/dt² W(I + tH)|₀ = ℂH : H`. -/
theorem hasDerivAt_deriv_energy_ray {W : Lin E → ℝ} {P : Lin E → Lin E} {H C : Lin E}
    (hP : ∀ᶠ t in 𝓝 (0 : ℝ), IsPiolaOf W (P (1 + t • H)) (1 + t • H))
    (hlin : HasDerivAt (fun t : ℝ => P (1 + t • H)) C 0) :
    HasDerivAt (deriv fun t : ℝ => W (1 + t • H)) (C ⊡ H) 0 := by
  have heq : (deriv fun t : ℝ => W (1 + t • H)) =ᶠ[𝓝 0] fun t => H ⊡ P (1 + t • H) :=
    hP.mono fun t ht => by rw [(hasDerivAt_energy_ray ht).deriv, dcontr_comm]
  have h := (dcontrCLM H).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlin
  simp only [Function.comp_def, dcontrCLM_apply] at h
  rw [dcontr_comm]
  exact h.congr_of_eventuallyEq heq

/-- A second-order Taylor estimate from one-sided data: if `φ(0) = 0`, `φ' = g` near `0`,
`g(0) = 0` and `g'(0) = a`, then `φ(t) = (a/2) t² + o(t²)`. -/
theorem isLittleO_sub_half_mul_sq {φ g : ℝ → ℝ} {a : ℝ} (hφ0 : φ 0 = 0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt φ (g t) t) (hg0 : g 0 = 0) (hg : HasDerivAt g a 0) :
    (fun t => φ t - a / 2 * t ^ 2) =o[𝓝 0] fun t => t ^ 2 := by
  rw [isLittleO_iff]
  intro ε hε
  have hlo := (hasDerivAt_iff_isLittleO.mp hg).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hd.and hlo)
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun t ht => ?_⟩
  set ψ : ℝ → ℝ := fun s => φ s - a / 2 * s ^ 2
  have hsub : Set.uIcc 0 t ⊆ Metric.ball (0 : ℝ) δ := fun s hs => by
    have := Set.abs_sub_left_of_mem_uIcc hs
    simp only [sub_zero] at this
    rw [Real.dist_eq, sub_zero] at ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact this.trans_lt ht
  have hder : ∀ s ∈ Set.uIcc 0 t, HasDerivWithinAt ψ (g s - a * s) (Set.uIcc 0 t) s := by
    intro s hs
    have h1 := (hball (hsub hs)).1
    have h2 := ((hasDerivAt_pow 2 s).const_mul (a / 2))
    refine (h1.sub h2).hasDerivWithinAt.congr_deriv ?_
    push_cast
    ring
  have hbd : ∀ s ∈ Set.uIcc 0 t, ‖g s - a * s‖ ≤ ε * ‖t‖ := by
    intro s hs
    have h := (hball (hsub hs)).2
    simp only [hg0, sub_zero, smul_eq_mul] at h
    have hs' := Set.abs_sub_left_of_mem_uIcc hs
    simp only [sub_zero] at hs'
    calc ‖g s - a * s‖ = ‖g s - s * a‖ := by rw [mul_comm]
      _ ≤ ε * ‖s‖ := h
      _ ≤ ε * ‖t‖ := by gcongr; simpa only [Real.norm_eq_abs] using hs'
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc 0 t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [ψ, hφ0, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero] at this
  calc ‖φ t - a / 2 * t ^ 2‖ ≤ ε * ‖t‖ * ‖t‖ := this
    _ = ε * ‖t ^ 2‖ := by rw [norm_pow]; ring

/-- `ℂH : H = λ (tr H)² + 2μ (sym H : sym H)` for every (not necessarily symmetric) `H`. -/
theorem isotropic_apply_dcontr_self (H : Lin E) :
    Lin4.isotropic lam mu H ⊡ H = lam * tr H ^ 2 + 2 * mu * (sym H ⊡ sym H) := by
  have hS := (Lin4.isotropic_hasMinorSymm lam mu : (Lin4.isotropic lam mu : Lin4 E).HasMinorSymm)
  rw [← hS.apply_sym, dcontr_sym_of_mem_sym (hS.1 _), Lin4.isotropic_dcontr_self lam mu (sym_mem H),
    tr_sym]

/-- **Second-order expansion of a stress-free hyperelastic energy**: if `W(I) = 0`, `P(I) = 0`
and `d/dt P(I + tH)|₀ = ℂ(λ, μ) H`, then
`W(I + tH) = t² (λ/2 (tr H)² + μ |sym H|²) + o(t²)`. -/
theorem energy_ray_expansion {W : Lin E → ℝ} {P : Lin E → Lin E} {H : Lin E} (hW1 : W 1 = 0)
    (hP1 : P 1 = 0) (hP : ∀ᶠ t in 𝓝 (0 : ℝ), IsPiolaOf W (P (1 + t • H)) (1 + t • H))
    (hlin : HasDerivAt (fun t : ℝ => P (1 + t • H)) (Lin4.isotropic lam mu H) 0) :
    (fun t : ℝ => W (1 + t • H) - t ^ 2 * (lam / 2 * tr H ^ 2 + mu * (sym H ⊡ sym H)))
      =o[𝓝 0] fun t => t ^ 2 := by
  have hg : HasDerivAt (fun t : ℝ => P (1 + t • H) ⊡ H) (Lin4.isotropic lam mu H ⊡ H) 0 := by
    have h := (dcontrCLM H).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlin
    simp only [Function.comp_def, dcontrCLM_apply] at h
    simp only [dcontr_comm _ H]
    exact h
  have := isLittleO_sub_half_mul_sq (φ := fun t : ℝ => W (1 + t • H)) (by simpa using hW1)
    (hP.mono fun t ht => hasDerivAt_energy_ray ht) (by simp [hP1]) hg
  refine this.congr_left fun t => ?_
  rw [isotropic_apply_dcontr_self]
  ring

/-- The SVK energy vanishes in the reference configuration. -/
theorem svkEnergy_one : svkEnergy lam mu (1 : Lin E) = 0 := by
  simp [svkEnergy, svkStrainEnergy, greenLagrange, rightCG]

/-- The neo-Hookean energy vanishes in the reference configuration. -/
theorem neoHookeanEnergy_one : neoHookeanEnergy lam mu (1 : Lin E) = 0 := by
  simp [neoHookeanEnergy, tr_one, det_one]

/-- The Mooney–Rivlin energy vanishes in the reference configuration. -/
theorem mooneyRivlinEnergy_one : mooneyRivlinEnergy lam c₁ c₂ (1 : Lin E) = 0 := by
  rw [mooneyRivlinEnergy_eq, neoHookeanEnergy_one, svkEnergy_one, add_zero]

/-- Near `t = 0`, `I + tH` is an admissible deformation gradient. -/
theorem eventually_det_one_add_smul_pos (H : Lin E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < ((1 : Lin E) + t • H).det := by
  have hc : Continuous fun t : ℝ => ((1 : Lin E) + t • H).det :=
    contDiff_det.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  exact (hc.tendsto 0).eventually (lt_mem_nhds (by simp [det_one]))

/-- **SVK energy at small strain**: `W(I + tH) = t² (λ/2 (tr H)² + μ |sym H|²) + o(t²)`, the
energy of linear isotropic elasticity. [Ciarlet1988], §6.2. -/
theorem svkEnergy_expansion (H : Lin E) :
    (fun t : ℝ => svkEnergy lam mu (1 + t • H) -
      t ^ 2 * (lam / 2 * tr H ^ 2 + mu * (sym H ⊡ sym H))) =o[𝓝 0] fun t => t ^ 2 :=
  energy_ray_expansion lam mu (svkEnergy_one lam mu) (svkPiola_one lam mu)
    (Eventually.of_forall fun _ => svk_isPiolaOf lam mu _) (svk_linearization lam mu H)

/-- **Neo-Hookean energy at small strain**: `W(I + tH) = t² (λ/2 (tr H)² + μ |sym H|²) + o(t²)`.
[Ciarlet1988], §4.10. -/
theorem neoHookeanEnergy_expansion (H : Lin E) :
    (fun t : ℝ => neoHookeanEnergy lam mu (1 + t • H) -
      t ^ 2 * (lam / 2 * tr H ^ 2 + mu * (sym H ⊡ sym H))) =o[𝓝 0] fun t => t ^ 2 :=
  energy_ray_expansion lam mu (neoHookeanEnergy_one lam mu) (neoHookeanPiola_one lam mu)
    ((eventually_det_one_add_smul_pos H).mono fun _ ht => neoHookean_isPiolaOf lam mu ht)
    (neoHookean_linearization lam mu H)

/-- **Mooney–Rivlin energy at small strain**, with the effective Lamé moduli
`λ' = λ + 4c₂`, `μ' = 2c₁ + 2c₂(d - 2)`. -/
theorem mooneyRivlinEnergy_expansion (H : Lin E) :
    (fun t : ℝ => mooneyRivlinEnergy lam c₁ c₂ (1 + t • H) -
      t ^ 2 * ((lam + 4 * c₂) / 2 * tr H ^ 2 +
        (2 * c₁ + 2 * c₂ * ((finrank ℝ E : ℝ) - 2)) * (sym H ⊡ sym H)))
      =o[𝓝 0] fun t => t ^ 2 :=
  energy_ray_expansion _ _ (mooneyRivlinEnergy_one lam c₁ c₂) (mooneyRivlin_piola_one lam c₁ c₂)
    ((eventually_det_one_add_smul_pos H).mono fun _ ht => mooneyRivlin_isPiolaOf lam c₁ c₂ ht)
    (mooneyRivlin_linearization lam c₁ c₂ H)

/-! ### Uniaxial tension of the incompressible neo-Hookean material -/

/-- The isochoric **uniaxial stretch** `F = s e ⊗ e + s^{-1/2} (I - e ⊗ e)` along `e`. -/
noncomputable def uniaxialStretch (e : E) (s : ℝ) : Lin E :=
  s • (e ⊗ e) + (Real.sqrt s)⁻¹ • (1 - e ⊗ e)

/-- The left Cauchy–Green tensor of a uniaxial stretch: `B = s² e ⊗ e + s⁻¹ (I - e ⊗ e)`. -/
theorem leftCG_uniaxialStretch {e : E} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) :
    leftCG (uniaxialStretch e s) = s ^ 2 • (e ⊗ e) + s⁻¹ • (1 - e ⊗ e) := by
  have hee : (e ⊗ e) * (e ⊗ e) = e ⊗ e := by
    rw [dyad_mul_dyad, real_inner_self_eq_norm_sq, he, one_pow, one_smul]
  have hsq : (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ = s⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  rw [leftCG, uniaxialStretch, transpose_add, transpose_smul, transpose_smul, star_sub,
    transpose_one, dyad_transpose]
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_sub, sub_mul, hee, one_mul, mul_one,
    sub_self, smul_zero, add_zero, zero_add, hsq]
  module

/-- **Uniaxial tension of an incompressible neo-Hookean solid**: with the Cauchy stress
`σ = -p I + μ B` and the pressure `p = μ / s` fixed by traction-free lateral faces, the stress
is purely axial, `σ = μ (s² - 1/s) e ⊗ e`. [Holzapfel2000], §6.3; [Ogden1984], §5.3. -/
theorem neoHookean_uniaxial_cauchy {e : E} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (mu : ℝ) :
    -(mu / s) • (1 : Lin E) + mu • leftCG (uniaxialStretch e s) =
      (mu * (s ^ 2 - 1 / s)) • (e ⊗ e) := by
  rw [leftCG_uniaxialStretch he hs]
  module

/-- The lateral-traction-free condition **determines the pressure**: if `σ = -p I + μ B` has
`σ v = 0` for some nonzero `v ⊥ e`, then `p = μ / s`. -/
theorem neoHookean_uniaxial_pressure {e v : E} (he : ‖e‖ = 1) (hv : v ≠ 0)
    (hve : ⟪e, v⟫_ℝ = 0) {s : ℝ} (hs : 0 < s) {mu p : ℝ}
    (hσ : (-p • (1 : Lin E) + mu • leftCG (uniaxialStretch e s)) v = 0) : p = mu / s := by
  rw [leftCG_uniaxialStretch he hs] at hσ
  simp only [add_apply, smul_apply, sub_apply, one_apply_eq_self, dyad_apply, hve,
    zero_smul, smul_zero, sub_zero, zero_add, smul_smul, ← add_smul] at hσ
  rcases smul_eq_zero.mp hσ with h | h
  · field_simp at h ⊢
    linarith
  · exact absurd h hv

end Lin

end ContinuumMechanics
