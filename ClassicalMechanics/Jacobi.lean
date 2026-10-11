import ClassicalMechanics.Hamiltonian

/-!
# The Jacobi identity for Poisson brackets

For functions `F, G, H` of class `C²` on phase space `ℝⁿ × ℝⁿ`, the Poisson bracket

`{F, G} = Σᵢ ∂F/∂qᵢ ∂G/∂pᵢ - ∂F/∂pᵢ ∂G/∂qᵢ`

satisfies the **Jacobi identity** `{F, {G, H}} + {G, {H, F}} + {H, {F, G}} = 0` (`jacobi`): with
antisymmetry (`pbr_antisymm`) it makes smooth functions on phase space a Lie algebra
([Arnold1989], §40).

The proof differentiates the bracket (`fderiv_pbr`), writes the left-hand side as a double sum
`Σⱼ Σᵢ E j i`, and checks `E j i + E i j = 0` using the symmetry of second derivatives.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §40.
-/

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

local notation "Z" => (Fin n → ℝ) × (Fin n → ℝ)

/-- The coordinate direction of `qᵢ`. -/
def eq (i : Fin n) : (Fin n → ℝ) × (Fin n → ℝ) := (Pi.single i 1, 0)

/-- The coordinate direction of `pᵢ`. -/
def ep (i : Fin n) : (Fin n → ℝ) × (Fin n → ℝ) := (0, Pi.single i 1)

/-- The **Poisson bracket** of two functions on phase space. -/
def pbr (F G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, (fderiv ℝ F z (eq i) * fderiv ℝ G z (ep i) - fderiv ℝ F z (ep i) * fderiv ℝ G z (eq i))

variable {F G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

theorem pbr_antisymm (F G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    pbr F G z = -pbr G F z := by
  simp only [pbr, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Directional derivative of a first derivative: `d/dz (DF(z) w) u = D²F(z)(u, w)`. -/
theorem hasFDerivAt_fderiv_apply (hF : ContDiff ℝ 2 F) (w z : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasFDerivAt (fun y => fderiv ℝ F y w) ((fderiv ℝ (fderiv ℝ F) z).flip w) z := by
  have hD : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h := (hD z).hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  simpa using h

theorem differentiable_fderiv_apply (hF : ContDiff ℝ 2 F) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    Differentiable ℝ (fun y => fderiv ℝ F y w) := fun z =>
  (hasFDerivAt_fderiv_apply hF w z).differentiableAt

/-- The derivative of a Poisson bracket. -/
theorem fderiv_pbr (hG : ContDiff ℝ 2 G) (hH : ContDiff ℝ 2 H) (z u : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (pbr G H) z u = ∑ i,
      (fderiv ℝ (fderiv ℝ G) z u (eq i) * fderiv ℝ H z (ep i) +
        fderiv ℝ G z (eq i) * fderiv ℝ (fderiv ℝ H) z u (ep i) -
      (fderiv ℝ (fderiv ℝ G) z u (ep i) * fderiv ℝ H z (eq i) +
        fderiv ℝ G z (ep i) * fderiv ℝ (fderiv ℝ H) z u (eq i))) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hasFDerivAt_fderiv_apply hG (eq i) z).mul (hasFDerivAt_fderiv_apply hH (ep i) z)).sub
      ((hasFDerivAt_fderiv_apply hG (ep i) z).mul (hasFDerivAt_fderiv_apply hH (eq i) z))
  have h' : HasFDerivAt (pbr G H) _ z := h
  rw [h'.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A double sum of an antisymmetric array vanishes. -/
theorem sum_sum_eq_zero_of_antisymm {E : Fin n → Fin n → ℝ} (h : ∀ i j, E i j + E j i = 0) :
    ∑ i, ∑ j, E i j = 0 := by
  have hs : ∑ i, ∑ j, E i j = ∑ i, ∑ j, E j i := Finset.sum_comm
  have : ∑ i, ∑ j, E i j + ∑ i, ∑ j, E j i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_add_distrib]; simp [h]
  linarith

/-- **Jacobi identity** for Poisson brackets of `C²` functions. -/
theorem jacobi (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hH : ContDiff ℝ 2 H)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    pbr F (pbr G H) z + pbr G (pbr H F) z + pbr H (pbr F G) z = 0 := by
  have sF : ∀ v w, fderiv ℝ (fderiv ℝ F) z v w = fderiv ℝ (fderiv ℝ F) z w v :=
    (hF.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  have sG : ∀ v w, fderiv ℝ (fderiv ℝ G) z v w = fderiv ℝ (fderiv ℝ G) z w v :=
    (hG.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  have sH : ∀ v w, fderiv ℝ (fderiv ℝ H) z v w = fderiv ℝ (fderiv ℝ H) z w v :=
    (hH.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  rw [pbr, pbr, pbr]
  simp only [fderiv_pbr hG hH, fderiv_pbr hH hF, fderiv_pbr hF hG, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_sum_eq_zero_of_antisymm fun i j => ?_
  simp only [sF, sG, sH]
  ring

end ClassicalMechanics
