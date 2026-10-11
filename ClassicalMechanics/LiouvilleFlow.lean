import ClassicalMechanics.Hamiltonian
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Liouville's theorem for nonlinear flows

Let `X : E → E` be a vector field on a finite-dimensional real normed space `E` and let
`Φ : ℝ → E → E` be its **flow**: `Φ 0 = id` and `∂ₜ Φ(t, z) = X(Φ(t, z))`. Mathlib does not (yet)
provide the differentiability of ODE flows with respect to the initial data, so the flow is taken
as data (`PhaseFlow`), together with the assumption that `(t, z) ↦ Φ(t, z)` is of class `C²`.

* **Variational equation** (`PhaseFlow.hasDerivAt_fderiv`): the Jacobian `DΦ(t, z)` satisfies
  `∂ₜ DΦ(t, z) = DX(Φ(t, z)) ∘ DΦ(t, z)`. It is *derived*, not assumed: it follows from the
  symmetry of the second derivative of the `C²` map `(t, z) ↦ Φ(t, z)`.
* **Jacobi's formula without invertibility** (`fderiv_det_apply_comp`):
  `D det(A)[B A] = tr B · det A` for every `A`, from `det((1 + sB) A) = det(1 + sB) det A`.
* **Liouville's formula** (`PhaseFlow.hasDerivAt_det`):
  `∂ₜ det DΦ(t, z) = (div X)(Φ(t, z)) · det DΦ(t, z)`, where `div X = tr DX`.
* **Divergence-free fields** (`PhaseFlow.det_fderiv_eq_one`): if `div X = 0`, then
  `det DΦ(t, z) = 1` for all `t`, `z`.
* **Liouville's theorem** (`PhaseFlow.measure_image`): if moreover `Φ t` is injective on a
  measurable set `A`, then `μ (Φ t '' A) = μ A` for every additive Haar measure `μ` (e.g. Lebesgue
  measure), by the change-of-variables formula.
* **Hamiltonian flows** (`div_hamField`, `hamiltonian_volume`): the divergence `tr DX_H` of the
  Hamiltonian vector field `X_H = (H_p, -H_q)` is `hamDiv H`, which vanishes by `liouville`; hence
  Hamiltonian flows preserve phase-space volume.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §16.
* [Hartman2002] P. Hartman, *Ordinary Differential Equations*, Ch. IV, Cor. 3.1 (Liouville's
  formula) and Ch. V (the variational equation).
-/

open Module Polynomial MeasureTheory

noncomputable section

namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Derivative of the determinant -/

/-- The matrix entry `A ↦ (b-coordinate i of A (b j))` as a continuous linear functional on
`E →L[ℝ] E`. -/
def clmEntry {ι : Type*} (b : Basis ι ℝ E) (i j : ι) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℝ E (b j))

/-- In a basis, the determinant of `A : E →L[ℝ] E` is a polynomial in the matrix entries. -/
theorem clm_det_eq_sum_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (A : E →L[ℝ] E) :
    A.det = ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, clmEntry b (σ i) i A := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [clmEntry, LinearMap.toMatrix_apply]

/-- The determinant is smooth on `E →L[ℝ] E`. -/
theorem contDiff_clm_det : ContDiff ℝ ⊤ (fun A : E →L[ℝ] E => A.det) := by
  classical
  let b := Module.finBasis ℝ E
  rw [show (fun A : E →L[ℝ] E => A.det) = fun A => ∑ σ : Equiv.Perm (Fin (finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, clmEntry b (σ i) i A from funext (clm_det_eq_sum_perm b)]
  fun_prop

/-- The determinant is differentiable at every `A : E →L[ℝ] E`. -/
theorem hasFDerivAt_clm_det (A : E →L[ℝ] E) :
    HasFDerivAt (fun A : E →L[ℝ] E => A.det) (fderiv ℝ (fun A : E →L[ℝ] E => A.det) A) A :=
  (contDiff_clm_det.differentiable (by simp) A).hasFDerivAt

omit [FiniteDimensional ℝ E] in
/-- `det (A B) = det A · det B` for continuous endomorphisms. -/
theorem clm_det_mul (A B : E →L[ℝ] E) : (A * B).det = A.det * B.det := by
  simp [ContinuousLinearMap.det]

/-- **Jacobi's formula at the identity**: `d/ds det(1 + s B)|ₛ₌₀ = tr B`. -/
theorem hasDerivAt_det_one_add_smul (B : E →L[ℝ] E) :
    HasDerivAt (fun s : ℝ => (1 + s • B).det) (LinearMap.trace ℝ E B) 0 := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (B : E →ₗ[ℝ] E)
  let p : ℝ[X] := (Matrix.det (1 + (X : ℝ[X]) • M.map C)).divX.divX
  have e : ∀ s : ℝ, (1 + s • B).det = 1 + LinearMap.trace ℝ E B * s + p.eval s * s ^ 2 := by
    intro s
    have h1 : (1 + s • B).det = Matrix.det (1 + s • M) := by
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b,
        ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add,
        map_smul]
      congr
      exact LinearMap.toMatrix_one b
    rw [h1, Matrix.det_one_add_smul, LinearMap.trace_eq_matrix_trace ℝ b]
  have hp : HasDerivAt (fun s : ℝ => 1 + LinearMap.trace ℝ E B * s + p.eval s * s ^ 2)
      (LinearMap.trace ℝ E B) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      ((hasDerivAt_id' (0 : ℝ)).const_mul (LinearMap.trace ℝ E B))).add
        ((p.hasDerivAt 0).mul (hasDerivAt_pow 2 (0 : ℝ)))
    convert h using 1
    simp
  exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall e)

/-- **Jacobi's formula** in the form needed for flows, valid without invertibility:
`D det(A)[B A] = tr B · det A`. -/
theorem fderiv_det_apply_comp (A B : E →L[ℝ] E) :
    fderiv ℝ (fun A : E →L[ℝ] E => A.det) A (B.comp A) = LinearMap.trace ℝ E B * A.det := by
  have h1 : HasDerivAt (fun s : ℝ => (A + s • B.comp A).det)
      (fderiv ℝ (fun A : E →L[ℝ] E => A.det) A (B.comp A)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => A + s • B.comp A) (B.comp A) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (B.comp A)).const_add A
    exact (hasFDerivAt_clm_det A).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ => (A + s • B.comp A).det)
      (LinearMap.trace ℝ E B * A.det) 0 := by
    have e : (fun s : ℝ => (A + s • B.comp A).det) = fun s => (1 + s • B).det * A.det := by
      funext s
      rw [← clm_det_mul, add_mul, one_mul, smul_mul_assoc, ContinuousLinearMap.mul_def]
    rw [e]
    exact (hasDerivAt_det_one_add_smul B).mul_const A.det
  exact h1.unique h2

/-! ### Flows and the variational equation -/

omit [FiniteDimensional ℝ E] in
/-- **Variational equation** for a `C²` map `F(t, z)` whose time slices are integral curves of
`X`: `∂ₜ D_zF(t, z) = DX(F(t, z)) ∘ D_zF(t, z)`. The proof exchanges `∂ₜ` and `D_z` by the
symmetry of the second derivative. -/
theorem hasDerivAt_fderiv_of_uncurry {F : ℝ × E → E} (hF : ContDiff ℝ 2 F) {X : E → E}
    (hT : ∀ s w, HasDerivAt (fun r => F (r, w)) (X (F (s, w))) s) (t : ℝ) (z : E)
    (hX : DifferentiableAt ℝ X (F (t, z))) :
    HasDerivAt (fun s => fderiv ℝ (fun w => F (s, w)) z)
      ((fderiv ℝ X (F (t, z))).comp (fderiv ℝ (fun w => F (t, w)) z)) t := by
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hG : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (t, z)) (t, z) :=
    (hD (t, z)).hasFDerivAt
  have hs := (hF.contDiffAt (x := (t, z))).isSymmSndFDerivAt (by simp)
  have hJ : ∀ s w, HasFDerivAt (fun w => F (s, w))
      ((fderiv ℝ F (s, w)).comp (ContinuousLinearMap.inr ℝ ℝ E)) w := fun s w =>
    (hF1 (s, w)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right s w)
  have hc : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hTime : ∀ w, fderiv ℝ F (t, w) (1, 0) = X (F (t, w)) := fun w =>
    ((hF1 (t, w)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t w))).unique (hT t w)
  have h1 : HasDerivAt (fun s => (fderiv ℝ F (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      ((fderiv ℝ (fderiv ℝ F) (t, z) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E)) t := by
    have hA : HasDerivAt (fun s => fderiv ℝ F (s, z)) (fderiv ℝ (fderiv ℝ F) (t, z) (1, 0)) t :=
      hG.comp_hasDerivAt t hc
    have h := hA.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E))
    rw [ContinuousLinearMap.comp_zero, add_zero] at h
    exact h
  have e1 : (fun s => fderiv ℝ (fun w => F (s, w)) z) =
      fun s => (fderiv ℝ F (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    funext fun s => (hJ s z).fderiv
  rw [e1]
  convert h1 using 1
  have h3 : HasFDerivAt (fun w => fderiv ℝ F (t, w) (1, 0))
      (((fderiv ℝ (fderiv ℝ F) (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ E)).flip (1, 0)) z := by
    have h := (hG.comp z (hasFDerivAt_prodMk_right t z)).clm_apply
      (hasFDerivAt_const ((1 : ℝ), (0 : E)) z)
    rw [ContinuousLinearMap.comp_zero, zero_add] at h
    exact h
  have e3 : (fun w => fderiv ℝ F (t, w) (1, 0)) = fun w => X (F (t, w)) := funext hTime
  rw [e3] at h3
  have h4 := hX.hasFDerivAt.comp z (hJ t z)
  rw [(hJ t z).fderiv, h4.unique h3]
  ext v
  simp [hs (1, 0) (0, v)]


/-- The **divergence** `div X = tr DX` of a vector field `X : E → E`. -/
def divergence (X : E → E) (z : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ X z : E →ₗ[ℝ] E)

/-- A **flow** of the vector field `X`, with `C²` dependence on `(t, z)`. -/
structure PhaseFlow (X : E → E) where
  /-- The flow map `Φ t z`: the state at time `t` of the motion starting at `z`. -/
  Φ : ℝ → E → E
  /-- Joint `C²` regularity in time and initial data. -/
  contDiff : ContDiff ℝ 2 (fun p : ℝ × E => Φ p.1 p.2)
  /-- Each motion `t ↦ Φ t z` is an integral curve of `X`. -/
  hasDerivAt : ∀ t z, HasDerivAt (fun s => Φ s z) (X (Φ t z)) t
  /-- `Φ 0 = id`. -/
  zero : ∀ z, Φ 0 z = z

namespace PhaseFlow

variable {X : E → E} (φ : PhaseFlow X)

omit [FiniteDimensional ℝ E] in
/-- The spatial Jacobian `DΦ(t, z)` is the `z`-block of the full derivative. -/
theorem hasFDerivAt_Φ (t : ℝ) (z : E) :
    HasFDerivAt (φ.Φ t)
      ((fderiv ℝ (fun p : ℝ × E => φ.Φ p.1 p.2) (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      z :=
  ((φ.contDiff.differentiable (by norm_num)) (t, z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right t z)

omit [FiniteDimensional ℝ E] in
/-- Each time-`t` map `Φ t` is differentiable. -/
theorem differentiable_Φ (t : ℝ) : Differentiable ℝ (φ.Φ t) :=
  fun z => (φ.hasFDerivAt_Φ t z).differentiableAt

omit [FiniteDimensional ℝ E] in
/-- **Variational equation**: `∂ₜ DΦ(t, z) = DX(Φ(t, z)) ∘ DΦ(t, z)`, derived from the symmetry
of the second derivative of the `C²` flow map. -/
theorem hasDerivAt_fderiv (t : ℝ) (z : E) (hX : DifferentiableAt ℝ X (φ.Φ t z)) :
    HasDerivAt (fun s => fderiv ℝ (φ.Φ s) z)
      ((fderiv ℝ X (φ.Φ t z)).comp (fderiv ℝ (φ.Φ t) z)) t :=
  hasDerivAt_fderiv_of_uncurry φ.contDiff φ.hasDerivAt t z hX

/-! ### Liouville's formula and volume preservation -/

/-- **Liouville's formula**: `∂ₜ det DΦ(t, z) = (div X)(Φ(t, z)) · det DΦ(t, z)`. -/
theorem hasDerivAt_det (t : ℝ) (z : E) (hX : DifferentiableAt ℝ X (φ.Φ t z)) :
    HasDerivAt (fun s => (fderiv ℝ (φ.Φ s) z).det)
      (divergence X (φ.Φ t z) * (fderiv ℝ (φ.Φ t) z).det) t := by
  have h := (hasFDerivAt_clm_det (fderiv ℝ (φ.Φ t) z)).comp_hasDerivAt t
    (φ.hasDerivAt_fderiv t z hX)
  rw [fderiv_det_apply_comp] at h
  exact h

/-- For a **divergence-free** field, the Jacobian determinant of the flow is identically `1`. -/
theorem det_fderiv_eq_one (hX : Differentiable ℝ X) (hdiv : ∀ x, divergence X x = 0)
    (t : ℝ) (z : E) : (fderiv ℝ (φ.Φ t) z).det = 1 := by
  have hd : ∀ s, HasDerivAt (fun s => (fderiv ℝ (φ.Φ s) z).det) 0 s := fun s => by
    simpa [hdiv] using φ.hasDerivAt_det s z (hX _)
  have h0 : φ.Φ 0 = id := funext φ.zero
  rw [is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0,
    h0, fderiv_id]
  simp [ContinuousLinearMap.det]

/-- **Liouville's theorem**: the flow of a divergence-free field preserves every additive Haar
measure (e.g. Lebesgue measure) of sets on which `Φ t` is injective. -/
theorem measure_image [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hX : Differentiable ℝ X) (hdiv : ∀ x, divergence X x = 0) (t : ℝ) {A : Set E}
    (hA : MeasurableSet A) (hinj : Set.InjOn (φ.Φ t) A) : μ (φ.Φ t '' A) = μ A := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hA
    (fun x _ => (φ.differentiable_Φ t x).hasFDerivAt.hasFDerivWithinAt) hinj]
  simp [φ.det_fderiv_eq_one hX hdiv t]

end PhaseFlow

/-! ### Hamiltonian flows -/

section Hamiltonian

variable {n : ℕ} {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

/-- The **Hamiltonian vector field** `X_H = (H_p, -H_q)` on phase space `ℝⁿ × ℝⁿ`. -/
def hamField (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => dp H i z, fun i => -dq H i z)

/-- The trace of an endomorphism of `ℝⁿ × ℝⁿ` in the standard basis. -/
theorem trace_prod_pi (f : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ)) :
    LinearMap.trace ℝ _ (f : (Fin n → ℝ) × (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ)) =
      ∑ i, (f (Pi.single i 1, 0)).1 i + ∑ i, (f (0, Pi.single i 1)).2 i := by
  classical
  let b := (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace, Fintype.sum_sum_type]
  simp [b, LinearMap.toMatrix_apply]

variable (hH : ContDiff ℝ 2 H)
include hH

/-- The Hamiltonian vector field of a `C²` Hamiltonian is differentiable. -/
theorem differentiable_hamField : Differentiable ℝ (hamField H) := by
  have hD : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  intro z
  refine DifferentiableAt.prodMk (differentiableAt_pi.2 fun i => ?_)
    (differentiableAt_pi.2 fun i => ?_)
  · exact (hD z).clm_apply (differentiableAt_const _)
  · exact ((hD z).clm_apply (differentiableAt_const _)).neg

/-- The divergence `tr DX_H` of the Hamiltonian vector field is `hamDiv H`. -/
theorem div_hamField (z : (Fin n → ℝ) × (Fin n → ℝ)) : divergence (hamField H) z = hamDiv H z := by
  have hX := (differentiable_hamField hH z).hasFDerivAt
  have hp : ∀ i v, (fderiv ℝ (hamField H) z v).1 i = fderiv ℝ (dp H i) z v := fun i v => by
    have h := ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))).hasFDerivAt.comp z hX
    have h2 : fderiv ℝ (dp H i) z = ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))).comp (fderiv ℝ (hamField H) z) :=
      h.fderiv
    rw [h2]
    rfl
  have hq : ∀ i v, (fderiv ℝ (hamField H) z v).2 i = -fderiv ℝ (dq H i) z v := fun i v => by
    have h := ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))).hasFDerivAt.comp z hX
    have h2 : fderiv ℝ (fun y => -dq H i y) z = ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))).comp (fderiv ℝ (hamField H) z) :=
      h.fderiv
    rw [fderiv_fun_neg] at h2
    rw [show -fderiv ℝ (dq H i) z v = (-fderiv ℝ (dq H i) z) v from rfl, h2]
    rfl
  rw [divergence, trace_prod_pi, hamDiv, Finset.sum_sub_distrib]
  simp only [hp, hq, Finset.sum_neg_distrib]
  ring

/-- The Hamiltonian vector field of a `C²` Hamiltonian is divergence-free. -/
theorem div_hamField_eq_zero (z : (Fin n → ℝ) × (Fin n → ℝ)) : divergence (hamField H) z = 0 := by
  rw [div_hamField hH, liouville hH]

/-- **Liouville's theorem for Hamiltonian flows**: a `C²` flow of a `C²` Hamiltonian has
Jacobian determinant `1`. -/
theorem hamiltonian_det_fderiv (φ : PhaseFlow (hamField H)) (t : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : (fderiv ℝ (φ.Φ t) z).det = 1 :=
  φ.det_fderiv_eq_one (differentiable_hamField hH) (div_hamField_eq_zero hH) t z

/-- **Liouville's theorem for Hamiltonian flows**: the flow preserves phase-space volume. -/
theorem hamiltonian_volume (φ : PhaseFlow (hamField H)) (t : ℝ)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA : MeasurableSet A) (hinj : Set.InjOn (φ.Φ t) A) :
    volume (φ.Φ t '' A) = volume A := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℝ))
    (volume : Measure (Fin n → ℝ))
  exact φ.measure_image volume (differentiable_hamField hH) (div_hamField_eq_zero hH) t hA hinj

end Hamiltonian

end ClassicalMechanics
