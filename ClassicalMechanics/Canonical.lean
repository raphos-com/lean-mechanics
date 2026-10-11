import ClassicalMechanics.LinearHamiltonian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Linear canonical transformations

Phase space is `ℝ²ⁿ = (l ⊕ l → ℝ)`, `z = (q, p)`, with Mathlib's `J = [[0, -I], [I, 0]]`
(`Matrix.J`). A linear change of variables `z = S w` is **canonical** (symplectic) when
`S J Sᵀ = J`, equivalently `Sᵀ J S = J`, i.e. `S ∈ symplecticGroup` ([Arnold1989], §§41, 44;
[Goldstein2002], §9.4; [MeyerHall2009], §2.2).

With the gradient `∇F(z)ᵢ = DF(z) eᵢ` (`grad`), Hamilton's equations `q̇ = H_p`, `ṗ = -H_q` read
`ż = -J ∇H(z)` (with Mathlib's sign of `J`, matching `hamMatrix` in `LinearHamiltonian`), and
the **Poisson bracket** is `{F, G} = F_q · G_p - F_p · G_q = -∇F · J ∇G` (`bracket`).

* **Chain rule** (`grad_comp`): `∇(F ∘ S)(w) = Sᵀ ∇F(S w)`.
* **Invariance of the Poisson bracket** (`bracket_comp`): for symplectic `S` and differentiable
  `F, G`, `{F ∘ S, G ∘ S}(w) = {F, G}(S w)`.
* **Hamiltonian flows go to Hamiltonian flows** (`hasDerivAt_canonical`): if `ż = -J ∇H(z)`
  then `w = S⁻¹ z` solves `ẇ = -J ∇(H ∘ S)(w)`, Hamilton's equations for the transformed
  Hamiltonian `K = H ∘ S`.
* **The symplectic group** (`symplectic_mul`, `symplectic_inv`, `symplectic_det`): canonical
  matrices form a group, of matrices of determinant `1` (Mathlib's
  `SymplecticGroup.det_eq_one`), and preserve the **symplectic form** `ω(u, v) = u · J v`
  (`form_mulVec`).
* **Linear Hamiltonian flows are canonical** (`LinearHamiltonianFlow.mem_symplecticGroup`): the
  time-`t` map `Φ(t)` of a quadratic Hamiltonian lies in the symplectic group, hence preserves
  `ω` and Poisson brackets (`LinearHamiltonianFlow.form_flow`,
  `LinearHamiltonianFlow.bracket_flow`).

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§41, 44.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §9.4.
* [MeyerHall2009] K. R. Meyer, G. R. Hall, D. Offin, *Introduction to Hamiltonian Dynamical
  Systems and the N-Body Problem*, §2.2.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

namespace Canonical

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The **gradient** of a function on phase space: `∇F(z)ᵢ = DF(z) eᵢ`. -/
def grad (F : (l ⊕ l → ℝ) → ℝ) (z : l ⊕ l → ℝ) : l ⊕ l → ℝ :=
  fun i => fderiv ℝ F z (Pi.single i 1)

/-- The **Poisson bracket** `{F, G} = -∇F · J ∇G = F_q · G_p - F_p · G_q`. -/
def bracket (F G : (l ⊕ l → ℝ) → ℝ) (z : l ⊕ l → ℝ) : ℝ :=
  -(grad F z ⬝ᵥ J l ℝ *ᵥ grad G z)

/-- The **symplectic form** `ω(u, v) = u · J v`. -/
def form (u v : l ⊕ l → ℝ) : ℝ := u ⬝ᵥ J l ℝ *ᵥ v

/-- A continuous linear functional is determined by its values on the coordinate vectors. -/
theorem clm_apply_eq_sum (L : (l ⊕ l → ℝ) →L[ℝ] ℝ) (v : l ⊕ l → ℝ) :
    L v = ∑ j, v j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]

/-- The derivative of the linear map `w ↦ S w`. -/
theorem hasFDerivAt_mulVec (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (z : l ⊕ l → ℝ) :
    HasFDerivAt (fun w => S *ᵥ w) (LinearMap.toContinuousLinearMap (Matrix.toLin' S)) z :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' S)).hasFDerivAt

/-- **Chain rule** for gradients: `∇(F ∘ S)(w) = Sᵀ ∇F(S w)`. -/
theorem grad_comp {F : (l ⊕ l → ℝ) → ℝ} (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ)
    (hF : DifferentiableAt ℝ F (S *ᵥ w)) :
    grad (fun v => F (S *ᵥ v)) w = Sᵀ *ᵥ grad F (S *ᵥ w) := by
  have h := hF.hasFDerivAt.comp w (hasFDerivAt_mulVec S w)
  ext i
  change fderiv ℝ (F ∘ fun v => S *ᵥ v) w (Pi.single i 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
  simp only [LinearMap.coe_toContinuousLinearMap', toLin'_apply, mulVec_single_one]
  simp [grad, mulVec, dotProduct]

omit [DecidableEq l] in
/-- `(S u) · v = u · (Sᵀ v)`. -/
theorem mulVec_dotProduct (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : l ⊕ l → ℝ) :
    S *ᵥ u ⬝ᵥ v = u ⬝ᵥ Sᵀ *ᵥ v := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- **Invariance of the Poisson bracket** under a linear canonical transformation:
`{F ∘ S, G ∘ S}(w) = {F, G}(S w)`. -/
theorem bracket_comp {F G : (l ⊕ l → ℝ) → ℝ} {S : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hS : S ∈ symplecticGroup l ℝ) (w : l ⊕ l → ℝ) (hF : DifferentiableAt ℝ F (S *ᵥ w))
    (hG : DifferentiableAt ℝ G (S *ᵥ w)) :
    bracket (fun v => F (S *ᵥ v)) (fun v => G (S *ᵥ v)) w = bracket F G (S *ᵥ w) := by
  rw [SymplecticGroup.mem_iff] at hS
  simp only [bracket, grad_comp S w hF, grad_comp S w hG]
  rw [mulVec_mulVec, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
    hS]

/-- `S⁻¹ J = J Sᵀ` for a symplectic matrix `S`. -/
theorem inv_mul_J {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ) :
    S⁻¹ * J l ℝ = J l ℝ * Sᵀ := by
  have hu := SymplecticGroup.symplectic_det hS
  rw [SymplecticGroup.mem_iff] at hS
  conv_lhs => rw [← hS]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc S⁻¹, nonsing_inv_mul S hu, Matrix.one_mul]

/-- **Canonical transformations map Hamiltonian flows to Hamiltonian flows**: if `z(t)` solves
Hamilton's equations `ż = -J ∇H(z)` and `S` is symplectic, then `w = S⁻¹ z` solves Hamilton's
equations `ẇ = -J ∇K(w)` for the transformed Hamiltonian `K(w) = H(S w)`. -/
theorem hasDerivAt_canonical {H : (l ⊕ l → ℝ) → ℝ} (hH : Differentiable ℝ H)
    {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ) {z : ℝ → l ⊕ l → ℝ}
    (hz : ∀ t, HasDerivAt z (-(J l ℝ *ᵥ grad H (z t))) t) (t : ℝ) :
    HasDerivAt (fun s => S⁻¹ *ᵥ z s)
      (-(J l ℝ *ᵥ grad (fun v => H (S *ᵥ v)) (S⁻¹ *ᵥ z t))) t := by
  have hu := SymplecticGroup.symplectic_det hS
  have h := (hasFDerivAt_mulVec S⁻¹ (z t)).comp_hasDerivAt t (hz t)
  have e : S *ᵥ (S⁻¹ *ᵥ z t) = z t := by rw [mulVec_mulVec, mul_nonsing_inv S hu, one_mulVec]
  have hd : DifferentiableAt ℝ H (S *ᵥ (S⁻¹ *ᵥ z t)) := by rw [e]; exact hH _
  rw [grad_comp S _ hd, e, mulVec_mulVec, ← inv_mul_J hS, ← mulVec_mulVec]
  have h' : HasDerivAt (fun s => S⁻¹ *ᵥ z s) (S⁻¹ *ᵥ -(J l ℝ *ᵥ grad H (z t))) t := h
  rwa [mulVec_neg] at h'

/-- Canonical matrices are closed under products. -/
theorem symplectic_mul {S T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ)
    (hT : T ∈ symplecticGroup l ℝ) : S * T ∈ symplecticGroup l ℝ :=
  Submonoid.mul_mem _ hS hT

/-- The inverse of a canonical matrix is canonical. -/
theorem symplectic_inv {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ) :
    S⁻¹ ∈ symplecticGroup l ℝ := by
  have h := ((⟨S, hS⟩ : symplecticGroup l ℝ)⁻¹).2
  rwa [SymplecticGroup.coe_inv'] at h

/-- Canonical matrices have **determinant one** (Mathlib's `SymplecticGroup.det_eq_one`): linear
canonical transformations preserve phase-space volume and orientation. -/
theorem symplectic_det {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ) :
    S.det = 1 :=
  SymplecticGroup.det_eq_one hS

/-- Canonical matrices **preserve the symplectic form**: `ω(S u, S v) = ω(u, v)`. -/
theorem form_mulVec {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ)
    (u v : l ⊕ l → ℝ) : form (S *ᵥ u) (S *ᵥ v) = form u v := by
  rw [SymplecticGroup.mem_iff'] at hS
  rw [form, form, mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, hS]

/-- Conversely, a matrix preserving the symplectic form is canonical. -/
theorem mem_of_form {S : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : ∀ u v, form (S *ᵥ u) (S *ᵥ v) = form u v) : S ∈ symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [form, mulVec_dotProduct, mulVec_mulVec, ← Matrix.mul_assoc] at hij
  simpa [mulVec_single_one, dotProduct, Pi.single_apply] using hij

end Canonical

namespace LinearHamiltonianFlow

open Canonical

variable {l : Type*} [Fintype l] [DecidableEq l] {S : Matrix (l ⊕ l) (l ⊕ l) ℝ}
  (F : LinearHamiltonianFlow S)

/-- **The flow of a linear Hamiltonian system is canonical**: `Φ(t) ∈ Sp(2n)` for all `t`. -/
theorem mem_symplecticGroup (hS : Sᵀ = S) (t : ℝ) : F.Φ t ∈ symplecticGroup l ℝ :=
  SymplecticGroup.mem_iff'.2 (F.symplectic hS t)

/-- The linear Hamiltonian flow preserves the symplectic form: `ω(Φ u, Φ v) = ω(u, v)`. -/
theorem form_flow (hS : Sᵀ = S) (t : ℝ) (u v : l ⊕ l → ℝ) :
    form (F.Φ t *ᵥ u) (F.Φ t *ᵥ v) = form u v :=
  form_mulVec (F.mem_symplecticGroup hS t) u v

/-- The linear Hamiltonian flow preserves Poisson brackets:
`{A ∘ Φ(t), B ∘ Φ(t)} = {A, B} ∘ Φ(t)`. -/
theorem bracket_flow (hS : Sᵀ = S) (t : ℝ) {A B : (l ⊕ l → ℝ) → ℝ} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) (w : l ⊕ l → ℝ) :
    bracket (fun v => A (F.Φ t *ᵥ v)) (fun v => B (F.Φ t *ᵥ v)) w =
      bracket A B (F.Φ t *ᵥ w) :=
  bracket_comp (F.mem_symplecticGroup hS t) w (hA _) (hB _)

end LinearHamiltonianFlow

end ClassicalMechanics
