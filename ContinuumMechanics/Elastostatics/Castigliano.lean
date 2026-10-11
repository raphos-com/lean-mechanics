import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ContinuumMechanics.Beams.EulerBernoulli.Solutions

/-!
# Castigliano's theorems and the unit-load method

A discretised (or finite-dimensional) **linear elastic structure** has generalised displacements
`u : ι → ℝ`, conjugate generalised forces `f : ι → ℝ` and a symmetric invertible **stiffness
matrix** `K`, with equilibrium `K u = f`. The **flexibility matrix** is `F = K⁻¹`, so `u = F f`.
The **strain energy** and the **complementary energy** are the quadratic forms

`U(u) = ½ uᵀ K u`,  `U*(f) = ½ fᵀ F f`.

**Castigliano's first theorem** says that the gradient of `U` is the force, `∂U/∂uᵢ = fᵢ`; the
**second theorem** says that the gradient of `U*` is the displacement, `∂U*/∂fᵢ = uᵢ`
([Castigliano1879]; [Langhaar1962], §§4.6–4.9; [TimoshenkoGere1997], §11.9).
The **unit-load (dummy-load) method** computes the displacement component along `d` as the
virtual work of a unit load: `d · u = (F d) · f = fᵀ F d`.

For a statically determinate truss the bar forces are linear in the loads, `N = B f` (`B` the
force-transformation matrix), each bar has flexibility `Lₑ / (Eₑ Aₑ)`, the elongations are
`eₑ = Nₑ Lₑ / (Eₑ Aₑ)`, and by virtual work the node displacements are `u = Bᵀ e`. Hence
`F = Bᵀ diag(L / EA) B`, and the unit-load formula becomes `δ = Σₑ Nₑ nₑ Lₑ / (Eₑ Aₑ)`, with `n`
the bar forces due to a unit load.

For a cantilever with tip load `P` the bending moment is `M(x) = P (L - x)`, the complementary
energy is `U* = ∫₀ᴸ M² / 2EI = P²L³ / 6EI`, and `∂U*/∂P = PL³ / 3EI` is the tip deflection
`EBBeam.cantileverTip_tip`.

## Main results

* `hasFDerivAt_quadEnergy`: the derivative of `v ↦ ½ vᵀ A v` (`A` symmetric) is `h ↦ (A v) · h`.
* `castigliano_first`, `castigliano_first_partial`: `∇U(u) = K u = f`, `∂U/∂uᵢ = fᵢ`.
* `castigliano_second`, `castigliano_second_partial`: `∇U*(f) = F f = u`, `∂U*/∂fᵢ = uᵢ`.
* `clapeyron_strain`, `clapeyron_complementary`: `U(u) = U*(f) = ½ f · u` at equilibrium.
* `maxwell_betti`: `f₁ · u₂ = f₂ · u₁`; `flexibility_symm`: `F_{ij} = F_{ji}`.
* `unit_load`: `d · u = (F d) · f`.
* `trussFlexibility_mulVec`, `truss_unit_load`: `δ = Σₑ Nₑ nₑ Lₑ / (Eₑ Aₑ)` for a statically
  determinate truss; `truss_castigliano_second`; `seriesBars_deflection` (example).
* `cantileverComplementaryEnergy_eq`: `U* = P²L³ / 6EI`; `cantilever_castigliano`:
  `dU*/dP = PL³ / 3EI = w(L)`; `cantilever_unit_load`: `∫₀ᴸ M m / EI = PL³ / 3EI`.

## References

* [Castigliano1879] A. Castigliano, *Théorie de l'équilibre des systèmes élastiques et ses
  applications* (1879).
* [Langhaar1962] H. L. Langhaar, *Energy Methods in Applied Mechanics*, Ch. 4.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, Ch. 11.
-/

open Matrix

namespace ContinuumMechanics.Castigliano

variable {ι : Type*} [Fintype ι]

/-! ### Quadratic energies and their derivatives -/

/-- The linear functional `h ↦ g · h`, as a continuous linear map. -/
noncomputable def dotCLM (g : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => g ⬝ᵥ h
      map_add' := dotProduct_add g
      map_smul' := fun c h => by simp [dotProduct_smul] }

/-- `dotCLM g h = g · h`. -/
@[simp]
theorem dotCLM_apply (g h : ι → ℝ) : dotCLM g h = g ⬝ᵥ h := rfl

/-- The quadratic energy `½ vᵀ A v` of a matrix `A`. -/
noncomputable def quadEnergy (A : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := 2⁻¹ * (v ⬝ᵥ (A *ᵥ v))

/-- Expansion along a line: `Q(v + t w) = Q(v) + t (A v) · w + t² Q(w)` for symmetric `A`. -/
theorem quadEnergy_add_smul {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℝ) (t : ℝ) :
    quadEnergy A (v + t • w) =
      quadEnergy A v + t * ((A *ᵥ v) ⬝ᵥ w) + t ^ 2 * quadEnergy A w := by
  have h1 : v ⬝ᵥ (A *ᵥ w) = (A *ᵥ v) ⬝ᵥ w := by
    have h : v ᵥ* A = A *ᵥ v := by rw [← vecMul_transpose, hA]
    rw [dotProduct_mulVec, h]
  have h2 : w ⬝ᵥ (A *ᵥ v) = (A *ᵥ v) ⬝ᵥ w := dotProduct_comm _ _
  simp only [quadEnergy, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, h1, h2]
  ring

/-- Directional derivative of a quadratic energy: `d/dt Q(v + t w)|₀ = (A v) · w`. -/
theorem hasDerivAt_quadEnergy_line {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℝ) :
    HasDerivAt (fun t : ℝ => quadEnergy A (v + t • w)) ((A *ᵥ v) ⬝ᵥ w) 0 := by
  simp only [quadEnergy_add_smul hA]
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const ((A *ᵥ v) ⬝ᵥ w)).const_add
    (quadEnergy A v)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (quadEnergy A w))
  convert h using 1
  · funext t; simp
  · simp

/-- A quadratic energy is differentiable. -/
theorem differentiable_quadEnergy (A : Matrix ι ι ℝ) : Differentiable ℝ (quadEnergy A) := by
  unfold quadEnergy
  simp only [dotProduct, mulVec]
  fun_prop

/-- **Gradient of a quadratic energy**: for symmetric `A`, the Fréchet derivative of
`v ↦ ½ vᵀ A v` at `v` is `h ↦ (A v) · h`. -/
theorem hasFDerivAt_quadEnergy {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v : ι → ℝ) :
    HasFDerivAt (quadEnergy A) (dotCLM (A *ᵥ v)) v := by
  have hd := (differentiable_quadEnergy A v).hasFDerivAt
  convert hd using 1
  refine ContinuousLinearMap.ext fun w => ?_
  have hline : HasDerivAt (fun t : ℝ => v + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have h2 : HasDerivAt (fun t : ℝ => quadEnergy A (v + t • w)) (fderiv ℝ (quadEnergy A) v w) 0 := by
    have hd' : HasFDerivAt (quadEnergy A) (fderiv ℝ (quadEnergy A) v) (v + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]; exact hd
    exact hd'.comp_hasDerivAt (0 : ℝ) hline
  exact (hasDerivAt_quadEnergy_line hA v w).unique h2

/-! ### Castigliano's theorems -/

/-- The **strain energy** `U(u) = ½ uᵀ K u` of a structure with stiffness matrix `K`. -/
noncomputable def strainEnergy (K : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := quadEnergy K u

/-- The **complementary energy** `U*(f) = ½ fᵀ F f`, with flexibility matrix `F = K⁻¹`. -/
noncomputable def complementaryEnergy [DecidableEq ι] (K : Matrix ι ι ℝ) (f : ι → ℝ) : ℝ :=
  quadEnergy K⁻¹ f

/-- **Castigliano's first theorem**: for a symmetric stiffness `K` and `K u = f`, the derivative
of the strain energy at `u` is the load: `∇U(u) = f`. -/
theorem castigliano_first {K : Matrix ι ι ℝ} (hK : Kᵀ = K) {u f : ι → ℝ} (hf : K *ᵥ u = f) :
    HasFDerivAt (strainEnergy K) (dotCLM f) u := by
  rw [← hf]; exact hasFDerivAt_quadEnergy hK u

/-- **Castigliano's first theorem**, partial derivatives: `∂U/∂uᵢ = fᵢ`. -/
theorem castigliano_first_partial [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K)
    {u f : ι → ℝ} (hf : K *ᵥ u = f) (i : ι) :
    HasDerivAt (fun t : ℝ => strainEnergy K (u + t • Pi.single i 1)) (f i) 0 := by
  have h := hasDerivAt_quadEnergy_line hK u (Pi.single i 1)
  rwa [dotProduct_single_one, hf] at h

/-- The **flexibility matrix** of a symmetric stiffness matrix is symmetric. -/
theorem flexibility_symm [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K) : K⁻¹ᵀ = K⁻¹ := by
  rw [transpose_nonsing_inv, hK]

/-- At equilibrium the displacement is given by the flexibility: `K u = f ⟹ u = F f`. -/
theorem displacement_eq_flexibility [DecidableEq ι] {K : Matrix ι ι ℝ} (hdet : IsUnit K.det)
    {u f : ι → ℝ} (hf : K *ᵥ u = f) : K⁻¹ *ᵥ f = u := by
  rw [← hf, mulVec_mulVec, nonsing_inv_mul K hdet, one_mulVec]

/-- **Castigliano's second theorem**: for a symmetric invertible stiffness and `K u = f`, the
derivative of the complementary energy at `f` is the displacement: `∇U*(f) = F f = u`. -/
theorem castigliano_second [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K) (hdet : IsUnit K.det)
    {u f : ι → ℝ} (hf : K *ᵥ u = f) :
    HasFDerivAt (complementaryEnergy K) (dotCLM u) f := by
  rw [← displacement_eq_flexibility hdet hf]
  exact hasFDerivAt_quadEnergy (flexibility_symm hK) f

/-- **Castigliano's second theorem**, partial derivatives: `∂U*/∂fᵢ = uᵢ`. -/
theorem castigliano_second_partial [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K)
    (hdet : IsUnit K.det) {u f : ι → ℝ} (hf : K *ᵥ u = f) (i : ι) :
    HasDerivAt (fun t : ℝ => complementaryEnergy K (f + t • Pi.single i 1)) (u i) 0 := by
  have h := hasDerivAt_quadEnergy_line (flexibility_symm hK) f (Pi.single i 1)
  rwa [dotProduct_single_one, displacement_eq_flexibility hdet hf] at h

/-- **Clapeyron's theorem** (strain energy): `U(u) = ½ f · u` at equilibrium. -/
theorem clapeyron_strain {K : Matrix ι ι ℝ} {u f : ι → ℝ} (hf : K *ᵥ u = f) :
    strainEnergy K u = 2⁻¹ * (f ⬝ᵥ u) := by
  rw [strainEnergy, quadEnergy, hf, dotProduct_comm]

/-- **Clapeyron's theorem** (complementary energy): `U*(f) = ½ f · u = U(u)` at equilibrium. -/
theorem clapeyron_complementary [DecidableEq ι] {K : Matrix ι ι ℝ} (hdet : IsUnit K.det)
    {u f : ι → ℝ} (hf : K *ᵥ u = f) :
    complementaryEnergy K f = 2⁻¹ * (f ⬝ᵥ u) ∧ complementaryEnergy K f = strainEnergy K u := by
  have h : complementaryEnergy K f = 2⁻¹ * (f ⬝ᵥ u) := by
    rw [complementaryEnergy, quadEnergy, displacement_eq_flexibility hdet hf]
  exact ⟨h, h.trans (clapeyron_strain hf).symm⟩

/-- **Maxwell–Betti reciprocity**: for a symmetric stiffness, the work of the first load system
on the second displacement equals the work of the second on the first: `f₁ · u₂ = f₂ · u₁`. -/
theorem maxwell_betti {K : Matrix ι ι ℝ} (hK : Kᵀ = K) {u₁ u₂ f₁ f₂ : ι → ℝ}
    (h₁ : K *ᵥ u₁ = f₁) (h₂ : K *ᵥ u₂ = f₂) : f₁ ⬝ᵥ u₂ = f₂ ⬝ᵥ u₁ := by
  rw [← h₁, ← h₂, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hK, dotProduct_comm]

/-- **Maxwell's reciprocal displacements**: the flexibility coefficients are symmetric,
`F_{ij} = F_{ji}` (the displacement at `i` due to a unit load at `j` equals the displacement at
`j` due to a unit load at `i`). -/
theorem maxwell_reciprocal [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K) (i j : ι) :
    K⁻¹ i j = K⁻¹ j i := by
  conv_rhs => rw [← flexibility_symm hK]
  rfl

/-! ### The unit-load method -/

/-- **Unit-load (dummy-load) method**: the displacement component along `d` equals the work of
the actual load `f` on the displacement `F d` produced by the dummy load `d`:
`d · u = (F d) · f = fᵀ F d`. -/
theorem unit_load [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : Kᵀ = K) (hdet : IsUnit K.det)
    {u f : ι → ℝ} (hf : K *ᵥ u = f) (d : ι → ℝ) :
    d ⬝ᵥ u = (K⁻¹ *ᵥ d) ⬝ᵥ f ∧ d ⬝ᵥ u = f ⬝ᵥ (K⁻¹ *ᵥ d) := by
  have hd : K *ᵥ (K⁻¹ *ᵥ d) = d := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdet, one_mulVec]
  have h := maxwell_betti hK hf hd
  exact ⟨h.symm.trans (dotProduct_comm _ _), h.symm⟩

/-! ### Statically determinate trusses -/

section Truss

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **flexibility matrix** `F = Bᵀ diag(c) B` of a statically determinate truss with
force-transformation matrix `B` (bar forces `N = B f`) and bar flexibilities `cₑ = Lₑ / (Eₑ Aₑ)`.
-/
def trussFlexibility (B : Matrix m ι ℝ) (c : m → ℝ) : Matrix ι ι ℝ := Bᵀ * diagonal c * B

/-- The node displacements of a determinate truss by virtual work: bar elongations
`eₑ = cₑ Nₑ` with `N = B f`, and `u = Bᵀ e`. -/
def trussDisplacement (B : Matrix m ι ℝ) (c : m → ℝ) (f : ι → ℝ) : ι → ℝ :=
  Bᵀ *ᵥ (c * (B *ᵥ f))

omit [Fintype ι] in
/-- The truss flexibility matrix is symmetric. -/
theorem trussFlexibility_transpose (B : Matrix m ι ℝ) (c : m → ℝ) :
    (trussFlexibility B c)ᵀ = trussFlexibility B c := by
  simp [trussFlexibility, transpose_mul, Matrix.mul_assoc]

/-- The virtual-work displacement is the flexibility applied to the load: `u = F f`. -/
theorem trussFlexibility_mulVec (B : Matrix m ι ℝ) (c : m → ℝ) (f : ι → ℝ) :
    trussFlexibility B c *ᵥ f = trussDisplacement B c f := by
  rw [trussFlexibility, trussDisplacement, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  funext e
  simp [mulVec_diagonal]

/-- **Unit-load method for trusses**: the displacement along `d` is
`δ = d · F f = Σₑ Nₑ nₑ cₑ`, with `N = B f` the bar forces under the load and `n = B d` the bar
forces under the unit load `d`. -/
theorem truss_unit_load_flex (B : Matrix m ι ℝ) (c : m → ℝ) (f d : ι → ℝ) :
    d ⬝ᵥ (trussFlexibility B c *ᵥ f) = ∑ e, (B *ᵥ f) e * (B *ᵥ d) e * c e := by
  rw [trussFlexibility_mulVec, trussDisplacement, dotProduct_mulVec, vecMul_transpose,
    dotProduct_comm]
  simp only [dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

omit [DecidableEq m] in
/-- **Unit-load formula for a statically determinate truss**:
`δ = Σₑ Nₑ nₑ Lₑ / (Eₑ Aₑ)`, with `N = B f`, `n = B d`. [TimoshenkoGere1997], §11.9. -/
theorem truss_unit_load (B : Matrix m ι ℝ) (L E A : m → ℝ) (f d : ι → ℝ) :
    d ⬝ᵥ trussDisplacement B (fun e => L e / (E e * A e)) f =
      ∑ e, (B *ᵥ f) e * (B *ᵥ d) e * L e / (E e * A e) := by
  classical
  rw [← trussFlexibility_mulVec, truss_unit_load_flex]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The complementary energy of a determinate truss: `½ fᵀ F f = Σₑ Nₑ² cₑ / 2`. -/
theorem truss_quadEnergy (B : Matrix m ι ℝ) (c : m → ℝ) (f : ι → ℝ) :
    quadEnergy (trussFlexibility B c) f = ∑ e, (B *ᵥ f) e ^ 2 * c e / 2 := by
  rw [quadEnergy, truss_unit_load_flex, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- **Castigliano's second theorem for a determinate truss**: the derivative of the
complementary energy `Σₑ Nₑ² cₑ / 2` with respect to the loads is the virtual-work
displacement `Bᵀ (c N)`. -/
theorem truss_castigliano_second (B : Matrix m ι ℝ) (c : m → ℝ) (f : ι → ℝ) :
    HasFDerivAt (quadEnergy (trussFlexibility B c)) (dotCLM (trussDisplacement B c f)) f := by
  rw [← trussFlexibility_mulVec]
  exact hasFDerivAt_quadEnergy (trussFlexibility_transpose B c) f

/-- **Example**: two bars in series, loaded by `P` at the free end: both bar forces equal `P`
(`B = [1; 1]`), and the end deflection is `δ = P (L₁ / E₁A₁ + L₂ / E₂A₂)`. -/
theorem seriesBars_deflection (L E A : Fin 2 → ℝ) (P : ℝ) :
    (fun _ => (1 : ℝ)) ⬝ᵥ trussDisplacement (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)
        (fun e => L e / (E e * A e)) (fun _ => P) =
      P * (L 0 / (E 0 * A 0) + L 1 / (E 1 * A 1)) := by
  rw [truss_unit_load]
  simp [Fin.sum_univ_two, mulVec, dotProduct]
  ring

end Truss

/-! ### Cantilever with a tip load -/

section Cantilever

open ContinuumMechanics.Beams

variable (b : EBBeam)

/-- The bending moment `M(x) = P (L - x)` of a cantilever (clamped at `0`) with tip load `P`. -/
def cantileverMoment (P x : ℝ) : ℝ := P * (b.L - x)

/-- The complementary energy `U*(P) = ∫₀ᴸ M(x)² / (2 EI) dx` of a cantilever with tip load `P`.
-/
noncomputable def cantileverComplementaryEnergy (P : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b.L, cantileverMoment b P x ^ 2 / (2 * b.EI)

/-- `∫₀ᴸ (L - x)² dx = L³ / 3`. -/
theorem integral_sub_sq (L : ℝ) : ∫ x in (0 : ℝ)..L, (L - x) ^ 2 = L ^ 3 / 3 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) L, integral_pow]
  simp
  ring

/-- **Complementary energy of a cantilever**: `U*(P) = P² L³ / (6 EI)`. -/
theorem cantileverComplementaryEnergy_eq (P : ℝ) :
    cantileverComplementaryEnergy b P = P ^ 2 * b.L ^ 3 / (6 * b.EI) := by
  have hEI := b.EI_pos.ne'
  have e : (fun x => cantileverMoment b P x ^ 2 / (2 * b.EI)) =
      fun x => P ^ 2 / (2 * b.EI) * (b.L - x) ^ 2 := by
    funext x; rw [cantileverMoment]; ring
  rw [cantileverComplementaryEnergy, e, intervalIntegral.integral_const_mul, integral_sub_sq]
  field_simp
  ring

/-- **Castigliano's second theorem for a cantilever**: `dU*/dP = P L³ / (3 EI)`, which is the
tip deflection `w(L)` of the closed-form solution `EBBeam.cantileverTip`. -/
theorem cantilever_castigliano (P : ℝ) :
    HasDerivAt (cantileverComplementaryEnergy b) (P * b.L ^ 3 / (3 * b.EI)) P ∧
      P * b.L ^ 3 / (3 * b.EI) = b.cantileverTip P b.L := by
  refine ⟨?_, (b.cantileverTip_tip P).symm⟩
  have hEI := b.EI_pos.ne'
  have e : cantileverComplementaryEnergy b = fun Q => Q ^ 2 * (b.L ^ 3 / (6 * b.EI)) := by
    funext Q; rw [cantileverComplementaryEnergy_eq]; ring
  rw [e]
  convert (hasDerivAt_pow 2 P).mul_const (b.L ^ 3 / (6 * b.EI)) using 1
  field_simp
  ring

/-- **Unit-load method for a cantilever**: with the unit-load moment `m(x) = L - x`, the tip
deflection is `∫₀ᴸ M m / EI = P L³ / (3 EI) = w(L)`. -/
theorem cantilever_unit_load (P : ℝ) :
    ∫ x in (0 : ℝ)..b.L, cantileverMoment b P x * cantileverMoment b 1 x / b.EI =
      b.cantileverTip P b.L := by
  have hEI := b.EI_pos.ne'
  have e : (fun x => cantileverMoment b P x * cantileverMoment b 1 x / b.EI) =
      fun x => P / b.EI * (b.L - x) ^ 2 := by
    funext x; rw [cantileverMoment, cantileverMoment]; ring
  rw [e, intervalIntegral.integral_const_mul, integral_sub_sq, b.cantileverTip_tip]
  field_simp

end Cantilever

end ContinuumMechanics.Castigliano
