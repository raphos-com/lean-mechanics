import ClassicalMechanics.Vector
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Linear Hamiltonian systems: symplecticity and Liouville's theorem

A quadratic Hamiltonian `H(z) = ½ zᵀ S z` on phase space `z = (q, p) ∈ ℝⁿ ⊕ ℝⁿ`, with `S`
symmetric, generates the linear system `ż = A z` with the **Hamiltonian matrix** `A = -J S`
(`J = [[0, -I], [I, 0]]`, Mathlib's `Matrix.J`), i.e. `q̇ = H_p`, `ṗ = -H_q`
([Arnold1989], §§40–41; [MeyerHall2009], §2.1).

* `hamiltonian_matrix`: `Aᵀ J + J A = 0`.
* **Symplecticity** (`symplectic`): the fundamental matrix `Φ(t)` of `Φ̇ = A Φ`, `Φ(0) = I`, is
  symplectic for all `t`: `Φᵀ J Φ = J`.
* **Liouville's theorem** (`det_flow`): `det Φ(t) = 1`, so the flow preserves phase-space volume
  (and orientation).

Derivatives of matrices are taken entrywise.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§40–41.
* [MeyerHall2009] K. R. Meyer, G. R. Hall, D. Offin, *Introduction to Hamiltonian Dynamical
  Systems and the N-Body Problem*, §2.1.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The Hamiltonian matrix `A = -J S` of the quadratic Hamiltonian `½ zᵀ S z`. -/
def hamMatrix (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := -(J l ℝ * S)

/-- `Aᵀ J + J A = 0` for `A = -J S` with `S` symmetric. -/
theorem hamiltonian_matrix {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S) :
    (hamMatrix S)ᵀ * J l ℝ + J l ℝ * hamMatrix S = 0 := by
  simp only [hamMatrix, transpose_neg, transpose_mul, hS, J_transpose,
    Matrix.mul_neg, neg_neg]
  rw [Matrix.mul_assoc, J_squared, ← Matrix.mul_assoc, J_squared]
  simp

/-- Entrywise product rule for matrices. -/
theorem hasDerivAt_mul_entry {m : Type*} [Fintype m] {M N M' N' : ℝ → Matrix m m ℝ} {t : ℝ}
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' t i j) t)
    (hN : ∀ i j, HasDerivAt (fun s => N s i j) (N' t i j) t) (i j : m) :
    HasDerivAt (fun s => (M s * N s) i j) ((M' t * N t + M t * N' t) i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hM i k).mul (hN k j)
  convert h using 1
  · funext s; simp [mul_apply]
  · simp [mul_apply, Finset.sum_add_distrib]

/-- The fundamental matrix of the linear Hamiltonian system `Φ̇ = A Φ`, `Φ(0) = I`. -/
structure LinearHamiltonianFlow (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) where
  Φ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ
  hasDerivAt : ∀ t i j, HasDerivAt (fun s => Φ s i j) ((hamMatrix S * Φ t) i j) t
  init : Φ 0 = 1

namespace LinearHamiltonianFlow

variable {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (F : LinearHamiltonianFlow S)

/-- **Symplecticity of the flow**: `Φ(t)ᵀ J Φ(t) = J`. -/
theorem symplectic (hS : Sᵀ = S) (t : ℝ) : (F.Φ t)ᵀ * J l ℝ * F.Φ t = J l ℝ := by
  ext i j
  have hd : ∀ t, HasDerivAt (fun s => ((F.Φ s)ᵀ * J l ℝ * F.Φ s) i j) 0 t := fun t => by
    have hT : ∀ i j, HasDerivAt (fun s => ((F.Φ s)ᵀ * J l ℝ) i j)
        (((hamMatrix S * F.Φ t)ᵀ * J l ℝ + (F.Φ t)ᵀ * (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ)) i j) t :=
      fun i j => hasDerivAt_mul_entry (M := fun s => (F.Φ s)ᵀ) (N := fun _ => J l ℝ)
        (M' := fun t => (hamMatrix S * F.Φ t)ᵀ) (N' := fun _ => 0)
        (fun i j => F.hasDerivAt t j i) (fun i j => hasDerivAt_const t _) i j
    have h := hasDerivAt_mul_entry (M := fun s => (F.Φ s)ᵀ * J l ℝ)
      (M' := fun t => (hamMatrix S * F.Φ t)ᵀ * J l ℝ + (F.Φ t)ᵀ * (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ))
      (N := F.Φ) (N' := fun t => hamMatrix S * F.Φ t) hT (F.hasDerivAt t) i j
    convert h using 1
    have e : (hamMatrix S * F.Φ t)ᵀ * J l ℝ * F.Φ t + (F.Φ t)ᵀ * J l ℝ * (hamMatrix S * F.Φ t) =
        (F.Φ t)ᵀ * ((hamMatrix S)ᵀ * J l ℝ + J l ℝ * hamMatrix S) * F.Φ t := by
      simp only [transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [Matrix.mul_zero, add_zero, e, hamiltonian_matrix hS]
    simp
  have := eq_of_hasDerivAt_zero hd t 0
  rw [this, F.init]
  simp

/-- **Liouville's theorem** for linear Hamiltonian systems: `det Φ(t) = 1`, the flow preserves
phase-space volume. -/
theorem det_flow (hS : Sᵀ = S) (t : ℝ) : (F.Φ t).det = 1 :=
  SymplecticGroup.det_eq_one (by rw [SymplecticGroup.mem_iff']; exact F.symplectic hS t)

end LinearHamiltonianFlow

end ClassicalMechanics
