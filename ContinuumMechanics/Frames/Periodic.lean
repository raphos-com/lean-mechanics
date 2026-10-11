import ContinuumMechanics.Frames.Truss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Periodic pin-jointed frames and their Bloch matrices

A **periodic frame** in `ℝᵈ` repeats a unit cell along a lattice with basis `a₁, …, a_d`. The cell
has nodes `N` and bars `B`; bar `b` joins node `src b` of cell `ℓ ∈ ℤᵈ` to node `tgt b` of cell
`ℓ + shift b`, so its vector is `e_b = x(tgt b) + Σⱼ (shift b)ⱼ aⱼ - x(src b)`.

The compatibility operator of the infinite frame maps a displacement field `u : ℤᵈ → N → ℝᵈ` to
the bar elongations `e_b · (u(ℓ + shift b, tgt b) - u(ℓ, src b))`. On a **Bloch field**
`u(ℓ, n) = e^{iθ·ℓ} u⁰(n)` it acts through the `|B| × d|N|` **Bloch compatibility matrix**

`C(θ)_b = e_b · (e^{iθ·shift b} u⁰(tgt b) - u⁰(src b))`

(`compatFull_bloch`). Its kernel consists of the Bloch zero modes, and the kernel of `C(θ)ᴴ` of
the Bloch states of self-stress. The **Maxwell–Calladine index theorem holds at every wave
vector**: `N₀(θ) - N_ss(θ) = d|N| - |B|` (`maxwell_calladine_bloch`). For a **Maxwell lattice**
(`d|N| = |B|`, e.g. the square and kagome lattices) the numbers of zero modes and self-stresses
are therefore equal at every `θ` — the starting point of [KaneLubensky2014].

At `θ = 0` uniform translations are zero modes (`translation_mem_zeroModes`).

## References

* [KaneLubensky2014] C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
  lattices*, Nature Physics (2014).
* [Calladine1978] C. R. Calladine, Int. J. Solids Struct. (1978).
-/

open Matrix
open scoped ComplexOrder

namespace ContinuumMechanics

section Index

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Index of a complex matrix**: `dim ker A - dim ker Aᴴ = #columns - #rows`. -/
theorem index_matrix_conjTranspose (A : Matrix m n ℂ) :
    (Module.finrank ℂ (LinearMap.ker A.mulVecLin) : ℤ) -
        Module.finrank ℂ (LinearMap.ker Aᴴ.mulVecLin) =
      Fintype.card n - Fintype.card m := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Aᴴ.mulVecLin
  have hr : Aᴴ.rank = A.rank := rank_conjTranspose A
  simp only [Matrix.rank] at hr
  simp only [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

end Index

/-- A periodic pin-jointed frame in `ℝᵈ`. -/
structure PeriodicTruss (d : ℕ) (N B : Type*) where
  /-- Lattice basis `aⱼ`. -/
  lattice : Fin d → Fin d → ℝ
  /-- Node positions in cell `0`. -/
  x : N → Fin d → ℝ
  /-- First end of each bar (in cell `ℓ`). -/
  src : B → N
  /-- Second end of each bar (in cell `ℓ + shift b`). -/
  tgt : B → N
  /-- Cell offset of the second end. -/
  shift : B → Fin d → ℤ

namespace PeriodicTruss

variable {d : ℕ} {N B : Type*} [DecidableEq N] (T : PeriodicTruss d N B)

/-- Position of node `n` in cell `ℓ`. -/
def pos (ℓ : Fin d → ℤ) (n : N) : Fin d → ℝ := T.x n + ∑ j, (ℓ j : ℝ) • T.lattice j

/-- The bar vector `e_b`. -/
def bar (b : B) : Fin d → ℝ := T.pos (T.shift b) (T.tgt b) - T.x (T.src b)

omit [DecidableEq N] in
theorem bar_eq_pos (ℓ : Fin d → ℤ) (b : B) :
    T.bar b = T.pos (ℓ + T.shift b) (T.tgt b) - T.pos ℓ (T.src b) := by
  simp only [bar, pos, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
  abel

/-- The compatibility operator of the infinite frame (complex displacements). -/
def compatFull (u : (Fin d → ℤ) → N → Fin d → ℂ) (ℓ : Fin d → ℤ) (b : B) : ℂ :=
  ∑ i, (T.bar b i : ℂ) * (u (ℓ + T.shift b) (T.tgt b) i - u ℓ (T.src b) i)

/-- The Bloch phase `e^{iθ·ℓ}`. -/
noncomputable def phase (θ : Fin d → ℝ) (ℓ : Fin d → ℤ) : ℂ :=
  Complex.exp ((∑ j, θ j * ℓ j : ℝ) * Complex.I)

theorem phase_add (θ : Fin d → ℝ) (ℓ ℓ' : Fin d → ℤ) :
    phase θ (ℓ + ℓ') = phase θ ℓ * phase θ ℓ' := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

/-- The **Bloch compatibility matrix** `C(θ)`. -/
noncomputable def compatBloch (θ : Fin d → ℝ) : Matrix B (N × Fin d) ℂ := fun b p =>
  ((if p.1 = T.tgt b then phase θ (T.shift b) else 0) - (if p.1 = T.src b then 1 else 0)) *
    T.bar b p.2

/-- A Bloch displacement field `u(ℓ, n) = e^{iθ·ℓ} u⁰(n)`. -/
noncomputable def bloch (θ : Fin d → ℝ) (u : N → Fin d → ℂ) :
    (Fin d → ℤ) → N → Fin d → ℂ := fun ℓ n => phase θ ℓ • u n

/-- **Bloch reduction**: on a Bloch field the compatibility operator of the infinite frame is
the Bloch matrix, times the phase of the cell. -/
theorem compatFull_bloch [Fintype N] (θ : Fin d → ℝ) (u : N → Fin d → ℂ) (ℓ : Fin d → ℤ)
    (b : B) :
    T.compatFull (bloch θ u) ℓ b =
      phase θ ℓ * (T.compatBloch θ *ᵥ fun p => u p.1 p.2) b := by
  simp only [compatFull, bloch, compatBloch, mulVec, dotProduct, Fintype.sum_prod_type,
    phase_add, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- Bloch zero modes. -/
noncomputable def zeroModes [Fintype N] (θ : Fin d → ℝ) : Submodule ℂ (N × Fin d → ℂ) :=
  LinearMap.ker (T.compatBloch θ).mulVecLin

/-- Bloch states of self-stress (kernel of the equilibrium matrix `C(θ)ᴴ`). -/
noncomputable def selfStresses [Fintype B] (θ : Fin d → ℝ) : Submodule ℂ (B → ℂ) :=
  LinearMap.ker (T.compatBloch θ)ᴴ.mulVecLin

/-- **Maxwell–Calladine at every wave vector**: `N₀(θ) - N_ss(θ) = d|N| - |B|`. -/
theorem maxwell_calladine_bloch [Fintype N] [Fintype B] (θ : Fin d → ℝ) :
    (Module.finrank ℂ (T.zeroModes θ) : ℤ) - Module.finrank ℂ (T.selfStresses θ) =
      d * Fintype.card N - Fintype.card B := by
  have := index_matrix_conjTranspose (T.compatBloch θ)
  rw [Fintype.card_prod, Fintype.card_fin] at this
  push_cast at this
  rw [zeroModes, selfStresses, this]
  ring

/-- For a **Maxwell lattice** (`d|N| = |B|`) zero modes and self-stresses are equinumerous at
every wave vector. -/
theorem finrank_zeroModes_eq_selfStresses [Fintype N] [Fintype B]
    (hM : d * Fintype.card N = Fintype.card B) (θ : Fin d → ℝ) :
    Module.finrank ℂ (T.zeroModes θ) = Module.finrank ℂ (T.selfStresses θ) := by
  have := T.maxwell_calladine_bloch θ
  rw [← Nat.cast_mul, hM, sub_self] at this
  omega

theorem phase_zero (ℓ : Fin d → ℤ) : phase (0 : Fin d → ℝ) ℓ = 1 := by simp [phase]

/-- At `θ = 0`, uniform translations are zero modes. -/
theorem translation_mem_zeroModes [Fintype N] (a : Fin d → ℂ) :
    (fun p : N × Fin d => a p.2) ∈ T.zeroModes 0 := by
  simp only [zeroModes, LinearMap.mem_ker, mulVecLin_apply]
  funext b
  simp only [compatBloch, phase_zero, mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun x y => if x = T.tgt b then (T.bar b y : ℂ) * a y else 0),
    Finset.sum_comm (f := fun x y => if x = T.src b then (T.bar b y : ℂ) * a y else 0)]
  simp [Finset.sum_ite_eq']

end PeriodicTruss

end ContinuumMechanics
