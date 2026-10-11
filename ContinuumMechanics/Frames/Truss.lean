import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pin-jointed frames: compatibility, equilibrium and Maxwell–Calladine counting

A **pin-jointed frame** (truss) in `ℝᵈ` has nodes `N`, bars `B`, node positions `x : N → ℝᵈ` and,
for each bar `b`, its end nodes `src b`, `tgt b`. With the bar vector `e_b = x(tgt b) - x(src b)`:

* the **compatibility matrix** `C` maps node displacements `u` to bar elongations
  `(C u)_b = e_b · (u(tgt b) - u(src b))` (to first order, times the bar length);
* the **equilibrium matrix** is its transpose: a bar tension `t` produces the node forces `Cᵀ t`
  (`equilibrium_apply`), and virtual work reads `t · C u = Cᵀ t · u`.

**Zero modes** (mechanisms, including rigid motions) are `ker C`; **states of self-stress** are
`ker Cᵀ`. The **Maxwell–Calladine index theorem** ([Maxwell1864], [Calladine1978]) is

`N₀ - N_ss = d |N| - |B|`,

a consequence of rank–nullity and `rank Cᵀ = rank C` (`index_matrix`, `maxwell_calladine`). It
holds for every matrix over a field, which is also how it is used for the Bloch matrices of
periodic frames ([KaneLubensky2014]).

Rigid motions `u(n) = a + W x(n)` with `W` skew are zero modes (`rigid_mem_zeroModes`).

## References

* [Maxwell1864] J. C. Maxwell, *On the calculation of the equilibrium and stiffness of frames*,
  Phil. Mag. (1864).
* [Calladine1978] C. R. Calladine, *Buckminster Fuller's "Tensegrity" structures and Clerk
  Maxwell's rules for the construction of stiff frames*, Int. J. Solids Struct. (1978).
* [KaneLubensky2014] C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
  lattices*, Nature Physics (2014).
-/

open Matrix

namespace ContinuumMechanics

/-! ### The index theorem for matrices -/

section Index

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- **Index of a matrix**: `dim ker A - dim ker Aᵀ = #columns - #rows`. -/
theorem index_matrix (A : Matrix m n K) :
    (Module.finrank K (LinearMap.ker A.mulVecLin) : ℤ) -
        Module.finrank K (LinearMap.ker Aᵀ.mulVecLin) =
      Fintype.card n - Fintype.card m := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  have hr : Aᵀ.rank = A.rank := rank_transpose A
  simp only [Matrix.rank] at hr
  simp only [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

end Index

/-! ### Pin-jointed frames -/

/-- A pin-jointed frame in `ℝᵈ` (coordinates `Fin d → ℝ`). -/
structure Truss (d : ℕ) (N B : Type*) where
  /-- Node positions. -/
  x : N → Fin d → ℝ
  /-- First end of each bar. -/
  src : B → N
  /-- Second end of each bar. -/
  tgt : B → N

namespace Truss

variable {d : ℕ} {N B : Type*} [DecidableEq N] (T : Truss d N B)

/-- The bar vector `e_b = x(tgt b) - x(src b)`. -/
def bar (b : B) : Fin d → ℝ := T.x (T.tgt b) - T.x (T.src b)

/-- The **compatibility matrix**: `(C u)_b = e_b · (u(tgt b) - u(src b))`, with displacements
indexed by `(node, coordinate)`. -/
def compat : Matrix B (N × Fin d) ℝ := fun b p =>
  ((if p.1 = T.tgt b then 1 else 0) - (if p.1 = T.src b then 1 else 0)) * T.bar b p.2

/-- Displacement fields as vectors indexed by `(node, coordinate)`. -/
def flat (u : N → Fin d → ℝ) : N × Fin d → ℝ := fun p => u p.1 p.2

theorem compat_mulVec [Fintype N] (u : N → Fin d → ℝ) (b : B) :
    (T.compat *ᵥ flat u) b = ∑ i, T.bar b i * (u (T.tgt b) i - u (T.src b) i) := by
  simp only [compat, mulVec, dotProduct, flat, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_sub]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

/-- The **equilibrium matrix** `Cᵀ`: a bar tension `t` produces at node `n` the force
`Σ_{b ending at n} t_b e_b - Σ_{b starting at n} t_b e_b`. -/
theorem equilibrium_apply [Fintype B] (t : B → ℝ) (n : N) (i : Fin d) :
    (T.compatᵀ *ᵥ t) (n, i) =
      ∑ b, ((if n = T.tgt b then 1 else 0) - (if n = T.src b then 1 else 0)) * t b *
        T.bar b i := by
  simp only [mulVec, dotProduct, transpose_apply, compat]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Virtual work**: `t · C u = Cᵀ t · u`. -/
theorem virtual_work [Fintype N] [Fintype B] (t : B → ℝ) (u : N × Fin d → ℝ) :
    t ⬝ᵥ (T.compat *ᵥ u) = (T.compatᵀ *ᵥ t) ⬝ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- Zero modes (mechanisms and rigid motions). -/
def zeroModes [Fintype N] : Submodule ℝ (N × Fin d → ℝ) := LinearMap.ker T.compat.mulVecLin

/-- States of self-stress. -/
def selfStresses [Fintype B] : Submodule ℝ (B → ℝ) := LinearMap.ker T.compatᵀ.mulVecLin

/-- **Maxwell–Calladine**: `N₀ - N_ss = d |N| - |B|`. -/
theorem maxwell_calladine [Fintype N] [Fintype B] :
    (Module.finrank ℝ T.zeroModes : ℤ) - Module.finrank ℝ T.selfStresses =
      d * Fintype.card N - Fintype.card B := by
  have := index_matrix T.compat
  rw [Fintype.card_prod, Fintype.card_fin] at this
  push_cast at this
  rw [zeroModes, selfStresses, this]
  ring

/-- **Rigid motions are zero modes**: `u(n) = a + W x(n)` with `W` skew-symmetric. -/
theorem rigid_mem_zeroModes [Fintype N] (a : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℝ)
    (hW : Wᵀ = -W) :
    flat (fun n => a + W *ᵥ T.x n) ∈ T.zeroModes := by
  simp only [zeroModes, LinearMap.mem_ker, mulVecLin_apply]
  funext b
  rw [compat_mulVec]
  have hskew : ∀ v : Fin d → ℝ, v ⬝ᵥ (W *ᵥ v) = 0 := fun v => by
    have h1 : v ⬝ᵥ (W *ᵥ v) = (Wᵀ *ᵥ v) ⬝ᵥ v := by
      rw [dotProduct_mulVec, mulVec_transpose]
    have h2 : (Wᵀ *ᵥ v) ⬝ᵥ v = -(v ⬝ᵥ (W *ᵥ v)) := by
      rw [hW, neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have e : ∑ i, T.bar b i * ((a + W *ᵥ T.x (T.tgt b)) i - (a + W *ᵥ T.x (T.src b)) i) =
      T.bar b ⬝ᵥ (W *ᵥ T.bar b) := by
    simp only [bar, mulVec_sub, dotProduct, Pi.add_apply, Pi.sub_apply, add_sub_add_left_eq_sub]
  rw [e, hskew]
  rfl

/-! ### Example: a triangle is rigid -/

/-- The triangle `(0, 0)`, `(1, 0)`, `(0, 1)` with bars `01`, `12`, `20`. -/
def triangle : Truss 2 (Fin 3) (Fin 3) where
  x := ![![0, 0], ![1, 0], ![0, 1]]
  src := ![0, 1, 2]
  tgt := ![1, 2, 0]

/-- The triangle has no state of self-stress. -/
theorem triangle_selfStresses : triangle.selfStresses = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  simp only [selfStresses, LinearMap.mem_ker, mulVecLin_apply] at ht
  have e := fun n i => congrFun ht (n, i)
  simp only [equilibrium_apply, Pi.zero_apply, Fin.sum_univ_three] at e
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 1
  simp [triangle, bar] at e00 e01 e10
  rw [Submodule.mem_bot]
  funext b; fin_cases b <;> simp <;> linarith

/-- **The triangle is rigid**: its only zero modes are the 3 rigid motions of the plane
(Maxwell–Calladine: `N₀ = 2 · 3 - 3 + N_ss = 3`). -/
theorem triangle_finrank_zeroModes : Module.finrank ℝ triangle.zeroModes = 3 := by
  have h := triangle.maxwell_calladine
  rw [triangle_selfStresses, finrank_bot] at h
  simp only [Fintype.card_fin] at h
  omega

end Truss

end ContinuumMechanics
