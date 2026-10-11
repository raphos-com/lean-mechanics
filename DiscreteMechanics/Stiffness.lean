import DiscreteMechanics.Truss
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The direct stiffness method for linear elastic trusses

A linear elastic bar `b` with Young's modulus `E_b`, cross-section `A_b` and length `L_b` has
**axial stiffness** `k_b = E_b A_b / L_b`: its tension is `t_b = k_b e_b` for an elongation `e_b`.
If `C` is the compatibility matrix (`e = C u`), the **global stiffness matrix** is

`K = Cᵀ diag(k) C`,

so that the bar forces are `t = diag(k) C u` and the node forces are `Cᵀ t = K u`
(the equilibrium matrix is `Cᵀ`, see `DiscreteMechanics.Truss`).

Everything is stated for an arbitrary real matrix `C : Matrix B D ℝ` (bars `B`, degrees of
freedom `D`) and then specialised to `Truss.compat`.

## Main results

* `stiffness_isSymm`, `stiffness_isHermitian`: `K` is symmetric.
* `dotProduct_stiffness_mulVec`: the strain energy `uᵀ K u = Σ_b k_b (C u)_b²`.
* `stiffness_posSemidef`: `K` is positive semidefinite for `k ≥ 0`.
* `stiffness_mulVec_eq_zero_iff`, `ker_stiffness`: for `k > 0`, `K u = 0 ↔ C u = 0`,
  i.e. `ker K = ker C` (mechanisms and rigid-body motions).
* `stiffness_eq_sum`: **assembly**, `K = Σ_b k_b c_b c_bᵀ` with `c_b` the `b`-th row of `C`.
* `stiffness_submatrix`: imposing supports (keeping the free degrees of freedom) commutes with
  forming `K`: `K_ff = C_fᵀ diag(k) C_f`.
* `stiffness_posDef`, `stiffness_isUnit`, `existsUnique_displacement`: if the restricted
  compatibility matrix is injective (kinematically determinate), `K_ff` is positive definite,
  invertible, and `K_ff u = f` has a unique solution for every load `f`.
* `minimum_potential_energy`, `minimum_potential_energy_strict`: a solution of `K u = f`
  minimises the potential energy `½ uᵀ K u - fᵀ u` (strictly if `K` is positive definite).
* `equilibrium_barForces`: the bar forces `t = diag(k) C u` satisfy equilibrium `Cᵀ t = f`.
* `maxwell_betti`: Maxwell–Betti reciprocity `u₁ · f₂ = u₂ · f₁`.
* `Truss.twoBar_*`: a two-bar plane truss worked out with explicit numbers.

## References

* [Maxwell1864] J. C. Maxwell, *On the calculation of the equilibrium and stiffness of frames*,
  Phil. Mag. (1864).
* [Betti1872] E. Betti, *Teoria della elasticità*, Il Nuovo Cimento (1872).
* [Przemieniecki1968] J. S. Przemieniecki, *Theory of Matrix Structural Analysis*,
  McGraw–Hill (1968).
-/

open Matrix

namespace DiscreteMechanics

/-- The **axial stiffness** `k = E A / L` of a bar with Young's modulus `E`, cross-sectional area
`A` and length `L`. -/
noncomputable def barStiffness (E A L : ℝ) : ℝ := E * A / L

/-- The axial stiffness of a bar with positive modulus, area and length is positive. -/
theorem barStiffness_pos {E A L : ℝ} (hE : 0 < E) (hA : 0 < A) (hL : 0 < L) :
    0 < barStiffness E A L :=
  div_pos (mul_pos hE hA) hL

section General

variable {B D F : Type*} [Fintype B] [DecidableEq B]

/-- The **global stiffness matrix** `K = Cᵀ diag(k) C` of a compatibility matrix `C` and bar
stiffnesses `k`. -/
def stiffness (C : Matrix B D ℝ) (k : B → ℝ) : Matrix D D ℝ := Cᵀ * diagonal k * C

/-- Entries of the stiffness matrix: `K i j = Σ_b k_b C b i C b j`. -/
theorem stiffness_apply (C : Matrix B D ℝ) (k : B → ℝ) (i j : D) :
    stiffness C k i j = ∑ b, k b * C b i * C b j := by
  rw [stiffness, Matrix.mul_assoc, mul_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [diagonal_mul, transpose_apply]; ring

/-- The stiffness matrix is **symmetric**. -/
theorem stiffness_isSymm (C : Matrix B D ℝ) (k : B → ℝ) : (stiffness C k).IsSymm := by
  ext i j
  rw [transpose_apply, stiffness_apply, stiffness_apply]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The stiffness matrix is Hermitian (symmetric, over `ℝ`). -/
theorem stiffness_isHermitian (C : Matrix B D ℝ) (k : B → ℝ) :
    (stiffness C k).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact stiffness_isSymm C k

/-- The **bar forces** `t = diag(k) C u` produced by node displacements `u`. -/
def barForces [Fintype D] (C : Matrix B D ℝ) (k : B → ℝ) (u : D → ℝ) : B → ℝ :=
  diagonal k *ᵥ (C *ᵥ u)

/-- The stiffness matrix maps displacements to node forces: `K u = Cᵀ t`
(with `t = diag(k) C u` the bar forces). -/
theorem stiffness_mulVec [Fintype D] (C : Matrix B D ℝ) (k : B → ℝ) (u : D → ℝ) :
    stiffness C k *ᵥ u = Cᵀ *ᵥ barForces C k u := by
  simp only [stiffness, barForces, mulVec_mulVec, Matrix.mul_assoc]

/-- Bar `b` carries the tension `t_b = k_b (C u)_b`. -/
theorem barForces_apply [Fintype D] (C : Matrix B D ℝ) (k : B → ℝ) (u : D → ℝ) (b : B) :
    barForces C k u b = k b * (C *ᵥ u) b := by
  simp [barForces, mulVec_diagonal]

/-- **Strain energy**: `uᵀ K u = Σ_b k_b (C u)_b²`. -/
theorem dotProduct_stiffness_mulVec [Fintype D] (C : Matrix B D ℝ) (k : B → ℝ) (u : D → ℝ) :
    u ⬝ᵥ (stiffness C k *ᵥ u) = ∑ b, k b * (C *ᵥ u) b ^ 2 := by
  rw [stiffness_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, barForces_apply]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Positive semidefiniteness**: for nonnegative bar stiffnesses, `K` is positive
semidefinite. -/
theorem stiffness_posSemidef [Finite D] (C : Matrix B D ℝ) {k : B → ℝ} (hk : ∀ b, 0 ≤ k b) :
    (stiffness C k).PosSemidef := by
  have := Fintype.ofFinite D
  refine PosSemidef.of_dotProduct_mulVec_nonneg (stiffness_isHermitian C k) fun u => ?_
  rw [star_trivial, dotProduct_stiffness_mulVec]
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hk b) (sq_nonneg _)

/-- **Zero-energy modes**: for positive bar stiffnesses, `uᵀ K u = 0` iff `C u = 0`. -/
theorem dotProduct_stiffness_mulVec_eq_zero_iff [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ}
    (hk : ∀ b, 0 < k b) (u : D → ℝ) :
    u ⬝ᵥ (stiffness C k *ᵥ u) = 0 ↔ C *ᵥ u = 0 := by
  rw [dotProduct_stiffness_mulVec,
    Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_nonneg (hk b).le (sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, (hk _).ne', false_or, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
  exact ⟨fun h => funext h, fun h b => congrFun h b⟩

/-- **The kernel of the stiffness matrix**: for positive bar stiffnesses, `K u = 0 ↔ C u = 0`;
the displacements producing no node forces are exactly the mechanisms and rigid motions. -/
theorem stiffness_mulVec_eq_zero_iff [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ}
    (hk : ∀ b, 0 < k b) (u : D → ℝ) :
    stiffness C k *ᵥ u = 0 ↔ C *ᵥ u = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← dotProduct_stiffness_mulVec_eq_zero_iff C hk, h, dotProduct_zero]
  · rw [stiffness_mulVec, barForces, h, mulVec_zero, mulVec_zero]

/-- `ker K = ker C` for positive bar stiffnesses. -/
theorem ker_stiffness [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ} (hk : ∀ b, 0 < k b) :
    LinearMap.ker (stiffness C k).mulVecLin = LinearMap.ker C.mulVecLin := by
  ext u
  simp only [LinearMap.mem_ker, mulVecLin_apply, stiffness_mulVec_eq_zero_iff C hk]

/-! ### Assembly from element stiffness matrices -/

/-- The **element stiffness matrix** `k_b c_b c_bᵀ` of bar `b`, with `c_b` the `b`-th row of
`C`. -/
def elementStiffness (C : Matrix B D ℝ) (k : B → ℝ) (b : B) : Matrix D D ℝ :=
  k b • vecMulVec (C b) (C b)

/-- **Assembly**: the global stiffness matrix is the sum of the element stiffness matrices,
`K = Σ_b k_b c_b c_bᵀ`. -/
theorem stiffness_eq_sum (C : Matrix B D ℝ) (k : B → ℝ) :
    stiffness C k = ∑ b, elementStiffness C k b := by
  ext i j
  rw [stiffness_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [elementStiffness, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-! ### Supports and the reduced stiffness matrix -/

/-- **Supports**: keeping only the free degrees of freedom `free : F → D`, the reduced stiffness
matrix `K_ff` is the stiffness matrix of the reduced compatibility matrix `C_f`. -/
theorem stiffness_submatrix (C : Matrix B D ℝ) (k : B → ℝ) (free : F → D) :
    (stiffness C k).submatrix free free = stiffness (C.submatrix id free) k := by
  ext i j
  simp only [submatrix_apply, stiffness_apply, id]

/-- **Kinematic determinacy implies positive definiteness**: if `C` has trivial kernel (no
mechanisms, no rigid motions) and all bar stiffnesses are positive, `K` is positive definite. -/
theorem stiffness_posDef [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ} (hk : ∀ b, 0 < k b)
    (hC : ∀ u, C *ᵥ u = 0 → u = 0) : (stiffness C k).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (stiffness_isHermitian C k) fun u hu => ?_
  rw [star_trivial]
  refine lt_of_le_of_ne ?_ fun h => hu (hC u ?_)
  · rw [dotProduct_stiffness_mulVec]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hk b).le (sq_nonneg _)
  · exact (dotProduct_stiffness_mulVec_eq_zero_iff C hk u).1 h.symm

/-- **The reduced stiffness matrix is positive definite** when the structure, restricted to its
free degrees of freedom, is kinematically determinate. -/
theorem reducedStiffness_posDef [Fintype F] (C : Matrix B D ℝ) {k : B → ℝ}
    (hk : ∀ b, 0 < k b) (free : F → D) (hC : ∀ v, C.submatrix id free *ᵥ v = 0 → v = 0) :
    ((stiffness C k).submatrix free free).PosDef := by
  rw [stiffness_submatrix]
  exact stiffness_posDef _ hk hC

/-- A positive definite (reduced) stiffness matrix is invertible. -/
theorem reducedStiffness_isUnit [Fintype F] [DecidableEq F] (C : Matrix B D ℝ)
    {k : B → ℝ} (hk : ∀ b, 0 < k b) (free : F → D)
    (hC : ∀ v, C.submatrix id free *ᵥ v = 0 → v = 0) :
    IsUnit ((stiffness C k).submatrix free free) :=
  (reducedStiffness_posDef C hk free hC).isUnit

/-- **Unique solvability**: for a kinematically determinate supported truss, `K_ff u = f` has a
unique solution `u` for every load `f`. -/
theorem existsUnique_displacement [Fintype F] (C : Matrix B D ℝ)
    {k : B → ℝ} (hk : ∀ b, 0 < k b) (free : F → D)
    (hC : ∀ v, C.submatrix id free *ᵥ v = 0 → v = 0) (f : F → ℝ) :
    ∃! u, (stiffness C k).submatrix free free *ᵥ u = f := by
  classical
  have hU := reducedStiffness_isUnit C hk free hC
  obtain ⟨u, hu⟩ := mulVec_surjective_iff_isUnit.2 hU f
  exact ⟨u, hu, fun v hv => mulVec_injective_iff_isUnit.2 hU (hv.trans hu.symm)⟩

/-! ### Minimum potential energy and equilibrium -/

/-- The **total potential energy** `Π(u) = ½ uᵀ K u - fᵀ u` under the load `f`. -/
noncomputable def potentialEnergy [Fintype D] (K : Matrix D D ℝ) (f u : D → ℝ) : ℝ :=
  1 / 2 * (u ⬝ᵥ (K *ᵥ u)) - f ⬝ᵥ u

/-- For a symmetric matrix, `u · K v = v · K u`. -/
theorem dotProduct_mulVec_comm_of_isSymm [Fintype D] {K : Matrix D D ℝ} (hK : K.IsSymm)
    (u v : D → ℝ) : u ⬝ᵥ (K *ᵥ v) = v ⬝ᵥ (K *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hK.eq, dotProduct_comm]

/-- **Energy expansion about an equilibrium**: if `K` is symmetric and `K u = f`, then
`Π(v) = Π(u) + ½ (v - u)ᵀ K (v - u)`. -/
theorem potentialEnergy_eq_add [Fintype D] {K : Matrix D D ℝ} (hK : K.IsSymm) {f u : D → ℝ}
    (hu : K *ᵥ u = f) (v : D → ℝ) :
    potentialEnergy K f v = potentialEnergy K f u + 1 / 2 * ((v - u) ⬝ᵥ (K *ᵥ (v - u))) := by
  have h := dotProduct_mulVec_comm_of_isSymm hK u v
  simp only [potentialEnergy, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  rw [hu] at h ⊢
  rw [dotProduct_comm f u, dotProduct_comm f v]
  linarith

/-- **Principle of minimum potential energy**: if `K u = f` for the stiffness matrix of a truss
with nonnegative bar stiffnesses, then `u` minimises `Π(v) = ½ vᵀ K v - fᵀ v`. -/
theorem minimum_potential_energy [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ}
    (hk : ∀ b, 0 ≤ k b) {f u : D → ℝ} (hu : stiffness C k *ᵥ u = f) (v : D → ℝ) :
    potentialEnergy (stiffness C k) f u ≤ potentialEnergy (stiffness C k) f v := by
  rw [potentialEnergy_eq_add (stiffness_isSymm C k) hu v, dotProduct_stiffness_mulVec]
  have : 0 ≤ ∑ b, k b * (C *ᵥ (v - u)) b ^ 2 :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hk b) (sq_nonneg _)
  linarith

/-- **Strict minimum**: for a kinematically determinate truss with positive bar stiffnesses, the
solution of `K u = f` is the unique minimiser of the potential energy. -/
theorem minimum_potential_energy_strict [Fintype D] (C : Matrix B D ℝ) {k : B → ℝ}
    (hk : ∀ b, 0 < k b) (hC : ∀ u, C *ᵥ u = 0 → u = 0) {f u : D → ℝ}
    (hu : stiffness C k *ᵥ u = f) {v : D → ℝ} (hv : v ≠ u) :
    potentialEnergy (stiffness C k) f u < potentialEnergy (stiffness C k) f v := by
  rw [potentialEnergy_eq_add (stiffness_isSymm C k) hu v]
  have := (stiffness_posDef C hk hC).dotProduct_mulVec_pos (sub_ne_zero.2 hv)
  rw [star_trivial] at this
  linarith

/-- **Equilibrium of the bar forces**: if `K u = f`, the bar forces `t = diag(k) C u` balance the
load through the equilibrium matrix, `Cᵀ t = f`. -/
theorem equilibrium_barForces [Fintype D] (C : Matrix B D ℝ) (k : B → ℝ) {f u : D → ℝ}
    (hu : stiffness C k *ᵥ u = f) : Cᵀ *ᵥ barForces C k u = f := by
  rw [← stiffness_mulVec, hu]

/-- **Maxwell–Betti reciprocal theorem**: for a symmetric stiffness matrix, the work of the
loads `f₂` on the displacements `u₁` due to `f₁` equals the work of `f₁` on `u₂`. -/
theorem maxwell_betti [Fintype D] {K : Matrix D D ℝ} (hK : K.IsSymm) {u₁ u₂ f₁ f₂ : D → ℝ}
    (h₁ : K *ᵥ u₁ = f₁) (h₂ : K *ᵥ u₂ = f₂) : u₁ ⬝ᵥ f₂ = u₂ ⬝ᵥ f₁ := by
  rw [← h₁, ← h₂, dotProduct_mulVec_comm_of_isSymm hK]

end General

/-! ### Trusses -/

namespace Truss

variable {d : ℕ} {N B F : Type*} [DecidableEq N] [Fintype N] [Fintype B] [DecidableEq B]
  (T : Truss d N B)

/-- The global stiffness matrix `K = Cᵀ diag(k) C` of a truss with bar stiffnesses `k`. -/
def stiffnessMatrix (k : B → ℝ) : Matrix (N × Fin d) (N × Fin d) ℝ := stiffness T.compat k

/-- **The kernel of the truss stiffness matrix is the space of zero modes** (mechanisms and
rigid motions) when all bar stiffnesses are positive. -/
theorem ker_stiffnessMatrix {k : B → ℝ} (hk : ∀ b, 0 < k b) :
    LinearMap.ker (T.stiffnessMatrix k).mulVecLin = T.zeroModes :=
  ker_stiffness T.compat hk

/-- **Equilibrium**: if `K u = f`, the bar tensions `t = diag(k) C u` satisfy `Cᵀ t = f`, i.e.
at each node `n` the forces of the bars meeting at `n` balance the load (`equilibrium_apply`). -/
theorem equilibrium_of_stiffness {k : B → ℝ} {f u : N × Fin d → ℝ}
    (hu : T.stiffnessMatrix k *ᵥ u = f) (n : N) (i : Fin d) :
    ∑ b, ((if n = T.tgt b then 1 else 0) - (if n = T.src b then 1 else 0)) *
        barForces T.compat k u b * T.bar b i = f (n, i) := by
  rw [← T.equilibrium_apply, equilibrium_barForces T.compat k hu]

/-! ### A two-bar example -/

/-- A two-bar plane truss: supports at `(0, 0)` and `(2, 0)`, apex `(1, 1)`; bar `0` joins
`(0, 0)` to the apex and bar `1` joins `(2, 0)` to the apex. -/
def twoBar : Truss 2 (Fin 3) (Fin 2) where
  x := ![![0, 0], ![2, 0], ![1, 1]]
  src := ![0, 1]
  tgt := ![2, 2]

/-- The free degrees of freedom of `twoBar`: the two displacement components of the apex. -/
def twoBarFree (i : Fin 2) : Fin 3 × Fin 2 := (2, i)

/-- The reduced compatibility matrix of `twoBar` (rows: the bar vectors `(1, 1)`, `(-1, 1)`). -/
theorem twoBar_reducedCompat :
    twoBar.compat.submatrix id twoBarFree = !![1, 1; -1, 1] := by
  ext b i
  fin_cases b <;> fin_cases i <;> norm_num [compat, bar, twoBar, twoBarFree]

/-- With bar stiffnesses `k = (3, 1)` the reduced stiffness matrix is `[[4, 2], [2, 4]]`. -/
theorem twoBar_reducedStiffness :
    (twoBar.stiffnessMatrix ![3, 1]).submatrix twoBarFree twoBarFree = !![4, 2; 2, 4] := by
  rw [stiffnessMatrix, stiffness_submatrix, twoBar_reducedCompat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stiffness_apply, Fin.sum_univ_two] <;> norm_num

/-- `twoBar` is kinematically determinate once its supports are imposed. -/
theorem twoBar_determinate (v : Fin 2 → ℝ) :
    twoBar.compat.submatrix id twoBarFree *ᵥ v = 0 → v = 0 := by
  rw [twoBar_reducedCompat]
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Worked example**: under a downward load `6` at the apex, the apex displacement
`u = (1, -2)` solves `K_ff u = (0, -6)`. -/
theorem twoBar_displacement :
    (twoBar.stiffnessMatrix ![3, 1]).submatrix twoBarFree twoBarFree *ᵥ ![1, -2] =
      ![0, -6] := by
  rw [twoBar_reducedStiffness]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The apex displacement `(1, -2)` is the only solution of `K_ff u = (0, -6)`. -/
theorem twoBar_displacement_unique (u : Fin 2 → ℝ)
    (hu : (twoBar.stiffnessMatrix ![3, 1]).submatrix twoBarFree twoBarFree *ᵥ u = ![0, -6]) :
    u = ![1, -2] := by
  have hk : ∀ b, 0 < (![3, 1] : Fin 2 → ℝ) b := by
    intro b; fin_cases b <;> norm_num
  obtain ⟨w, _, hw⟩ :=
    existsUnique_displacement twoBar.compat hk twoBarFree twoBar_determinate ![0, -6]
  rw [hw u hu, hw _ twoBar_displacement]

/-- Both bars are in compression with force `3` (tension `-3`) under the load `(0, -6)`. -/
theorem twoBar_barForces :
    barForces (twoBar.compat.submatrix id twoBarFree) ![3, 1] ![1, -2] = ![-3, -3] := by
  rw [twoBar_reducedCompat]
  ext b
  fin_cases b <;> simp [barForces_apply, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

end Truss

end DiscreteMechanics
