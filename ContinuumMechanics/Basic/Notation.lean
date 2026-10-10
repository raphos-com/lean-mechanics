import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Notation for continuum mechanics

Scoped notation shared by the whole library. Open it with
`open scoped ContinuumMechanics`.

* `Aᵀ` — the transpose of a second-order tensor. For `A : E →L[ℝ] E` on a real
  inner product space this is Mathlib's Hilbert adjoint, available as `star A`
  ([Gurtin1981], §1.2: `Aᵀ` is the unique tensor with `u · Aᵀ v = A u · v`).

Further symbols (`A ⊡ B`, `a ⊗ b`, `𝕀ˢʸᵐ`) are introduced next to their definitions in
`ContinuumMechanics/Tensor/`.
-/

namespace ContinuumMechanics

/-- `Aᵀ` is the transpose of a tensor, i.e. `star A`; for continuous linear endomorphisms of
a real inner product space this is the adjoint `ContinuousLinearMap.adjoint A`.
[Gurtin1981], §1.2. -/
scoped postfix:max "ᵀ" => star

end ContinuumMechanics

section Examples

open scoped ContinuumMechanics InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The defining property of the transpose: `⟪Aᵀ u, v⟫ = ⟪u, A v⟫`. -/
example (A : E →L[ℝ] E) (u v : E) : ⟪Aᵀ u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left A v u

/-- Transposition reverses products: `(A B)ᵀ = Bᵀ Aᵀ`. -/
example (A B : E →L[ℝ] E) : (A * B)ᵀ = Bᵀ * Aᵀ := star_mul A B

end Examples
