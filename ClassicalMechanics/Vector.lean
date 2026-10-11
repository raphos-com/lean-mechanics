import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vectors in `ℝ³` and their time derivatives

Classical mechanics is formulated in `ℝ³ = Fin 3 → ℝ`, with the dot product `u ⬝ᵥ v` and the
cross product `u ⨯₃ v` of Mathlib. This file provides the product rules for trajectories
`ℝ → ℝ³` (`hasDerivAt_dot`, `hasDerivAt_cross`) and the constancy of quantities with zero
derivative (`eq_of_hasDerivAt_zero`).
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- Vectors of physical space. -/
abbrev Vec := Fin 3 → ℝ

variable {f g : ℝ → Vec} {f' g' : Vec} {t : ℝ}

/-- Product rule for the dot product. -/
theorem hasDerivAt_dot (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hf' i).mul (hg' i)
  convert this using 1
  · ext s; simp [dotProduct]
  · simp [dotProduct, Finset.sum_add_distrib]

/-- Product rule for the cross product. -/
theorem hasDerivAt_cross (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⨯₃ g s) (f' ⨯₃ g t + f t ⨯₃ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · convert ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1)) using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring
  · convert ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2)) using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring
  · convert ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0)) using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring

/-- `|v|² = v · v`. -/
def normSq (v : Vec) : ℝ := v ⬝ᵥ v

theorem normSq_nonneg (v : Vec) : 0 ≤ normSq v := by
  simp only [normSq, dotProduct, Fin.sum_univ_three]
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- A quantity whose derivative vanishes everywhere is constant. -/
theorem eq_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E}
    (h : ∀ t, HasDerivAt F 0 t) (s t : ℝ) : F s = F t :=
  is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) s t

end ClassicalMechanics
