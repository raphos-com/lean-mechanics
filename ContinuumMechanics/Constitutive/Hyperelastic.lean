import ContinuumMechanics.Tensor.DetDeriv
import ContinuumMechanics.Kinematics.Body

/-!
# Hyperelastic materials and frame indifference

A **hyperelastic** material has a stored-energy function `W : Lin E → ℝ` whose derivative is the
first Piola–Kirchhoff stress: `DW(F)[H] = P(F) : H`, written `P = ∂W/∂F`
([Gurtin1981], §§27–29; [Ciarlet1988], §4.1). Only deformation gradients with `det F > 0` are
physically admissible, so all statements are on that (open) set.

## Main definitions

* `Lin.dcontrCLM P`: the continuous linear functional `H ↦ P : H`.
* `Lin.IsPiolaOf W P F`: `P` is the first Piola–Kirchhoff stress of `W` at `F`.
* `Lin.IsFrameIndifferent W`: `W(Q F) = W(F)` for every rotation `Q` and `det F > 0`.

## Main results

* `Lin.IsPiolaOf.unique`: the stress is determined by the energy.
* `Lin.isFrameIndifferent_iff`: **`W` is frame-indifferent iff `W(F) = Ŵ(Fᵀ F)` for some `Ŵ`**
  (reduced form via the right Cauchy–Green tensor). [Gurtin1981], §29; [Ciarlet1988], Thm. 4.2-1.
* `Lin.IsFrameIndifferent.piola_rot_mul`: for a frame-indifferent hyperelastic material,
  `P(Q F) = Q P(F)`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§27–29.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §§3–4.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics Ring

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- `H ↦ P : H` as a continuous linear functional. -/
noncomputable def dcontrCLM (P : Lin E) : Lin E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (dcontr P)

@[simp] theorem dcontrCLM_apply (P H : Lin E) : dcontrCLM P H = P ⊡ H := rfl

/-- Nondegeneracy of the double contraction. -/
theorem eq_of_dcontr_eq {A B : Lin E} (h : ∀ H, A ⊡ H = B ⊡ H) : A = B := by
  have := h (A - B)
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub] at this
  exact sub_eq_zero.mp (dcontr_self_eq_zero.mp this)

theorem dcontrCLM_injective : Function.Injective (dcontrCLM : Lin E → Lin E →L[ℝ] ℝ) :=
  fun _ _ h => eq_of_dcontr_eq fun H => congrArg (fun L => L H) h

/-- `P` is the **first Piola–Kirchhoff stress** of the stored energy `W` at `F`:
`DW(F)[H] = P : H`. [Gurtin1981], §27. -/
def IsPiolaOf (W : Lin E → ℝ) (P F : Lin E) : Prop := HasFDerivAt W (dcontrCLM P) F

theorem IsPiolaOf.unique {W : Lin E → ℝ} {P₁ P₂ F : Lin E} (h₁ : IsPiolaOf W P₁ F)
    (h₂ : IsPiolaOf W P₂ F) : P₁ = P₂ :=
  dcontrCLM_injective (HasFDerivAt.unique h₁ h₂)

/-- The admissible deformation gradients `{F | det F > 0}` form an open set. -/
theorem isOpen_det_pos : IsOpen {F : Lin E | 0 < F.det} :=
  isOpen_lt continuous_const contDiff_det.continuous

/-- A stored energy is **frame-indifferent** if `W(Q F) = W(F)` for all rotations `Q` and all
admissible `F`. [Gurtin1981], §29. -/
def IsFrameIndifferent (W : Lin E → ℝ) : Prop :=
  ∀ Q ∈ Orth E, Q.det = 1 → ∀ F : Lin E, 0 < F.det → W (Q * F) = W F

/-- **Reduced form of frame-indifferent energies**: `W` is frame-indifferent iff it depends on
`F` only through `C = Fᵀ F`. [Gurtin1981], §29; [Ciarlet1988], Thm. 4.2-1. -/
theorem isFrameIndifferent_iff {W : Lin E → ℝ} :
    IsFrameIndifferent W ↔ ∃ Ŵ : Lin E → ℝ, ∀ F : Lin E, 0 < F.det → W F = Ŵ (rightCG F) := by
  constructor
  · intro hW
    refine ⟨fun C => W (CFC.sqrt C), fun F hF => ?_⟩
    have hU : IsUnit F := isUnit_iff_det_ne_zero.mpr hF.ne'
    have hR := polarRotation_mem_orth hU
    have hRdet := (det_polarRotation_eq_one_iff hU).mpr hF
    have hUdet : 0 < (rightStretch F).det :=
      det_pos_of_isStrictlyPositive (isStrictlyPositive_rightStretch hU)
    calc W F = W (polarRotation F * rightStretch F) := by rw [polarRotation_mul_rightStretch hU]
      _ = W (rightStretch F) := hW _ hR hRdet _ hUdet
      _ = W (CFC.sqrt (rightCG F)) := rfl
  · rintro ⟨Ŵ, hŴ⟩ Q hQ hQdet F hF
    have hQF : 0 < (Q * F).det := by rw [det_mul, hQdet, one_mul]; exact hF
    rw [hŴ _ hQF, hŴ _ hF, rightCG_orth_mul F hQ]

/-- For a frame-indifferent hyperelastic material the first Piola–Kirchhoff stress transforms as
`P(Q F) = Q P(F)` under rotations. [Gurtin1981], §29. -/
theorem IsFrameIndifferent.piola_rot_mul {W : Lin E → ℝ} {P : Lin E → Lin E}
    (hW : IsFrameIndifferent W) (hP : ∀ F : Lin E, 0 < F.det → IsPiolaOf W (P F) F)
    {Q : Lin E} (hQ : Q ∈ Orth E) (hQdet : Q.det = 1) {F : Lin E} (hF : 0 < F.det) :
    P (Q * F) = Q * P F := by
  have hQF : 0 < (Q * F).det := by rw [det_mul, hQdet, one_mul]; exact hF
  -- differentiate `F ↦ W(Q F)` in two ways
  have h1 : HasFDerivAt (fun G => W (Q * G))
      ((dcontrCLM (P (Q * F))).comp (ContinuousLinearMap.mul ℝ (Lin E) Q)) F :=
    (hP _ hQF).comp F (ContinuousLinearMap.mul ℝ (Lin E) Q).hasFDerivAt
  have h2 : HasFDerivAt (fun G => W (Q * G)) (dcontrCLM (P F)) F := by
    refine (hP F hF).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_det_pos.mem_nhds (show F ∈ {F : Lin E | 0 < F.det} from hF)]
      with G hG
    exact hW Q hQ hQdet G hG
  have key : ∀ H, P (Q * F) ⊡ (Q * H) = P F ⊡ H := fun H =>
    congrArg (fun L : Lin E →L[ℝ] ℝ => L H) (h1.unique h2)
  have hQt : Qᵀ * P (Q * F) = P F := eq_of_dcontr_eq fun H => by
    rw [← key H, dcontr_comm (Qᵀ * P (Q * F)) H, dcontr_comm (P (Q * F)) (Q * H),
      mul_dcontr_left]
  calc P (Q * F) = (Q * Qᵀ) * P (Q * F) := by rw [mul_transpose_self_of_mem_orth hQ, one_mul]
    _ = Q * P F := by rw [mul_assoc, hQt]

end Lin

end ContinuumMechanics
