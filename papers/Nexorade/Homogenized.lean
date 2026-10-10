import Nexorade.InPlane
import Nexorade.Plate

/-!
# The homogenized nexorade plate (static approach)

In the static approach ([GrecoLebeeDouthe2013], §2.2; [LebeeSab2013]) the complementary energy
density of the equivalent plate at macroscopic stresses `(N, M)` is the **minimum of the cell
complementary energy per unit area over the statically admissible fields with these averages**.
For the square nexorade this minimum is computed exactly:

* out of plane: admissible fields exist **only for hydrostatic moments** `M₁₁ = M₂₂`, `M₁₂ = 0`,
  and then `w*(M) = ½ d M²` (`d = Cell.compliance`);
* in plane: admissible fields exist **only for `N₁₂ = 0`**, and then
  `w*(N) = ½ A₁₁₁₁ (N₁₁² + N₂₂²)` (`A₂₂₁₁ = 0`).

So the equivalent plate is a degenerate Kirchhoff–Love plate: infinitely compliant in twist,
in deviatoric bending and in membrane shear.

## Main results

* `Cell.isLeast_outOfPlane` (with `Cell.M11_eq_M22` for the degeneracy).
* `Cell.isLeast_inPlane`, `Cell.N12_eq_zero_of_admissible`.

## References

* [GrecoLebeeDouthe2013] L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of
  reciprocal systems using homogenization techniques* (2013).
* [LebeeSab2013] A. Lebée, K. Sab, *Homogenization of a space frame as a thick plate*,
  Computers and Structures (2013).
-/

noncomputable section

namespace ContinuumMechanics.Nexorade.Cell

variable (c : Cell)

/-- **Out-of-plane homogenized energy**: `min {Π/A | admissible, M₁₁ = M} = ½ d M²`. -/
theorem isLeast_outOfPlane (M : ℝ) :
    IsLeast {e | ∃ f, c.Admissible f ∧ c.M11 f = M ∧ e = c.energy f / c.area}
      (c.compliance * M ^ 2 / 2) := by
  obtain ⟨hadm, hM⟩ := c.localization M
  refine ⟨⟨_, hadm, hM, ?_⟩, ?_⟩
  · rw [c.energy_eq hadm, hM]
  · rintro e ⟨f, hf, hfM, rfl⟩
    rw [c.energy_eq hf, hfM]

/-- **In-plane homogenized energy**: `min {Π/A | admissible, N₁₁ = n₁, N₂₂ = n₂}
= ½ A₁₁₁₁ (n₁² + n₂²)`. -/
theorem isLeast_inPlane {ES EI GS : ℝ} (hES : 0 < ES) (hEI : 0 < EI) (hGS : 0 < GS)
    (n₁ n₂ : ℝ) :
    IsLeast {e | ∃ F, InPlane.Admissible c F ∧ InPlane.N11 c F = n₁ ∧ InPlane.N22 c F = n₂ ∧
        e = InPlane.energy c ES EI GS F / c.area}
      (InPlane.compliance11 c ES EI GS * (n₁ ^ 2 + n₂ ^ 2) / 2) := by
  obtain ⟨hadm, h1, h2⟩ := InPlane.admissible_opt (c := c) n₁ n₂
  refine ⟨⟨_, hadm, h1, h2, (InPlane.energy_opt hES.ne' hEI.ne' hGS.ne' n₁ n₂).symm⟩, ?_⟩
  rintro e ⟨F, hF, hF1, hF2, rfl⟩
  rw [← InPlane.energy_opt hES.ne' hEI.ne' hGS.ne' n₁ n₂]
  have := InPlane.energy_opt_le hES hEI hGS hF
  rw [hF1, hF2] at this
  exact div_le_div_of_nonneg_right this c.area_pos.le

/-- **No membrane shear**: every admissible field has `N₁₂ = 0`. -/
theorem N12_eq_zero_of_admissible {F : InPlane} (hF : InPlane.Admissible c F) :
    InPlane.N12 c F = 0 := InPlane.N12_eq_zero hF

end ContinuumMechanics.Nexorade.Cell

end
