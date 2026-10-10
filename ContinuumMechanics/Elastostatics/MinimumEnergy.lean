import ContinuumMechanics.Elastostatics.Basic

/-!
# The principle of minimum potential energy

For the mixed problem of linear elastostatics with body force `b` and prescribed surface traction
`s`, the **total potential energy** of a displacement `v` is

`Φ(v) = U(v) - ∫_B v · b - ∫_∂B v · s`.

If `u` is a `C²` equilibrium displacement, `div σ(u) + b = 0` in `B`, and a competitor `v` is
*kinematically admissible* in the sense that `(v - u) · σ(u) n = (v - u) · s` on `∂B` (on the
displacement part `v = u`, on the traction part `σ(u) n = s`), then

`Φ(v) = Φ(u) + U(v - u) ≥ Φ(u)`,

with equality exactly when `v - u` is an infinitesimal rigid displacement (for positive definite
`ℂ` on a connected body). [Gurtin1981], §34; [Ciarlet1988], §6.2.

## Main results

* `potentialEnergy_eq_add`: `Φ(v) = Φ(u) + U(v - u)`.
* `potentialEnergy_le`: **minimum potential energy** `Φ(u) ≤ Φ(v)`.
* `rigid_of_potentialEnergy_eq`: equality forces `v - u` to be rigid.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §34.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.2.
-/

open MeasureTheory Set
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (B : DivergenceRegion E)

/-- The **total potential energy** `Φ(v) = U(v) - ∫_B v · b - ∫_∂B v · s` for body force `b` and
surface traction `s`. [Gurtin1981], §34. -/
noncomputable def potentialEnergy (C : Lin4 E) (b s v : E → E) : ℝ :=
  strainEnergy B C v - (∫ x in B.carrier, ⟪v x, b x⟫_ℝ) - ∫ x, ⟪v x, s x⟫_ℝ ∂B.surface

variable {C : Lin4 E} {b s u v : E → E}

/-- `Φ(v) = Φ(u) + U(v - u)` for an equilibrium displacement `u` and an admissible `v`.
[Gurtin1981], §34. -/
theorem potentialEnergy_eq_add (hCm : C.HasMinorSymm) (hCM : C.HasMajorSymm)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hb : Continuous b)
    (heq : ∀ x ∈ B.carrier, tdiv (stressField C u) x + b x = 0)
    (hsu : Integrable (fun x => ⟪u x, s x⟫_ℝ) B.surface)
    (hsv : Integrable (fun x => ⟪v x, s x⟫_ℝ) B.surface)
    (hbdry : ∀ᵐ x ∂B.surface,
      ⟪v x - u x, stressField C u x (B.normal x)⟫_ℝ = ⟪v x - u x, s x⟫_ℝ) :
    potentialEnergy B C b s v = potentialEnergy B C b s u + strainEnergy B C (v - u) := by
  have hw : ContDiff ℝ 2 (v - u) := hv.sub hu
  have du : ∀ x, DifferentiableAt ℝ u x := fun x => (hu.differentiable (by norm_num)) x
  have dv : ∀ x, DifferentiableAt ℝ v x := fun x => (hv.differentiable (by norm_num)) x
  have hεv : ∀ x, strainField v x = strainField u x + strainField (v - u) x := fun x => by
    rw [strainField_sub (dv x) (du x), add_sub_cancel]
  have εu := (contDiff_strainField hu).continuous
  have εw := (contDiff_strainField hw).continuous
  -- pointwise expansion of the energy density
  have hpt : ∀ x, strainField v x ⊡ C (strainField v x) =
      strainField u x ⊡ C (strainField u x) + 2 * (stressField C u x ⊡ strainField (v - u) x)
        + strainField (v - u) x ⊡ C (strainField (v - u) x) := fun x => by
    rw [hεv, stressField]
    simp only [map_add, LinearMap.add_apply]
    linear_combination Lin.dcontr_comm (strainField (v - u) x) (C (strainField u x)) -
      hCM (strainField u x) (strainField (v - u) x)
  -- the work identity for `σ(u)` tested with `v - u`
  have hwork := work_identity B (contDiff_stressField C hu) (fun x => hCm.1 _) hb heq
    (hw.of_le one_le_two)
  have hsurf : ∫ x, ⟪(v - u) x, stressField C u x (B.normal x)⟫_ℝ ∂B.surface =
      (∫ x, ⟪v x, s x⟫_ℝ ∂B.surface) - ∫ x, ⟪u x, s x⟫_ℝ ∂B.surface := by
    rw [← integral_sub hsv hsu]
    refine integral_congr_ae (hbdry.mono fun x hx => ?_)
    simp only [Pi.sub_apply, hx, inner_sub_left]
  have hvol : ∫ x in B.carrier, ⟪(v - u) x, b x⟫_ℝ =
      (∫ x in B.carrier, ⟪v x, b x⟫_ℝ) - ∫ x in B.carrier, ⟪u x, b x⟫_ℝ := by
    rw [← integral_sub (B.integrableOn_real (hv.continuous.inner hb))
      (B.integrableOn_real (hu.continuous.inner hb))]
    simp only [Pi.sub_apply, inner_sub_left]
  rw [hsurf, hvol] at hwork
  -- integrate the expansion
  have i1 : IntegrableOn (fun x => strainField u x ⊡ C (strainField u x)) B.carrier :=
    B.integrableOn_real (εu.dcontr (C.continuous.comp εu))
  have i2 : IntegrableOn (fun x => 2 * (stressField C u x ⊡ strainField (v - u) x)) B.carrier :=
    B.integrableOn_real (((C.continuous.comp εu).dcontr εw).const_mul (2 : ℝ))
  have i3 : IntegrableOn (fun x => strainField (v - u) x ⊡ C (strainField (v - u) x))
      B.carrier := B.integrableOn_real (εw.dcontr (C.continuous.comp εw))
  have i12 : IntegrableOn (fun x => strainField u x ⊡ C (strainField u x)
      + 2 * (stressField C u x ⊡ strainField (v - u) x)) B.carrier := i1.add i2
  have hU : strainEnergy B C v = strainEnergy B C u + strainEnergy B C (v - u)
      + ∫ x in B.carrier, stressField C u x ⊡ strainField (v - u) x := by
    simp only [strainEnergy, hpt]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul]
    ring
  simp only [potentialEnergy]
  rw [hU, hwork]
  ring

/-- **Principle of minimum potential energy**: an equilibrium displacement minimises the total
potential energy over kinematically admissible displacements. [Gurtin1981], §34;
[Ciarlet1988], Thm. 6.2-1. -/
theorem potentialEnergy_le (hCm : C.HasMinorSymm) (hCM : C.HasMajorSymm) (hpos : C.PosDefOnSym)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hb : Continuous b)
    (heq : ∀ x ∈ B.carrier, tdiv (stressField C u) x + b x = 0)
    (hsu : Integrable (fun x => ⟪u x, s x⟫_ℝ) B.surface)
    (hsv : Integrable (fun x => ⟪v x, s x⟫_ℝ) B.surface)
    (hbdry : ∀ᵐ x ∂B.surface,
      ⟪v x - u x, stressField C u x (B.normal x)⟫_ℝ = ⟪v x - u x, s x⟫_ℝ) :
    potentialEnergy B C b s u ≤ potentialEnergy B C b s v := by
  rw [potentialEnergy_eq_add B hCm hCM hu hv hb heq hsu hsv hbdry]
  linarith [strainEnergy_nonneg B hpos (v - u)]

/-- **Equality case**: if an admissible `v` has the same potential energy as the equilibrium
displacement `u`, then `v - u` is an infinitesimal rigid displacement. [Gurtin1981], §34. -/
theorem rigid_of_potentialEnergy_eq (hCm : C.HasMinorSymm) (hCM : C.HasMajorSymm)
    (hpos : C.PosDefOnSym) (hΩ : IsOpen B.carrier) (hconn : IsPreconnected B.carrier)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hb : Continuous b)
    (heq : ∀ x ∈ B.carrier, tdiv (stressField C u) x + b x = 0)
    (hsu : Integrable (fun x => ⟪u x, s x⟫_ℝ) B.surface)
    (hsv : Integrable (fun x => ⟪v x, s x⟫_ℝ) B.surface)
    (hbdry : ∀ᵐ x ∂B.surface,
      ⟪v x - u x, stressField C u x (B.normal x)⟫_ℝ = ⟪v x - u x, s x⟫_ℝ)
    (hΦ : potentialEnergy B C b s v = potentialEnergy B C b s u) :
    ∃ (a : E) (W : Lin E), W ∈ Skw E ∧ ∀ x ∈ B.carrier, v x - u x = a + W x := by
  rw [potentialEnergy_eq_add B hCm hCM hu hv hb heq hsu hsv hbdry, add_eq_left] at hΦ
  simpa using rigid_of_strainEnergy_eq_zero B hpos hΩ hconn (hv.sub hu) hΦ

end ContinuumMechanics
