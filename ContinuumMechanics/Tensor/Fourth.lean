import ContinuumMechanics.Tensor.Spherical

/-!
# Fourth-order tensors

A **fourth-order tensor** is a linear map `Lin E → Lin E` ([Gurtin1981], §1.2; [Ciarlet1988],
§3.3); elasticity tensors `ℂ` are of this kind. We model them as `Lin4 E := Lin E →L[ℝ] Lin E`.

## Main definitions

* `Lin4.HasMinorSymm ℂ`: `ℂ A` is symmetric and `ℂ` vanishes on skew tensors.
* `Lin4.HasMajorSymm ℂ`: `ℂ A : B = A : ℂ B`.
* `Lin4.PosDefOnSym ℂ`: `ℂ A : A > 0` for symmetric `A ≠ 0`.
* `Lin4.symId` (`𝕀ˢʸᵐ`): `A ↦ sym A`; `Lin4.idDyad` (`I ⊗ I`): `A ↦ (tr A) I`.
* `Lin4.isotropic lam mu = lam I ⊗ I + 2 mu 𝕀ˢʸᵐ`, the isotropic elasticity tensor.

## Main results

* `Lin4.HasMinorSymm.apply_sym`: minor symmetry gives `ℂ A = ℂ (sym A)`.
* `Lin4.isotropic_hasMinorSymm`, `Lin4.isotropic_hasMajorSymm`.
* `Lin4.isotropic_dcontr_self`: `ℂ A : A = lam (tr A)² + 2 mu (A : A)` for symmetric `A`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §1.2.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §3.3.
-/

open Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Lin4 E`, the space of **fourth-order tensors**: linear maps `Lin E → Lin E`.
[Gurtin1981], §1.2. -/
abbrev Lin4 := Lin E →L[ℝ] Lin E

variable {E} [FiniteDimensional ℝ E]

namespace Lin4

open Lin

/-- **Minor symmetries**: `ℂ A` is always symmetric and `ℂ W = 0` for skew `W`; equivalently
`ℂᵢⱼₖₗ = ℂⱼᵢₖₗ = ℂᵢⱼₗₖ`. [Gurtin1981], §22; [Ciarlet1988], §3.3. -/
def HasMinorSymm (C : Lin4 E) : Prop :=
  (∀ A, C A ∈ Sym E) ∧ ∀ W ∈ Skw E, C W = 0

/-- **Major symmetry**: `ℂ A : B = A : ℂ B`; equivalently `ℂᵢⱼₖₗ = ℂₖₗᵢⱼ`.
[Gurtin1981], §22; [Ciarlet1988], §3.3. -/
def HasMajorSymm (C : Lin4 E) : Prop :=
  ∀ A B, C A ⊡ B = A ⊡ C B

/-- **Positive definiteness on symmetric tensors**: `ℂ A : A > 0` for symmetric `A ≠ 0`.
[Gurtin1981], §22. -/
def PosDefOnSym (C : Lin4 E) : Prop :=
  ∀ A ∈ Sym E, A ≠ 0 → 0 < C A ⊡ A

theorem HasMinorSymm.apply_sym {C : Lin4 E} (hC : C.HasMinorSymm) (A : Lin E) :
    C (sym A) = C A := by
  conv_rhs => rw [← sym_add_skw A]
  rw [map_add, hC.2 _ (skw_mem A), add_zero]

theorem HasMinorSymm.add {C D : Lin4 E} (hC : C.HasMinorSymm) (hD : D.HasMinorSymm) :
    (C + D).HasMinorSymm :=
  ⟨fun A => (Sym E).add_mem (hC.1 A) (hD.1 A), fun W hW => by
    rw [add_apply, hC.2 W hW, hD.2 W hW, add_zero]⟩

theorem HasMinorSymm.smul {C : Lin4 E} (hC : C.HasMinorSymm) (c : ℝ) : (c • C).HasMinorSymm :=
  ⟨fun A => (Sym E).smul_mem c (hC.1 A), fun W hW => by
    rw [smul_apply, hC.2 W hW, smul_zero]⟩

theorem HasMajorSymm.add {C D : Lin4 E} (hC : C.HasMajorSymm) (hD : D.HasMajorSymm) :
    (C + D).HasMajorSymm := fun A B => by
  simp only [add_apply, map_add, LinearMap.add_apply, hC A B, hD A B]

theorem HasMajorSymm.smul {C : Lin4 E} (hC : C.HasMajorSymm) (c : ℝ) : (c • C).HasMajorSymm :=
  fun A B => by
    simp only [smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hC A B]

/-- The **symmetric identity** `𝕀ˢʸᵐ : A ↦ sym A`. [Gurtin1981], §22. -/
noncomputable def symId : Lin4 E := LinearMap.toContinuousLinearMap sym

@[inherit_doc] scoped[ContinuumMechanics] notation "𝕀ˢʸᵐ" => Lin4.symId

/-- The fourth-order tensor `I ⊗ I : A ↦ (tr A) I`. [Gurtin1981], §22. -/
noncomputable def idDyad : Lin4 E := LinearMap.toContinuousLinearMap (tr.smulRight (1 : Lin E))

@[simp] theorem symId_apply (A : Lin E) : (𝕀ˢʸᵐ : Lin4 E) A = sym A := rfl

@[simp] theorem idDyad_apply (A : Lin E) : (idDyad : Lin4 E) A = tr A • (1 : Lin E) := rfl

theorem symId_hasMinorSymm : (𝕀ˢʸᵐ : Lin4 E).HasMinorSymm :=
  ⟨fun A => sym_mem A, fun _ hW => sym_eq_zero_of_mem_skw hW⟩

theorem symId_hasMajorSymm : (𝕀ˢʸᵐ : Lin4 E).HasMajorSymm := fun A B => by
  rw [symId_apply, symId_apply, dcontr_sym_of_mem_sym (sym_mem A) B, dcontr_comm A,
    dcontr_sym_of_mem_sym (sym_mem B) A, dcontr_comm]

theorem idDyad_hasMinorSymm : (idDyad : Lin4 E).HasMinorSymm :=
  ⟨fun A => (Sym E).smul_mem _ (mem_sym_iff.mpr (transpose_one)), fun W hW => by
    rw [idDyad_apply, tr_eq_zero_of_mem_skw hW, zero_smul]⟩

theorem idDyad_hasMajorSymm : (idDyad : Lin4 E).HasMajorSymm := fun A B => by
  rw [idDyad_apply, idDyad_apply, map_smul, map_smul, LinearMap.smul_apply, one_dcontr,
    dcontr_one, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The **isotropic elasticity tensor** `ℂ = λ I ⊗ I + 2μ 𝕀ˢʸᵐ`, with Lamé moduli `λ`, `μ`.
[Gurtin1981], §22; [Ciarlet1988], §3.8. -/
noncomputable def isotropic (lam mu : ℝ) : Lin4 E := lam • idDyad + (2 * mu) • 𝕀ˢʸᵐ

theorem isotropic_apply (lam mu : ℝ) (A : Lin E) :
    isotropic lam mu A = (lam * tr A) • (1 : Lin E) + (2 * mu) • sym A := by
  rw [isotropic, add_apply, smul_apply,
    smul_apply, idDyad_apply, symId_apply, smul_smul]

theorem isotropic_hasMinorSymm (lam mu : ℝ) : (isotropic lam mu : Lin4 E).HasMinorSymm :=
  (idDyad_hasMinorSymm.smul lam).add (symId_hasMinorSymm.smul _)

theorem isotropic_hasMajorSymm (lam mu : ℝ) : (isotropic lam mu : Lin4 E).HasMajorSymm :=
  (idDyad_hasMajorSymm.smul lam).add (symId_hasMajorSymm.smul _)

/-- For symmetric `A`: `ℂ A : A = λ (tr A)² + 2μ (A : A)`. [Gurtin1981], §22. -/
theorem isotropic_dcontr_self (lam mu : ℝ) {A : Lin E} (hA : A ∈ Sym E) :
    isotropic lam mu A ⊡ A = lam * tr A ^ 2 + 2 * mu * (A ⊡ A) := by
  rw [isotropic_apply, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, one_dcontr, sym_eq_self_of_mem hA, smul_eq_mul, smul_eq_mul]
  ring

end Lin4

section Examples

open Lin4

/-- `𝕀ˢʸᵐ` is the isotropic tensor with `λ = 0`, `μ = ½`. -/
example : (isotropic 0 (1 / 2) : Lin4 E) = 𝕀ˢʸᵐ := by
  ext1 A
  rw [isotropic_apply]
  simp

/-- A concrete isotropic material (steel, Lamé moduli in GPa) gives a minor- and major-symmetric
elasticity tensor. -/
example : (isotropic 121.15 80.77 : Lin4 E).HasMinorSymm ∧
    (isotropic 121.15 80.77 : Lin4 E).HasMajorSymm :=
  ⟨isotropic_hasMinorSymm _ _, isotropic_hasMajorSymm _ _⟩

end Examples

end ContinuumMechanics
