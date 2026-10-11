import ContinuumMechanics.Kinematics.Compatibility
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Saint-Venant compatibility (sufficiency on convex domains)

Let `Ω` be an open convex subset of a finite-dimensional inner product space `E` and `ε : E → Lin E`
a symmetric `C²` strain field satisfying the **Saint-Venant compatibility conditions** in `Ω`
(the form proved necessary in `Kinematics/Compatibility`):

`D²ε(c,d)a·b + D²ε(a,b)c·d - D²ε(a,c)b·d - D²ε(b,d)a·c = 0`.

Then `ε` is the strain of a displacement: there is `u` with `sym ∇u = ε` in `Ω`
(`saintVenant_sufficient`). With `saintVenant` this characterises compatible strains on convex
domains ([Gurtin1981], §14; [Ciarlet1988], §6.6).

The proof is the classical two-step integration, using Mathlib's Poincaré lemma for closed 1-forms
on convex sets (`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`):

1. the `Lin E`-valued 1-form `ω(c) a · b = Dε(a)c · b - Dε(b)c · a` (in components
   `Wᵢⱼ,ₖ = εᵢₖ,ⱼ - εⱼₖ,ᵢ`) is closed by the compatibility conditions, hence `ω = DW` for an
   infinitesimal rotation field `W`, which can be taken skew since `ω` is skew-valued;
2. the 1-form `ε + W` is then closed, hence `ε + W = ∇u`, and `sym ∇u = ε`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.6.
-/

open scoped InnerProductSpace ContinuumMechanics

noncomputable section

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace SaintVenant

/-- The transpose as a continuous linear map. -/
def transposeL : Lin E →L[ℝ] Lin E :=
  LinearMap.toContinuousLinearMap ((2 : ℝ) • (Lin.sym : Lin E →ₗ[ℝ] Lin E) - LinearMap.id)

theorem transposeL_apply (A : Lin E) : transposeL A = Aᵀ := by
  simp only [transposeL, LinearMap.coe_toContinuousLinearMap', LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Lin.sym_apply, smul_smul]
  norm_num

/-- `A ↦ A - Aᵀ`. -/
def skewL : Lin E →L[ℝ] Lin E := ContinuousLinearMap.id ℝ (Lin E) - transposeL

theorem skewL_apply (A : Lin E) : skewL A = A - Aᵀ := by
  simp [skewL, transposeL_apply]

/-- `T ↦ (c ↦ (a ↦ T(a)c) - (a ↦ T(a)c)ᵀ)`: the rotation-gradient form of a strain gradient. -/
def Φ : (E →L[ℝ] Lin E) →L[ℝ] (E →L[ℝ] Lin E) :=
  (ContinuousLinearMap.compL ℝ E (Lin E) (Lin E) skewL).comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap

theorem inner_Φ (T : E →L[ℝ] Lin E) (c a b : E) :
    ⟪Φ T c a, b⟫_ℝ = ⟪T a c, b⟫_ℝ - ⟪a, T b c⟫_ℝ := by
  simp [Φ, skewL_apply, inner_sub_left, Lin.inner_transpose_left]

theorem transpose_Φ (T : E →L[ℝ] Lin E) (c : E) : (Φ T c)ᵀ = -Φ T c := by
  have h : Φ T c = skewL (T.flip c) := rfl
  rw [h, skewL_apply, ← transposeL_apply, map_sub, transposeL_apply, transposeL_apply,
    Lin.transpose_transpose, neg_sub]

/-- The derivative of a symmetric-tensor-valued map is symmetric. -/
theorem transpose_fderiv {f : E → Lin E} (hf : Differentiable ℝ f) (hs : ∀ y, (f y)ᵀ = f y)
    (x d : E) : (fderiv ℝ f x d)ᵀ = fderiv ℝ f x d := by
  have he : (⇑transposeL ∘ f) = f := funext fun y => by
    rw [Function.comp_apply, transposeL_apply, hs]
  have h := (transposeL.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  rw [he] at h
  conv_rhs => rw [h, ContinuousLinearMap.comp_apply, transposeL_apply]

end SaintVenant

open SaintVenant in
/-- **Saint-Venant compatibility** (sufficiency): on an open convex set `Ω`, a symmetric `C²`
strain field satisfying the compatibility conditions is the strain `sym ∇u` of a displacement.
[Gurtin1981], §14. -/
theorem saintVenant_sufficient {Ω : Set E} (hΩ : Convex ℝ Ω) (hΩo : IsOpen Ω) {ε : E → Lin E}
    (hε : ContDiff ℝ 2 ε) (hs : ∀ x, (ε x)ᵀ = ε x)
    (hc : ∀ x ∈ Ω, ∀ a b c d : E,
      ⟪fderiv ℝ (fderiv ℝ ε) x c d a, b⟫_ℝ + ⟪fderiv ℝ (fderiv ℝ ε) x a b c, d⟫_ℝ -
        ⟪fderiv ℝ (fderiv ℝ ε) x a c b, d⟫_ℝ - ⟪fderiv ℝ (fderiv ℝ ε) x b d a, c⟫_ℝ = 0) :
    ∃ u : E → E, ∀ x ∈ Ω, DifferentiableAt ℝ u x ∧ strainField u x = ε x := by
  have hε1 : Differentiable ℝ ε := hε.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ ε) :=
    (hε.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set H := fderiv ℝ (fderiv ℝ ε) with hH
  -- symmetries of `D²ε`
  have hHs : ∀ x p q, H x p q = H x q p := fun x p q =>
    (hε.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) p q
  have hH' : ∀ x p q, fderiv ℝ (fun y => fderiv ℝ ε y q) x p = H x p q := fun x p q => by
    have h := ((hD x).hasFDerivAt.clm_apply (hasFDerivAt_const q x))
    rw [h.fderiv, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have hHT : ∀ x p q r s, ⟪H x p q r, s⟫_ℝ = ⟪H x p q s, r⟫_ℝ := fun x p q r s => by
    have h := transpose_fderiv (f := fun y => fderiv ℝ ε y q)
      (hD.clm_apply (differentiable_const q)) (fun y => transpose_fderiv hε1 hs y q) x p
    rw [hH'] at h
    rw [← Lin.inner_transpose_right, h, real_inner_comm]
  have hDT : ∀ x p r s, ⟪fderiv ℝ ε x p r, s⟫_ℝ = ⟪fderiv ℝ ε x p s, r⟫_ℝ := fun x p r s => by
    rw [← Lin.inner_transpose_right, transpose_fderiv hε1 hs, real_inner_comm]
  -- step 1: the rotation gradient `ω = Φ(Dε)` is closed, `ω = DW`
  set ω : E → E →L[ℝ] Lin E := fun x => Φ (fderiv ℝ ε x) with hω
  have hωd : ∀ x, HasFDerivAt ω (Φ.comp (H x)) x := fun x => by
    have h := HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := E →L[ℝ] Lin E) (G := E →L[ℝ] Lin E) x
      Φ.hasFDerivAt (hD x).hasFDerivAt
    exact h
  obtain ⟨W, hW⟩ := hΩ.exists_forall_hasFDerivAt_of_fderiv_symmetric hΩo
    (fun x _ => (hωd x).differentiableAt.differentiableWithinAt) fun x hx p q => by
      rw [(hωd x).fderiv]
      ext a
      refine ext_inner_right ℝ fun b => ?_
      simp only [ContinuousLinearMap.comp_apply]
      rw [inner_Φ, inner_Φ]
      have h := hc x hx q b a p
      have e1 : ⟪H x a p q, b⟫_ℝ = ⟪H x p a q, b⟫_ℝ := by rw [hHs x a p]
      have e2 : ⟪H x q b a, p⟫_ℝ = ⟪a, H x q b p⟫_ℝ := by rw [hHT, real_inner_comm]
      have e3 : ⟪H x q a b, p⟫_ℝ = ⟪H x q a p, b⟫_ℝ := hHT x q a b p
      have e4 : ⟪H x b p q, a⟫_ℝ = ⟪a, H x p b q⟫_ℝ := by rw [hHs x b p, real_inner_comm]
      linarith
  -- `W` can be taken skew
  set S : Lin E →L[ℝ] Lin E := LinearMap.toContinuousLinearMap (Lin.skw : Lin E →ₗ[ℝ] Lin E)
  have hW' : ∀ x ∈ Ω, HasFDerivAt (fun y => S (W y)) (ω x) x := fun x hx => by
    have h := HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := Lin E) (G := Lin E) x S.hasFDerivAt
      (hW x hx)
    have e : S.comp (ω x) = ω x := by
      ext c : 1
      simp only [ContinuousLinearMap.comp_apply, S, LinearMap.coe_toContinuousLinearMap']
      exact Lin.skw_eq_self_of_mem (Lin.mem_skw_iff.mpr (transpose_Φ _ c))
    rw [e] at h
    exact h
  -- step 2: `ε + W` is closed, `ε + W = ∇u`
  have hβ : ∀ x ∈ Ω, HasFDerivAt (fun y => ε y + S (W y)) (fderiv ℝ ε x + ω x) x :=
    fun x hx => (hε1 x).hasFDerivAt.add (hW' x hx)
  obtain ⟨u, hu⟩ := hΩ.exists_forall_hasFDerivAt_of_fderiv_symmetric hΩo
    (fun x hx => (hβ x hx).differentiableAt.differentiableWithinAt) fun x hx p q => by
      rw [(hβ x hx).fderiv]
      refine ext_inner_right ℝ fun b => ?_
      simp only [add_apply, inner_add_left]
      rw [inner_Φ, inner_Φ, real_inner_comm _ q, real_inner_comm _ p, hDT x b p q]
      ring
  refine ⟨u, fun x hx => ⟨(hu x hx).differentiableAt, ?_⟩⟩
  rw [strainField, (hu x hx).fderiv, map_add, Lin.sym_eq_self_of_mem (Lin.mem_sym_iff.mpr (hs x)),
    Lin.sym_eq_zero_of_mem_skw (by simpa [S] using Lin.skw_mem (W x)), add_zero]

end ContinuumMechanics
