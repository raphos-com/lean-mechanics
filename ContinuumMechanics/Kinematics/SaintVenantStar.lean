import ContinuumMechanics.Kinematics.SaintVenant
import ContinuumMechanics.Kinematics.PoincareStar

/-!
# Saint-Venant compatibility (sufficiency on star-shaped domains)

`Kinematics/SaintVenant` proves that the Saint-Venant compatibility conditions are sufficient for
a symmetric `C²` strain field to be the symmetric gradient of a displacement on an open **convex**
domain. Here we extend this to open domains that are **star-shaped** about some point `c`
(`StarConvex ℝ c Ω`), e.g. any body that can be seen entirely from one of its points.

The proof is the same classical two-step integration (rotation field `W` with `DW = ω`, then
displacement `u` with `∇u = ε + W`); the only change is that both integrations use the Poincaré
lemma for star-shaped open sets, `StarConvex.exists_forall_hasFDerivAt_of_fderiv_symmetric`
(`Kinematics/PoincareStar`), instead of the convex version.

## Main results

* `ContinuumMechanics.saintVenant_sufficient_of_starConvex`: compatibility conditions on an open
  star-shaped set imply `ε = sym ∇u` for some displacement `u`.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.6.
-/

open scoped InnerProductSpace ContinuumMechanics

noncomputable section

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open SaintVenant in
/-- **Saint-Venant compatibility** (sufficiency, star-shaped domains): on an open set `Ω`
star-shaped about some point `c`, a symmetric `C²` strain field satisfying the compatibility
conditions is the strain `sym ∇u` of a displacement. [Gurtin1981], §14. -/
theorem saintVenant_sufficient_of_starConvex {Ω : Set E} {c : E} (hΩ : StarConvex ℝ c Ω)
    (hΩo : IsOpen Ω) {ε : E → Lin E}
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
