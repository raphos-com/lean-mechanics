import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import ContinuumMechanics.Elastostatics.Basic

/-!
# Saint-Venant compatibility (necessity)

A strain field `ε` is **compatible** if it is the symmetric gradient of a displacement. In
components, a compatible `C²` strain satisfies the Saint-Venant conditions
`εᵢⱼ,ₖₗ + εₖₗ,ᵢⱼ - εᵢₖ,ⱼₗ - εⱼₗ,ᵢₖ = 0`, i.e. `curl curl ε = 0` in 3D ([Gurtin1981], §13;
[Ciarlet1988], §6.6).

We state and prove necessity coordinate-free and in any dimension: for `u ∈ C³` and
`ε = sym ∇u`, with `D²ε(c, d) ∈ Lin E` the second derivative,

`D²ε(c,d)a · b + D²ε(a,b)c · d - D²ε(a,c)b · d - D²ε(b,d)a · c = 0`  for all `a, b, c, d`.

The proof only uses the full symmetry of `D³u`, obtained from the symmetry of second derivatives
(`ContDiffAt.isSymmSndFDerivAt`) applied to `u` and to `∇u`.

Sufficiency (on simply connected bodies) needs a Poincaré lemma that Mathlib does not yet have; it
is recorded in `GAPS.md`.

## Main results

* `ContinuumMechanics.fderiv3_comm₁₂`, `fderiv3_comm₂₃`: symmetry of `D³u`.
* `ContinuumMechanics.fderiv_fderiv_strainField`: `D²ε(c, d) = sym (D³u(c, d))`.
* `ContinuumMechanics.saintVenant`: the compatibility conditions.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §13.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.6.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u : E → E}

omit [FiniteDimensional ℝ E] in
/-- Symmetry of `D³u` in its first two arguments. -/
theorem fderiv3_comm₁₂ (hu : ContDiff ℝ 3 u) (x a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x c a b = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x a c b := by
  have hg : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  rw [(hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) c a]

omit [FiniteDimensional ℝ E] in
/-- Symmetry of `D³u` in its last two arguments. -/
theorem fderiv3_comm₂₃ (hu : ContDiff ℝ 3 u) (x a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x c a b = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x c b a := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ (fderiv ℝ u)) := h1.differentiable one_ne_zero
  have key : ∀ p q : E, fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y p q) x c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x c p q := fun p q => by
    have h := ((hD x).hasFDerivAt.clm_apply (hasFDerivAt_const p x)).clm_apply
      (hasFDerivAt_const q x)
    rw [h.fderiv]
    simp
  have hsym : (fun y => fderiv ℝ (fderiv ℝ u) y a b) = fun y => fderiv ℝ (fderiv ℝ u) y b a :=
    funext fun y => (hu.contDiffAt (x := y)).isSymmSndFDerivAt (by simp; norm_num) a b
  rw [← key, ← key, hsym]

/-- The second derivative of the strain: `D²ε(c, d) = sym (D³u(c, d))`. -/
theorem fderiv_fderiv_strainField (hu : ContDiff ℝ 3 u) (x c d : E) :
    fderiv ℝ (fderiv ℝ (strainField u)) x c d =
      Lin.sym (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x c d) := by
  set S : (E →L[ℝ] E) →L[ℝ] Lin E :=
    LinearMap.toContinuousLinearMap (Lin.sym : Lin E →ₗ[ℝ] Lin E)
  have h2 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := h2.fderiv_right (by norm_num)
  have hε : fderiv ℝ (strainField u) = fun y => S.comp (fderiv ℝ (fderiv ℝ u) y) :=
    funext fun y => by
    have := (S.hasFDerivAt.comp y ((h2.differentiable (by norm_num)) y).hasFDerivAt).fderiv
    exact this
  rw [hε]
  have h := (hasFDerivAt_const S x).clm_comp ((h1.differentiable one_ne_zero) x).hasFDerivAt
  rw [h.fderiv]
  simp [S]

/-- **Saint-Venant compatibility** (necessity): the strain `ε = sym ∇u` of a `C³` displacement
satisfies `D²ε(c,d)a·b + D²ε(a,b)c·d - D²ε(a,c)b·d - D²ε(b,d)a·c = 0`, the coordinate-free form of
`εᵢⱼ,ₖₗ + εₖₗ,ᵢⱼ - εᵢₖ,ⱼₗ - εⱼₗ,ᵢₖ = 0` (`curl curl ε = 0`). [Gurtin1981], §13. -/
theorem saintVenant (hu : ContDiff ℝ 3 u) (x a b c d : E) :
    ⟪fderiv ℝ (fderiv ℝ (strainField u)) x c d a, b⟫_ℝ +
        ⟪fderiv ℝ (fderiv ℝ (strainField u)) x a b c, d⟫_ℝ -
      ⟪fderiv ℝ (fderiv ℝ (strainField u)) x a c b, d⟫_ℝ -
        ⟪fderiv ℝ (fderiv ℝ (strainField u)) x b d a, c⟫_ℝ = 0 := by
  have s12 := fderiv3_comm₁₂ hu x
  have s23 := fderiv3_comm₂₃ hu x
  have hs : ∀ p q r s : E, ⟪Lin.sym (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x p q) r, s⟫_ℝ =
      2⁻¹ * (⟪fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x p q r, s⟫_ℝ +
        ⟪fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x p q s, r⟫_ℝ) :=
    fun p q r s => by
      rw [Lin.sym_apply, smul_apply, add_apply,
        real_inner_smul_left, inner_add_left, Lin.inner_transpose_left, real_inner_comm r]
  simp only [fderiv_fderiv_strainField hu, hs]
  set T := fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x
  have e1 : T c d a = T a c d := by rw [s23, s12]
  have e2 : T c d b = T b d c := by rw [s12, s23, s12]
  have e3 : T a b c = T a c b := s23 b c a
  have e4 : T a b d = T b d a := by rw [s12, s23]
  rw [e1, e2, e3, e4]
  ring

end ContinuumMechanics
