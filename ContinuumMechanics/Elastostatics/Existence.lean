import ContinuumMechanics.Elastostatics.H10
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Existence and uniqueness for clamped isotropic linear elastostatics

Let `Ω ⊆ ℝⁿ` be bounded and let `H¹₀(Ω; ℝⁿ)` be the Sobolev space of `Elastostatics.H10`
(the closure of the graphs `u ↦ (u, ∇u)` of smooth fields compactly supported in `Ω`). For Lamé
constants `μ > 0`, `λ ≥ 0`, the weak problem of isotropic linear elastostatics with the body
clamped on the whole boundary is

`find U ∈ H¹₀(Ω; ℝⁿ):  a(U, V) = 2μ⟪ε(U), ε(V)⟫ + λ⟪div U, div V⟫ = ℓ(V)`  for all `V`,

for a continuous linear load `ℓ` (e.g. `ℓ(V) = ⟪f, V⟫_{L²}` for a body force `f ∈ L²`).

Korn's inequality (`Sobolev.energy_coercive`) bounds only the gradient part `‖∇U‖` of the `H¹`
norm. The missing ingredient is the **Poincaré inequality** `‖U‖_{L²} ≤ 2R ‖∇U‖_{L²}` for `Ω`
contained in a slab `{|xⱼ| ≤ R}` (`Sobolev.poincare`). For a smooth compactly supported `f`
vanishing outside the slab it follows from one integration by parts against the coordinate `xⱼ`
and Cauchy–Schwarz,

`∫ f² = ∫ f² ∂ⱼxⱼ = -2 ∫ (xⱼ f) ∂ⱼf ≤ 2R ‖f‖ ‖∂ⱼf‖`,

(`Sobolev.poincare_scalar`) and it extends to `H¹₀(Ω; ℝⁿ)` by density. Korn and Poincaré
together make `a` coercive for the full `H¹` norm, `a(U, U) ≥ μ/(1 + 4R²) ‖U‖²`
(`Sobolev.energy_coercive_H10`), and the Lax–Milgram theorem (Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`) gives well-posedness.

The Lax–Milgram step is carried out for an abstract Lamé form `a(u, v) = 2μ⟪ε u, ε v⟫ + λ⟪d u, d v⟫`
on a Hilbert space (`Sobolev.lameForm`) and then specialised to `H¹₀(Ω; ℝⁿ)`.

## Main results

* `Sobolev.poincare`: `‖disp U‖² ≤ 4R² ‖∇U‖²` on `H¹₀(Ω; ℝⁿ)` for `Ω ⊆ {|xⱼ| ≤ R}`.
* `Sobolev.energy_coercive_H10`: `μ/(1 + 4R²) ‖U‖² ≤ 2μ‖ε(U)‖² + λ‖div U‖²` on `H¹₀(Ω; ℝⁿ)`.
* `Sobolev.existsUnique_weak`: for bounded `Ω`, `μ > 0`, `λ ≥ 0` and every continuous linear `ℓ`,
  the weak problem has a unique solution in `H¹₀(Ω; ℝⁿ)`.
* `Sobolev.existsUnique_clamped`: the same for a body force `f ∈ L²(ℝⁿ)ⁿ`.
* `Sobolev.isMinOn_totalEnergy`, `Sobolev.eq_of_totalEnergy_eq`: the weak solution is the unique
  minimiser of the total potential energy `J(V) = ½ a(V, V) - ℓ(V)`.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.3.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §9.4 and Cor. 9.19.
* [Evans2010] L. C. Evans, *Partial Differential Equations*, §6.2.2 (Lax–Milgram).
-/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace ContinuumMechanics.Sobolev

open Korn

variable {n : ℕ}

/-! ### The Poincaré inequality -/

/-- The coordinate function `x ↦ xⱼ` has `∂ⱼ xⱼ = 1`. -/
theorem pd_coord (j : Fin n) (x : Fin n → ℝ) : pd (fun y => y j) j x = 1 := by
  simp [pd, (hasFDerivAt_apply j x).fderiv]

/-- Chain rule for the square: `∂ⱼ (f²) = 2 f ∂ⱼ f`. -/
theorem pd_sq {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) (j : Fin n) (x : Fin n → ℝ) :
    pd (fun y => f y ^ 2) j x = 2 * f x * pd f j x := by
  have := ((hf x).hasFDerivAt.pow 2).fderiv
  simp only [pd]
  rw [this]
  simp

/-- For square-integrable `f`, `g`, the integral `∫ f g` is the `L²` inner product. -/
theorem integral_inner_toL2 {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : ∫ x, f x * g x = ⟪toL2 f, toL2 g⟫_ℝ := by
  rw [L2.inner_def, toL2_of_memLp hf, toL2_of_memLp hg]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

/-- **Poincaré inequality in a slab** for a scalar `C¹` function with compact support:
if `f` vanishes outside the slab `{|xⱼ| ≤ R}`, then `∫ f² ≤ 4R² ∫ (∂ⱼf)²`.

Proof: integrating by parts against the coordinate `xⱼ` (with `∂ⱼxⱼ = 1`),
`∫ f² = -2 ∫ (xⱼ f) ∂ⱼf ≤ 2 ‖xⱼ f‖ ‖∂ⱼf‖ ≤ 2R ‖f‖ ‖∂ⱼf‖`. -/
theorem poincare_scalar {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (j : Fin n) {R : ℝ} (hs : ∀ x, f x ≠ 0 → |x j| ≤ R) :
    ‖toL2 f‖ ^ 2 ≤ 4 * R ^ 2 * ‖toL2 (pd f j)‖ ^ 2 := by
  set φ : (Fin n → ℝ) → ℝ := fun x => x j * f x with hφ
  have cf := hf.continuous
  have cφ : Continuous φ := (continuous_apply j).mul cf
  have sφ : HasCompactSupport φ := hc.mul_left
  have mφ : MemLp φ 2 volume := cφ.memLp_of_hasCompactSupport sφ
  have mf : MemLp f 2 volume := cf.memLp_of_hasCompactSupport hc
  have md : MemLp (pd f j) 2 volume :=
    (continuous_pd hf j).memLp_of_hasCompactSupport (hasCompactSupport_pd hc j)
  -- integration by parts against the coordinate `x ↦ xⱼ`
  have hsq : ContDiff ℝ 1 fun x => f x ^ 2 := hf.pow 2
  have hsqc : HasCompactSupport fun x => f x ^ 2 :=
    hc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have ibp := integral_mul_pd hsq (contDiff_apply ℝ ℝ j) hsqc j
  simp only [pd_coord, mul_one, pd_sq (hf.differentiable one_ne_zero)] at ibp
  have e1 : ∫ x, f x ^ 2 = -(2 * ∫ x, φ x * pd f j x) := by
    rw [ibp, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hφ]
    ring
  have hA : ‖toL2 f‖ ^ 2 ≤ 2 * ‖toL2 φ‖ * ‖toL2 (pd f j)‖ := by
    rw [norm_toL2_sq mf, e1, integral_inner_toL2 mφ md, mul_assoc]
    have := abs_real_inner_le_norm (toL2 φ) (toL2 (pd f j))
    have := neg_abs_le ⟪toL2 φ, toL2 (pd f j)⟫_ℝ
    linarith
  have hB : ‖toL2 φ‖ ^ 2 ≤ R ^ 2 * ‖toL2 f‖ ^ 2 := by
    rw [norm_toL2_sq mf, norm_toL2_sq mφ, ← integral_const_mul]
    refine integral_mono (integrable_sq cφ sφ) ((integrable_sq cf hc).const_mul _) fun x => ?_
    simp only [hφ]
    by_cases h : f x = 0
    · simp [h]
    · have h1 := hs x h
      have h2 : x j ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hB' : ‖toL2 φ‖ ≤ |R| * ‖toL2 f‖ := by
    have h : ‖toL2 φ‖ ^ 2 ≤ (|R| * ‖toL2 f‖) ^ 2 := by rw [mul_pow, sq_abs]; exact hB
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  set A := ‖toL2 f‖
  set D := ‖toL2 (pd f j)‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  have h2 : A ^ 2 ≤ 2 * |R| * A * D := by
    nlinarith [mul_le_mul_of_nonneg_right hB' hD0]
  rcases hA0.eq_or_lt with h0 | h0
  · rw [← h0]
    nlinarith [sq_nonneg (R * D)]
  · have h3 : A ≤ 2 * |R| * D := by nlinarith
    calc A ^ 2 ≤ (2 * |R| * D) ^ 2 := pow_le_pow_left₀ hA0 h3 2
      _ = 4 * R ^ 2 * D ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring

variable {Ω : Set (Fin n → ℝ)}

/-- Poincaré inequality `‖U‖² ≤ 4R² ‖∇U‖²` (displacement part) for the graph of a test field
supported in `Ω ⊆ {|xⱼ| ≤ R}`. -/
theorem poincare_graph (j : Fin n) {R : ℝ} (hΩ : Ω ⊆ {x | |x j| ≤ R}) (u : testFields Ω) :
    ‖disp (graph Ω u)‖ ^ 2 ≤ 4 * R ^ 2 * ‖grad (graph Ω u)‖ ^ 2 := by
  rw [norm_mat_sq, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hs : ∀ x, u.1 i x ≠ 0 → |x j| ≤ R := fun x hx =>
    hΩ ((u.2 i).2.2 (subset_tsupport _ hx))
  calc ‖disp (graph Ω u) i‖ ^ 2 = ‖toL2 (u.1 i)‖ ^ 2 := rfl
    _ ≤ 4 * R ^ 2 * ‖toL2 (pd (u.1 i) j)‖ ^ 2 :=
      poincare_scalar ((u.2 i).1.of_le (by simp)) (u.2 i).2.1 j hs
    _ = 4 * R ^ 2 * ‖grad (graph Ω u) i j‖ ^ 2 := rfl
    _ ≤ 4 * R ^ 2 * ∑ k, ‖grad (graph Ω u) i k‖ ^ 2 := by
      gcongr
      exact Finset.single_le_sum (f := fun k => ‖grad (graph Ω u) i k‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)

/-- **Poincaré inequality on `H¹₀(Ω; ℝⁿ)`** for `Ω` contained in the slab `{|xⱼ| ≤ R}`:
`‖disp U‖² ≤ 4R² ‖∇U‖²`, extended by density from the test fields. -/
theorem poincare (j : Fin n) {R : ℝ} (hΩ : Ω ⊆ {x | |x j| ≤ R}) {U : G n} (hU : U ∈ H10 Ω) :
    ‖disp U‖ ^ 2 ≤ 4 * R ^ 2 * ‖grad U‖ ^ 2 := by
  have hcl : IsClosed {V : G n | ‖disp V‖ ^ 2 ≤ 4 * R ^ 2 * ‖grad V‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub : ((LinearMap.range (graph Ω) : Submodule ℝ (G n)) : Set (G n)) ⊆
      {V : G n | ‖disp V‖ ^ 2 ≤ 4 * R ^ 2 * ‖grad V‖ ^ 2} := by
    rintro _ ⟨u, rfl⟩
    exact poincare_graph j hΩ u
  have hU' : U ∈ closure ((LinearMap.range (graph Ω) : Submodule ℝ (G n)) : Set (G n)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hU
  exact closure_minimal hsub hcl hU'

/-- A bounded set lies in a slab `{|x₀| ≤ R}`. -/
theorem exists_slab [NeZero n] (hΩ : Bornology.IsBounded Ω) :
    ∃ R : ℝ, Ω ⊆ {x | |x 0| ≤ R} := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hΩ
  refine ⟨R, fun x hx => ?_⟩
  have h := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact (Real.norm_eq_abs (x 0) ▸ norm_le_pi_norm x 0).trans h

/-- The `H¹` norm: `‖U‖² = ‖disp U‖² + ‖∇U‖²`. -/
theorem norm_sq_eq (U : G n) : ‖U‖ ^ 2 = ‖disp U‖ ^ 2 + ‖grad U‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 U

/-- **Coercivity of the Lamé energy in the full `H¹` norm** on `H¹₀(Ω; ℝⁿ)`, for `Ω` in the
slab `{|xⱼ| ≤ R}`: `μ/(1 + 4R²) ‖U‖² ≤ 2μ‖ε(U)‖² + λ‖div U‖²` (Korn + Poincaré). -/
theorem energy_coercive_H10 {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) (j : Fin n) {R : ℝ}
    (hΩ : Ω ⊆ {x | |x j| ≤ R}) {U : G n} (hU : U ∈ H10 Ω) :
    μ / (1 + 4 * R ^ 2) * ‖U‖ ^ 2 ≤ energy μ lam U := by
  have hp := poincare j hΩ hU
  have he := energy_coercive (lam := lam) hμ hlam hU
  have hpos : 0 < 1 + 4 * R ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos, norm_sq_eq]
  have h1 : μ * (‖disp U‖ ^ 2 + ‖grad U‖ ^ 2) ≤ μ * ((1 + 4 * R ^ 2) * ‖grad U‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hμ.le
  nlinarith [sq_nonneg ‖grad U‖]

/-! ### Lax–Milgram for an abstract Lamé form -/

section Abstract

variable {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (ε : V →L[ℝ] E) (d : V →L[ℝ] F) (μ lam : ℝ)

/-- The abstract Lamé bilinear form `a(u, v) = 2μ⟪ε u, ε v⟫ + λ⟪d u, d v⟫` built from a
"strain" map `ε` and a "divergence" map `d`. -/
def lameForm : V →L[ℝ] V →L[ℝ] ℝ :=
  (2 * μ) • (innerSL ℝ (E := E)).bilinearComp ε ε + lam • (innerSL ℝ (E := F)).bilinearComp d d

/-- Evaluation of the Lamé form. -/
theorem lameForm_apply (u v : V) :
    lameForm ε d μ lam u v = 2 * μ * ⟪ε u, ε v⟫_ℝ + lam * ⟪d u, d v⟫_ℝ := by
  simp [lameForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

/-- The Lamé form is symmetric. -/
theorem lameForm_comm (u v : V) : lameForm ε d μ lam u v = lameForm ε d μ lam v u := by
  rw [lameForm_apply, lameForm_apply, real_inner_comm (ε u), real_inner_comm (d u)]

/-- The diagonal of the Lamé form: `a(v, v) = 2μ‖ε v‖² + λ‖d v‖²`. -/
theorem lameForm_self (v : V) :
    lameForm ε d μ lam v v = 2 * μ * ‖ε v‖ ^ 2 + lam * ‖d v‖ ^ 2 := by
  rw [lameForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The total potential energy `J(v) = ½ a(v, v) - ℓ(v)`. -/
def lameEnergy (ℓ : V →L[ℝ] ℝ) (v : V) : ℝ := 2⁻¹ * lameForm ε d μ lam v v - ℓ v

variable {ε d μ lam}

/-- **Lax–Milgram** for a coercive Lamé form on a Hilbert space: for every continuous linear
load `ℓ` there is a unique `u` with `a(u, v) = ℓ(v)` for all `v`. -/
theorem existsUnique_lame [CompleteSpace V] {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v, c * ‖v‖ ^ 2 ≤ lameForm ε d μ lam v v) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v, lameForm ε d μ lam u v = ℓ v := by
  have hB : IsCoercive (lameForm ε d μ lam) :=
    ⟨c, hc, fun v => by rw [mul_assoc, ← sq]; exact hcoer v⟩
  set g := (InnerProductSpace.toDual ℝ V).symm ℓ
  have hg : ∀ w, ⟪g, w⟫_ℝ = ℓ w := fun w => InnerProductSpace.toDual_symm_apply
  refine ⟨hB.continuousLinearEquivOfBilin.symm g, fun w => ?_, fun v hv => ?_⟩
  · rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hg]
  · have := hB.unique_continuousLinearEquivOfBilin (v := v) (f := g) fun w => by rw [hg, hv]
    rw [this, ContinuousLinearEquiv.symm_apply_apply]

/-- `J(v) = J(u) + ½ a(v - u, v - u)` for the weak solution `u`. -/
theorem lameEnergy_eq_add {ℓ : V →L[ℝ] ℝ} {u : V} (hu : ∀ v, lameForm ε d μ lam u v = ℓ v)
    (v : V) : lameEnergy ε d μ lam ℓ v =
      lameEnergy ε d μ lam ℓ u + 2⁻¹ * lameForm ε d μ lam (v - u) (v - u) := by
  have h1 := hu (v - u)
  have h2 := lameForm_comm ε d μ lam u v
  have h3 := hu u
  simp only [lameEnergy, map_sub, sub_apply] at h1 ⊢
  linarith

/-- The weak solution minimises the total potential energy (`μ, λ ≥ 0`). -/
theorem isMinOn_lameEnergy (hμ : 0 ≤ μ) (hlam : 0 ≤ lam) {ℓ : V →L[ℝ] ℝ} {u : V}
    (hu : ∀ v, lameForm ε d μ lam u v = ℓ v) :
    IsMinOn (lameEnergy ε d μ lam ℓ) Set.univ u := fun v _ => by
  change lameEnergy ε d μ lam ℓ u ≤ lameEnergy ε d μ lam ℓ v
  rw [lameEnergy_eq_add hu v, lameForm_self]
  have : 0 ≤ 2 * μ * ‖ε (v - u)‖ ^ 2 + lam * ‖d (v - u)‖ ^ 2 := by positivity
  linarith

/-- For a coercive Lamé form the energy minimiser is unique. -/
theorem eq_of_lameEnergy_eq {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v, c * ‖v‖ ^ 2 ≤ lameForm ε d μ lam v v) {ℓ : V →L[ℝ] ℝ} {u : V}
    (hu : ∀ v, lameForm ε d μ lam u v = ℓ v) {v : V}
    (hv : lameEnergy ε d μ lam ℓ v = lameEnergy ε d μ lam ℓ u) : v = u := by
  rw [lameEnergy_eq_add hu v, add_eq_left, mul_eq_zero] at hv
  have h0 : lameForm ε d μ lam (v - u) (v - u) = 0 := hv.resolve_left (by norm_num)
  have hb := hcoer (v - u)
  rw [h0] at hb
  have : ‖v - u‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖v - u‖]) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

end Abstract

/-! ### The clamped problem on `H¹₀(Ω; ℝⁿ)` -/

section Clamped

variable {μ lam : ℝ}

/-- The strain `ε : H¹₀(Ω; ℝⁿ) → L²(ℝⁿ)ⁿˣⁿ`. -/
abbrev strainH (Ω : Set (Fin n → ℝ)) : H10 Ω →L[ℝ] Mat n := strain.comp (H10 Ω).subtypeL

/-- The divergence `div : H¹₀(Ω; ℝⁿ) → L²(ℝⁿ)`. -/
abbrev divH (Ω : Set (Fin n → ℝ)) : H10 Ω →L[ℝ] L2 n := div.comp (H10 Ω).subtypeL

/-- `strainH` is the strain of the underlying element of `G`. -/
theorem strainH_apply (U : H10 Ω) : strainH Ω U = strain (U : G n) := rfl

/-- `divH` is the divergence of the underlying element of `G`. -/
theorem divH_apply (U : H10 Ω) : divH Ω U = div (U : G n) := rfl

/-- On `H¹₀(Ω; ℝⁿ)` the diagonal of the Lamé form is the Lamé energy `Sobolev.energy`. -/
theorem lameForm_H10_self (U : H10 Ω) :
    lameForm (strainH Ω) (divH Ω) μ lam U U = energy μ lam (U : G n) := by
  rw [lameForm_self, energy, strainH_apply, divH_apply]

/-- The Lamé form on `H¹₀(Ω; ℝⁿ)` is coercive for `Ω` in a slab, `μ > 0`, `λ ≥ 0`. -/
theorem lameForm_H10_coercive (hμ : 0 < μ) (hlam : 0 ≤ lam) (j : Fin n) {R : ℝ}
    (hΩ : Ω ⊆ {x | |x j| ≤ R}) (U : H10 Ω) :
    μ / (1 + 4 * R ^ 2) * ‖U‖ ^ 2 ≤ lameForm (strainH Ω) (divH Ω) μ lam U U := by
  rw [lameForm_H10_self]
  exact energy_coercive_H10 hμ hlam j hΩ U.2

/-- **Existence and uniqueness of weak solutions** of clamped isotropic linear elastostatics
for `Ω` in a slab `{|xⱼ| ≤ R}`: for every continuous load `ℓ` on `H¹₀(Ω; ℝⁿ)` there is a
unique `U ∈ H¹₀(Ω; ℝⁿ)` with `2μ⟪ε(U), ε(V)⟫ + λ⟪div U, div V⟫ = ℓ(V)` for all `V`. -/
theorem existsUnique_weak_slab (hμ : 0 < μ) (hlam : 0 ≤ lam) (j : Fin n) {R : ℝ}
    (hΩ : Ω ⊆ {x | |x j| ≤ R}) (ℓ : H10 Ω →L[ℝ] ℝ) :
    ∃! U : H10 Ω, ∀ V : H10 Ω,
      2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ + lam * ⟪div (U : G n), div (V : G n)⟫_ℝ =
        ℓ V := by
  have h := existsUnique_lame (by positivity : 0 < μ / (1 + 4 * R ^ 2))
    (lameForm_H10_coercive hμ hlam j hΩ) ℓ
  simpa only [lameForm_apply, strainH_apply, divH_apply] using h

/-- **Existence and uniqueness of weak solutions** of clamped isotropic linear elastostatics
on a bounded set `Ω ⊆ ℝⁿ` (`μ > 0`, `λ ≥ 0`): for every continuous linear load `ℓ` on
`H¹₀(Ω; ℝⁿ)` there is a unique `U ∈ H¹₀(Ω; ℝⁿ)` with
`2μ⟪ε(U), ε(V)⟫ + λ⟪div U, div V⟫ = ℓ(V)` for all `V ∈ H¹₀(Ω; ℝⁿ)`. -/
theorem existsUnique_weak [NeZero n] (hμ : 0 < μ) (hlam : 0 ≤ lam)
    (hΩ : Bornology.IsBounded Ω) (ℓ : H10 Ω →L[ℝ] ℝ) :
    ∃! U : H10 Ω, ∀ V : H10 Ω,
      2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ + lam * ⟪div (U : G n), div (V : G n)⟫_ℝ =
        ℓ V := by
  obtain ⟨R, hR⟩ := exists_slab hΩ
  exact existsUnique_weak_slab hμ hlam 0 hR ℓ

/-- The load `V ↦ ⟪f, V⟫_{L²}` of a body force `f ∈ L²(ℝⁿ)ⁿ`. -/
def bodyLoad (Ω : Set (Fin n → ℝ)) (f : Vec n) : H10 Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (disp.comp (H10 Ω).subtypeL)

/-- Evaluation of the body-force load. -/
theorem bodyLoad_apply (f : Vec n) (V : H10 Ω) : bodyLoad Ω f V = ⟪f, disp (V : G n)⟫_ℝ := by
  simp [bodyLoad, innerSL_apply_apply]

/-- **Clamped body under a body force**: for bounded `Ω`, `μ > 0`, `λ ≥ 0` and `f ∈ L²`,
there is a unique `U ∈ H¹₀(Ω; ℝⁿ)` with `2μ⟪ε(U), ε(V)⟫ + λ⟪div U, div V⟫ = ⟪f, V⟫` for all
`V ∈ H¹₀(Ω; ℝⁿ)`. -/
theorem existsUnique_clamped [NeZero n] (hμ : 0 < μ) (hlam : 0 ≤ lam)
    (hΩ : Bornology.IsBounded Ω) (f : Vec n) :
    ∃! U : H10 Ω, ∀ V : H10 Ω,
      2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ + lam * ⟪div (U : G n), div (V : G n)⟫_ℝ =
        ⟪f, disp (V : G n)⟫_ℝ := by
  simpa only [bodyLoad_apply] using existsUnique_weak hμ hlam hΩ (bodyLoad Ω f)

/-- The total potential energy `J(V) = ½ (2μ‖ε(V)‖² + λ‖div V‖²) - ℓ(V)` on `H¹₀(Ω; ℝⁿ)`. -/
def totalEnergy (μ lam : ℝ) (ℓ : H10 Ω →L[ℝ] ℝ) (V : H10 Ω) : ℝ :=
  2⁻¹ * energy μ lam (V : G n) - ℓ V

/-- `totalEnergy` is the abstract `lameEnergy` of `strainH`, `divH`. -/
theorem totalEnergy_eq (ℓ : H10 Ω →L[ℝ] ℝ) :
    totalEnergy μ lam ℓ = lameEnergy (strainH Ω) (divH Ω) μ lam ℓ := by
  funext V
  rw [totalEnergy, lameEnergy, lameForm_H10_self]

/-- A weak solution in concrete form solves the abstract Lamé problem. -/
theorem lameForm_H10_eq {ℓ : H10 Ω →L[ℝ] ℝ} {U : H10 Ω}
    (hU : ∀ V : H10 Ω, 2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ +
      lam * ⟪div (U : G n), div (V : G n)⟫_ℝ = ℓ V) (V : H10 Ω) :
    lameForm (strainH Ω) (divH Ω) μ lam U V = ℓ V := by
  rw [lameForm_apply, strainH_apply, strainH_apply, divH_apply, divH_apply]
  exact hU V

/-- **Principle of minimum potential energy**: the weak solution minimises `J` on
`H¹₀(Ω; ℝⁿ)`. -/
theorem isMinOn_totalEnergy (hμ : 0 ≤ μ) (hlam : 0 ≤ lam) {ℓ : H10 Ω →L[ℝ] ℝ} {U : H10 Ω}
    (hU : ∀ V : H10 Ω, 2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ +
      lam * ⟪div (U : G n), div (V : G n)⟫_ℝ = ℓ V) :
    IsMinOn (totalEnergy μ lam ℓ) Set.univ U := by
  rw [totalEnergy_eq]
  exact isMinOn_lameEnergy hμ hlam (lameForm_H10_eq hU)

/-- The minimiser of `J` is unique: on bounded `Ω`, `J(V) = J(U)` for the weak solution `U`
forces `V = U`. -/
theorem eq_of_totalEnergy_eq [NeZero n] (hμ : 0 < μ) (hlam : 0 ≤ lam)
    (hΩ : Bornology.IsBounded Ω) {ℓ : H10 Ω →L[ℝ] ℝ} {U : H10 Ω}
    (hU : ∀ V : H10 Ω, 2 * μ * ⟪strain (U : G n), strain (V : G n)⟫_ℝ +
      lam * ⟪div (U : G n), div (V : G n)⟫_ℝ = ℓ V) {V : H10 Ω}
    (hV : totalEnergy μ lam ℓ V = totalEnergy μ lam ℓ U) : V = U := by
  obtain ⟨R, hR⟩ := exists_slab hΩ
  rw [totalEnergy_eq] at hV
  exact eq_of_lameEnergy_eq (by positivity : 0 < μ / (1 + 4 * R ^ 2))
    (lameForm_H10_coercive hμ hlam 0 hR) (lameForm_H10_eq hU) hV

end Clamped

end ContinuumMechanics.Sobolev
