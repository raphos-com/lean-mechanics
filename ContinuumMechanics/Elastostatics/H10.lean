import ContinuumMechanics.Elastostatics.Variational
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The Sobolev space `H¹₀(Ω; ℝⁿ)` and Korn's inequality by density

For an open set `Ω ⊆ ℝⁿ` we realise `H¹₀(Ω; ℝⁿ)` as the closure of the smooth, compactly supported
vector fields with support in `Ω`, embedded into the Hilbert space

`G = L²(ℝⁿ)ⁿ × L²(ℝⁿ)ⁿˣⁿ`   (`Sobolev.G`, an `L²` product of `PiLp 2` spaces)

by their **graph** `u ↦ (u, ∇u)` (`Sobolev.graph`), i.e. the components `uᵢ` and the partial
derivatives `∂ⱼuᵢ` regarded as `L²` classes. Its norm is the `H¹` norm
`‖U‖² = Σᵢ ‖Uᵢ‖²_{L²} + Σᵢⱼ ‖∂ⱼUᵢ‖²_{L²}`. Being a closed subspace of a Hilbert space,
`H¹₀(Ω; ℝⁿ)` is complete.

The gradient, strain and divergence of an element `U = (u, g) ∈ G` are the continuous linear maps
`∇U = g` (`Sobolev.grad`), `ε(U)ᵢⱼ = (gᵢⱼ + gⱼᵢ)/2` (`Sobolev.strain`) and
`div U = Σᵢ gᵢᵢ` (`Sobolev.div`).
On graphs of smooth fields their squared `L²` norms are `∫ |∇u|²`, `∫ |ε(u)|²` and `∫ (div u)²`
(`Sobolev.norm_grad_graph_sq`, …), so Korn's identity of `Elastostatics.Korn` reads
`‖∇U‖² + ‖div U‖² = 2‖ε(U)‖²` on graphs. Both sides are continuous in `U`, so the identity
extends to the closure `H¹₀(Ω; ℝⁿ)`: this is **Korn's inequality by density**.

## Main results

* `Sobolev.H10`: the space `H¹₀(Ω; ℝⁿ)`, with `Sobolev.instCompleteSpace`.
* `Sobolev.korn_identity`: `‖∇U‖² + ‖div U‖² = 2‖ε(U)‖²` for `U ∈ H¹₀(Ω; ℝⁿ)`.
* `Sobolev.korn_first`: **Korn's first inequality** `‖∇U‖² ≤ 2‖ε(U)‖²` on `H¹₀(Ω; ℝⁿ)`.
* `Sobolev.energy_coercive`: the Lamé energy `2μ‖ε(U)‖² + λ‖div U‖²` (`μ > 0`, `λ ≥ 0`) is bounded
  below by `μ‖∇U‖²` on `H¹₀(Ω; ℝⁿ)`.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.3.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §9.4.
* [DuvautLions1976] G. Duvaut, J.-L. Lions, *Inequalities in Mechanics and Physics*, Ch. III.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Sobolev

open Korn

variable {n : ℕ}

/-- The Hilbert space `L²(ℝⁿ)` of real square-integrable functions. -/
abbrev L2 (n : ℕ) : Type := Lp ℝ 2 (volume : Measure (Fin n → ℝ))

/-- Vector fields in `L²(ℝⁿ)ⁿ`, with the Hilbert (`ℓ²`) norm. -/
abbrev Vec (n : ℕ) : Type := PiLp 2 fun _ : Fin n => L2 n

/-- Matrix fields in `L²(ℝⁿ)ⁿˣⁿ`, with the Hilbert (Frobenius) norm. -/
abbrev Mat (n : ℕ) : Type := PiLp 2 fun _ : Fin n => Vec n

/-- The ambient Hilbert space `G = L²(ℝⁿ)ⁿ × L²(ℝⁿ)ⁿˣⁿ` of pairs (displacement, gradient). -/
abbrev G (n : ℕ) : Type := WithLp 2 (Vec n × Mat n)

/-! ### Functions as `L²` classes -/

section ToL2

variable {f g : (Fin n → ℝ) → ℝ}

open Classical in
/-- The `L²` class of a function (zero if the function is not square integrable). -/
def toL2 (f : (Fin n → ℝ) → ℝ) : L2 n :=
  if h : MemLp f 2 volume then h.toLp f else 0

/-- On square-integrable functions `toL2` is `MemLp.toLp`. -/
theorem toL2_of_memLp (h : MemLp f 2 volume) : toL2 f = h.toLp f := by
  simp [toL2, h]

/-- `toL2` is additive on square-integrable functions. -/
theorem toL2_add (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f + g) = toL2 f + toL2 g := by
  rw [toL2_of_memLp hf, toL2_of_memLp hg, toL2_of_memLp (hf.add hg), MemLp.toLp_add]

/-- `toL2` commutes with scalar multiplication on square-integrable functions. -/
theorem toL2_smul (c : ℝ) (hf : MemLp f 2 volume) : toL2 (c • f) = c • toL2 f := by
  rw [toL2_of_memLp hf, toL2_of_memLp (hf.const_smul c), MemLp.toLp_const_smul]

/-- `toL2` commutes with finite sums of square-integrable functions. -/
theorem toL2_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℝ) → ℝ)
    (hF : ∀ i, MemLp (F i) 2 volume) : toL2 (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, toL2 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact toL2_of_memLp (MemLp.zero' (p := 2) (μ := volume)) |>.trans (MemLp.toLp_zero _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    have hs : MemLp (fun x => ∑ i ∈ s, F i x) 2 volume :=
      memLp_finsetSum s fun i _ => hF i
    exact toL2_add (f := F a) (hF a) hs

/-- The squared `L²` norm of an `L²` function is `∫ f²`. -/
theorem norm_toL2_sq (hf : MemLp f 2 volume) : ‖toL2 f‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, toL2_of_memLp hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end ToL2

/-! ### Test fields and their graphs -/

/-- The space of smooth vector fields `u : ℝⁿ → ℝⁿ` with compact support contained in `Ω`. -/
def testFields (Ω : Set (Fin n → ℝ)) : Submodule ℝ (Fin n → (Fin n → ℝ) → ℝ) where
  carrier := {u | ∀ i, ContDiff ℝ ∞ (u i) ∧ HasCompactSupport (u i) ∧ tsupport (u i) ⊆ Ω}
  add_mem' {u v} hu hv i := ⟨(hu i).1.add (hv i).1, (hu i).2.1.add (hv i).2.1,
    (tsupport_add _ _).trans (Set.union_subset (hu i).2.2 (hv i).2.2)⟩
  zero_mem' _ := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' c u hu i := by
    obtain ⟨h1, h2, h3⟩ := hu i
    refine ⟨h1.const_smul c, ?_, ?_⟩
    · exact HasCompactSupport.smul_left (f := fun _ => c) h2
    · exact (tsupport_smul_subset_right (fun _ => c) (u i)).trans h3

section Test

variable {Ω : Set (Fin n → ℝ)}

/-- The components of a test field are of class `C²`. -/
theorem contDiff_two_of_mem {u : Fin n → (Fin n → ℝ) → ℝ} (hu : u ∈ testFields Ω) (i : Fin n) :
    ContDiff ℝ 2 (u i) :=
  (hu i).1.of_le (by simp)

/-- The partial derivatives of the components of a test field are continuous. -/
theorem continuous_pd_of_mem {u : Fin n → (Fin n → ℝ) → ℝ} (hu : u ∈ testFields Ω)
    (i j : Fin n) : Continuous (pd (u i) j) :=
  continuous_pd ((hu i).1.of_le (by simp)) j

/-- The components of a test field are square integrable. -/
theorem memLp_of_mem {u : Fin n → (Fin n → ℝ) → ℝ} (hu : u ∈ testFields Ω) (i : Fin n) :
    MemLp (u i) 2 volume :=
  (hu i).1.continuous.memLp_of_hasCompactSupport (hu i).2.1

/-- The partial derivatives of a test field are square integrable. -/
theorem memLp_pd_of_mem {u : Fin n → (Fin n → ℝ) → ℝ} (hu : u ∈ testFields Ω) (i j : Fin n) :
    MemLp (pd (u i) j) 2 volume :=
  (continuous_pd_of_mem hu i j).memLp_of_hasCompactSupport (hasCompactSupport_pd (hu i).2.1 j)

/-- `∂ⱼ(c f) = c ∂ⱼf` for differentiable `f`. -/
theorem pd_smul (c : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) (j : Fin n) :
    pd (c • f) j = c • pd f j := by
  funext x
  simp [pd, fderiv_const_smul (hf x) c]

/-- The **graph map** `u ↦ (u, ∇u)` from test fields into `G`, componentwise as `L²` classes. -/
def graph (Ω : Set (Fin n → ℝ)) : testFields Ω →ₗ[ℝ] G n where
  toFun u := WithLp.toLp 2 (WithLp.toLp 2 fun i => toL2 (u.1 i),
    WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => toL2 (pd (u.1 i) j))
  map_add' u v := by
    have hd : ∀ (w : testFields Ω) i, Differentiable ℝ (w.1 i) := fun w i =>
      (w.2 i).1.differentiable (by simp)
    simp only [Submodule.coe_add, Pi.add_apply]
    simp_rw [pd_add (hd u _) (hd v _), toL2_add (memLp_of_mem u.2 _) (memLp_of_mem v.2 _),
      toL2_add (memLp_pd_of_mem u.2 _ _) (memLp_pd_of_mem v.2 _ _)]
    rfl
  map_smul' c u := by
    have hd : ∀ i, Differentiable ℝ (u.1 i) := fun i => (u.2 i).1.differentiable (by simp)
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    simp_rw [pd_smul c (hd _), toL2_smul c (memLp_of_mem u.2 _),
      toL2_smul c (memLp_pd_of_mem u.2 _ _)]
    rfl

end Test

/-- The Sobolev space `H¹₀(Ω; ℝⁿ)`: the closure in `G` of the graphs of smooth vector fields
compactly supported in `Ω`. -/
def H10 (Ω : Set (Fin n → ℝ)) : Submodule ℝ (G n) :=
  (LinearMap.range (graph Ω)).topologicalClosure

/-- `H¹₀(Ω; ℝⁿ)` is closed in `G`. -/
theorem isClosed_H10 (Ω : Set (Fin n → ℝ)) : IsClosed (H10 Ω : Set (G n)) :=
  Submodule.isClosed_topologicalClosure _

/-- `H¹₀(Ω; ℝⁿ)` is complete: a closed subspace of the Hilbert space `G`. -/
instance instCompleteSpace (Ω : Set (Fin n → ℝ)) : CompleteSpace (H10 Ω) :=
  (isClosed_H10 Ω).completeSpace_coe

/-- The graph of every test field lies in `H¹₀(Ω; ℝⁿ)`. -/
theorem graph_mem_H10 {Ω : Set (Fin n → ℝ)} (u : testFields Ω) : graph Ω u ∈ H10 Ω :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)

/-! ### Gradient, strain and divergence -/

/-- The displacement component `U ↦ u` of `U = (u, g) ∈ G`. -/
def disp : G n →L[ℝ] Vec n := WithLp.fstL 2 ℝ (Vec n) (Mat n)

/-- The gradient component `U ↦ g = ∇U` of `U = (u, g) ∈ G`. -/
def grad : G n →L[ℝ] Mat n := WithLp.sndL 2 ℝ (Vec n) (Mat n)

/-- The symmetric part `g ↦ (g + gᵀ)/2` of a matrix field. -/
def symm : Mat n →L[ℝ] Mat n :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => Vec n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => L2 n).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun j => (1 / 2 : ℝ) •
          ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) j).comp
              (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) i) +
            (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) i).comp
              (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) j))))

/-- The strain `ε(U)ᵢⱼ = (∂ⱼUᵢ + ∂ᵢUⱼ)/2` of `U ∈ G`. -/
def strain : G n →L[ℝ] Mat n := symm.comp grad

/-- The divergence `div U = Σᵢ ∂ᵢUᵢ` of `U ∈ G`. -/
def div : G n →L[ℝ] L2 n :=
  ∑ i, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) i).comp
    ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) i).comp grad)

/-- Components of the strain: `ε(U)ᵢⱼ = (∂ⱼUᵢ + ∂ᵢUⱼ)/2`. -/
theorem strain_apply (U : G n) (i j : Fin n) :
    strain U i j = (1 / 2 : ℝ) • (grad U i j + grad U j i) := by
  simp [strain, symm]

/-- The divergence is the trace of the gradient. -/
theorem div_apply (U : G n) : div U = ∑ i, grad U i i := by
  simp [div]

/-- The squared Frobenius norm of a matrix field: `‖M‖² = Σᵢⱼ ‖Mᵢⱼ‖²`. -/
theorem norm_mat_sq (M : Mat n) : ‖M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ => PiLp.norm_sq_eq_of_L2 _ _

/-! ### Norms on graphs of test fields -/

section Graph

variable {Ω : Set (Fin n → ℝ)}

/-- The square of a continuous compactly supported function is integrable. -/
theorem integrable_sq {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable fun x => f x ^ 2 := by
  simpa only [sq] using integrable_mul_cs hf hf hc

/-- `‖∇U‖² = ∫ |∇u|²` for the graph `U` of a test field `u`. -/
theorem norm_grad_graph_sq (u : testFields Ω) : ‖grad (graph Ω u)‖ ^ 2 = ∫ x, gradSq u.1 x := by
  have hc : ∀ i j, Integrable fun x => pd (u.1 i) j x ^ 2 := fun i j =>
    integrable_sq (continuous_pd_of_mem u.2 i j) (hasCompactSupport_pd (u.2 i).2.1 j)
  rw [norm_mat_sq]
  simp only [gradSq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hc i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hc i j]
  exact Finset.sum_congr rfl fun j _ => norm_toL2_sq (memLp_pd_of_mem u.2 i j)

/-- `‖ε(U)‖² = ∫ |ε(u)|²` for the graph `U` of a test field `u`. -/
theorem norm_strain_graph_sq (u : testFields Ω) :
    ‖strain (graph Ω u)‖ ^ 2 = ∫ x, strainSq u.1 x := by
  have hs : ∀ i j, Continuous (Korn.strain u.1 i j) := fun i j =>
    ((continuous_pd_of_mem u.2 i j).add (continuous_pd_of_mem u.2 j i)).div_const 2
  have hsc : ∀ i j, HasCompactSupport (Korn.strain u.1 i j) := fun i j =>
    ((hasCompactSupport_pd (u.2 i).2.1 j).add (hasCompactSupport_pd (u.2 j).2.1 i)).comp_left
      (g := fun y : ℝ => y / 2) (by simp)
  have hc : ∀ i j, Integrable fun x => Korn.strain u.1 i j x ^ 2 := fun i j =>
    integrable_sq (hs i j) (hsc i j)
  have he : ∀ i j, strain (graph Ω u) i j = toL2 (Korn.strain u.1 i j) := fun i j => by
    have : Korn.strain u.1 i j = (1 / 2 : ℝ) • (pd (u.1 i) j + pd (u.1 j) i) := by
      funext x
      simp only [Korn.strain, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [strain_apply, this, toL2_smul _ ((memLp_pd_of_mem u.2 i j).add (memLp_pd_of_mem u.2 j i)),
      toL2_add (memLp_pd_of_mem u.2 i j) (memLp_pd_of_mem u.2 j i)]
    rfl
  rw [norm_mat_sq]
  change _ = ∫ x, ∑ i, ∑ j, Korn.strain u.1 i j x ^ 2
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hc i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hc i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he]
  exact norm_toL2_sq ((hs i j).memLp_of_hasCompactSupport (hsc i j))

/-- `‖div U‖² = ∫ (div u)²` for the graph `U` of a test field `u`. -/
theorem norm_div_graph_sq (u : testFields Ω) :
    ‖div (graph Ω u)‖ ^ 2 = ∫ x, Korn.div u.1 x ^ 2 := by
  have hd : div (graph Ω u) = toL2 (Korn.div u.1) := by
    rw [div_apply]
    exact (toL2_sum Finset.univ (fun i => pd (u.1 i) i)
      fun i => memLp_pd_of_mem u.2 i i).symm
  rw [hd]
  exact norm_toL2_sq ((continuous_finsetSum _ fun i _ => continuous_pd_of_mem u.2 i i
    ).memLp_of_hasCompactSupport
    (hasCompactSupport_sum _ _ fun i _ => hasCompactSupport_pd (u.2 i).2.1 i))

end Graph

/-! ### Korn's identity and inequality by density -/

section Korn

variable {Ω : Set (Fin n → ℝ)}

/-- **Korn's identity on `H¹₀(Ω; ℝⁿ)`**: `‖∇U‖² + ‖div U‖² = 2‖ε(U)‖²`, extended by density from
the smooth compactly supported fields (`Korn.korn_identity`). -/
theorem korn_identity {U : G n} (hU : U ∈ H10 Ω) :
    ‖grad U‖ ^ 2 + ‖div U‖ ^ 2 = 2 * ‖strain U‖ ^ 2 := by
  have hcl : IsClosed {V : G n | ‖grad V‖ ^ 2 + ‖div V‖ ^ 2 = 2 * ‖strain V‖ ^ 2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : ((LinearMap.range (graph Ω) : Submodule ℝ (G n)) : Set (G n)) ⊆
      {V : G n | ‖grad V‖ ^ 2 + ‖div V‖ ^ 2 = 2 * ‖strain V‖ ^ 2} := by
    rintro _ ⟨u, rfl⟩
    change ‖grad (graph Ω u)‖ ^ 2 + ‖div (graph Ω u)‖ ^ 2 = 2 * ‖strain (graph Ω u)‖ ^ 2
    rw [norm_grad_graph_sq, norm_div_graph_sq, norm_strain_graph_sq]
    exact Korn.korn_identity (contDiff_two_of_mem u.2) fun i => (u.2 i).2.1
  have hU' : U ∈ closure ((LinearMap.range (graph Ω) : Submodule ℝ (G n)) : Set (G n)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hU
  exact closure_minimal hsub hcl hU'

/-- **Korn's first inequality on `H¹₀(Ω; ℝⁿ)`**: `‖∇U‖² ≤ 2‖ε(U)‖²`. -/
theorem korn_first {U : G n} (hU : U ∈ H10 Ω) : ‖grad U‖ ^ 2 ≤ 2 * ‖strain U‖ ^ 2 := by
  have := korn_identity hU
  nlinarith [sq_nonneg ‖div U‖]

/-- Korn's inequality in norm form: `‖∇U‖ ≤ √2 ‖ε(U)‖` on `H¹₀(Ω; ℝⁿ)`. -/
theorem norm_grad_le {U : G n} (hU : U ∈ H10 Ω) : ‖grad U‖ ≤ √2 * ‖strain U‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (grad U)), ← Real.sqrt_sq (norm_nonneg (strain U)),
    ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (korn_first hU)

/-- The isotropic (Lamé) strain energy `a(U, U) = 2μ‖ε(U)‖² + λ‖div U‖²`. -/
def energy (μ lam : ℝ) (U : G n) : ℝ := 2 * μ * ‖strain U‖ ^ 2 + lam * ‖div U‖ ^ 2

/-- **Coercivity** of the Lamé energy on `H¹₀(Ω; ℝⁿ)` in the gradient seminorm:
`a(U, U) ≥ μ‖∇U‖²` for `μ > 0`, `λ ≥ 0`. -/
theorem energy_coercive {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) {U : G n} (hU : U ∈ H10 Ω) :
    μ * ‖grad U‖ ^ 2 ≤ energy μ lam U := by
  have hk := korn_first hU
  have h1 : μ * ‖grad U‖ ^ 2 ≤ μ * (2 * ‖strain U‖ ^ 2) := mul_le_mul_of_nonneg_left hk hμ.le
  have h2 : 0 ≤ lam * ‖div U‖ ^ 2 := mul_nonneg hlam (sq_nonneg _)
  rw [energy]
  linarith

end Korn

end ContinuumMechanics.Sobolev
