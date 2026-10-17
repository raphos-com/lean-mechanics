import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import ContinuumMechanics.Sobolev1D.BarWeak

/-!
# Galerkin approximation and error estimates

Let `V` be a real normed space, `a : V × V → ℝ` a bounded bilinear form
(`|a(u, v)| ≤ M ‖u‖ ‖v‖`) which is coercive (`a(v, v) ≥ α ‖v‖²`, `α > 0`), `ℓ` a continuous
linear load and `u` the **weak solution**, `a(u, v) = ℓ(v)` for all `v ∈ V`. A **Galerkin
(finite element) approximation** on a subspace `V_h ⊆ V` is `u_h ∈ V_h` with
`a(u_h, v_h) = ℓ(v_h)` for all `v_h ∈ V_h`. Then:

* **Galerkin orthogonality**: `a(u - u_h, v_h) = 0` for all `v_h ∈ V_h`;
* **Céa's lemma**: `‖u - u_h‖ ≤ (M / α) ‖u - v_h‖` for all `v_h ∈ V_h`, hence
  `‖u - u_h‖ ≤ (M / α) dist(u, V_h)`: the Galerkin error is quasi-optimal;
* for symmetric `a`, `u_h` is the `a`-orthogonal projection of `u`:
  `a(u - v_h, u - v_h) = a(u - u_h, u - u_h) + a(u_h - v_h, u_h - v_h)`, so `u_h` is the best
  approximation in the energy norm, and `a(u_h, u_h) ≤ a(u, u)`: the discrete model is too
  stiff and **underestimates the strain energy** (and the compliance `ℓ(u_h) ≤ ℓ(u)`);
  equivalently `J(u) ≤ J(u_h) = min_{V_h} J` for the potential energy `J = ½ a - ℓ`;
* on a Hilbert space `V`, the Galerkin problem on a closed (e.g. finite-dimensional) subspace
  is **well posed** (Lax–Milgram on `V_h`).

As a 1D illustration we take the fixed–fixed bar `-EA u'' = f`, `u(0) = u(L) = 0`, in the
derivative model of `Sobolev1D.BarWeak` (`V = H¹₀ = {v ∈ L² | ∫₀ᴸ v = 0}`, `u = P v`). For a mesh
`0 = x₀, x₁, …, xₙ = L` the derivatives of the continuous piecewise-linear functions vanishing at
`0` and `L` are the functions constant on the cells `(x_j, x_{j+1}]` with zero integral
(`Beams.Bar.femSpace`). The **discrete Green's function** `g_i = χ_(0,x_i] - (x_i/L) χ_(0,L]`
lies in this space and represents nodal evaluation, `⟪g_i, w⟫ = (P w)(x_i)` on `H¹₀`; Galerkin
orthogonality then gives **nodal exactness**: the finite element solution interpolates the exact
solution at the nodes, for every load.

## Main results

* `Galerkin.orthogonality`: `a(u - u_h, v_h) = 0`.
* `Galerkin.cea`, `Galerkin.cea_infDist`, `Galerkin.cea_opNorm`: Céa's lemma.
* `Galerkin.energy_pythagoras`, `Galerkin.energy_best_approx`: energy-norm best approximation.
* `Galerkin.form_galerkin_le`, `Galerkin.load_galerkin_le`: `a(u_h, u_h) ≤ a(u, u)`,
  `ℓ(u_h) ≤ ℓ(u)`.
* `Galerkin.energy_galerkin_eq_add`, `Galerkin.isMinOn_energy_galerkin`: `J(u_h) = J(u) +
  ½ a(u - u_h, u - u_h)` and `u_h` minimises `J` on `V_h`.
* `Galerkin.existsUnique_galerkin`, `Galerkin.existsUnique_galerkin_of_finiteDimensional`:
  well-posedness of the Galerkin problem.
* `Beams.Bar.femSpace_existsUnique`: existence of the 1D finite element solution.
* `Beams.Bar.nodal_exact`, `Beams.Bar.nodal_exact_classical`: nodal exactness of linear finite
  elements for the bar.
* `Beams.Bar.fem_best_approx`: the 1D finite element strain is the `L²` best approximation.

## References

* [Ciarlet1978] P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Thm. 2.4.1.
* [BrennerScott2008] S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element
  Methods*, §2.8 and §0.4.
* [Strang1973] G. Strang, G. Fix, *An Analysis of the Finite Element Method*, §1.3.
-/

open scoped InnerProductSpace

namespace ContinuumMechanics

namespace Galerkin

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `u` is a **weak solution** of `a(u, v) = ℓ(v)` for all `v ∈ V`. -/
def IsWeakSolution (a : V →L[ℝ] V →L[ℝ] ℝ) (ℓ : V →L[ℝ] ℝ) (u : V) : Prop :=
  ∀ v, a u v = ℓ v

/-- `u_h` is a **Galerkin solution** on the subspace `V_h`: `u_h ∈ V_h` and
`a(u_h, v_h) = ℓ(v_h)` for all `v_h ∈ V_h`. -/
def IsGalerkinSolution (a : V →L[ℝ] V →L[ℝ] ℝ) (ℓ : V →L[ℝ] ℝ) (Vh : Submodule ℝ V)
    (uh : V) : Prop :=
  uh ∈ Vh ∧ ∀ vh ∈ Vh, a uh vh = ℓ vh

variable {a : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : V →L[ℝ] ℝ} {Vh : Submodule ℝ V} {u uh : V}

/-- **Galerkin orthogonality**: the error `u - u_h` is `a`-orthogonal to `V_h`. -/
theorem orthogonality (hu : IsWeakSolution a ℓ u) (huh : IsGalerkinSolution a ℓ Vh uh)
    {vh : V} (hvh : vh ∈ Vh) : a (u - uh) vh = 0 := by
  rw [map_sub, sub_apply, hu, huh.2 vh hvh, sub_self]

/-- The error tested against itself equals the error tested against `u - v_h`. -/
theorem form_err_err (hu : IsWeakSolution a ℓ u) (huh : IsGalerkinSolution a ℓ Vh uh)
    {vh : V} (hvh : vh ∈ Vh) : a (u - uh) (u - uh) = a (u - uh) (u - vh) := by
  have h0 : a (u - uh) (vh - uh) = 0 := orthogonality hu huh (Vh.sub_mem hvh huh.1)
  have h2 : u - uh = (u - vh) + (vh - uh) := by abel
  calc a (u - uh) (u - uh) = a (u - uh) ((u - vh) + (vh - uh)) := by rw [← h2]
    _ = a (u - uh) (u - vh) := by rw [map_add, h0, add_zero]

/-- **Céa's lemma**: for a bounded (`|a(v, w)| ≤ M ‖v‖ ‖w‖`) coercive (`α ‖v‖² ≤ a(v, v)`)
form, `‖u - u_h‖ ≤ (M / α) ‖u - v_h‖` for every `v_h ∈ V_h`. [Ciarlet1978], Thm. 2.4.1. -/
theorem cea {M α : ℝ} (hα : 0 < α) (hM : ∀ v w, |a v w| ≤ M * ‖v‖ * ‖w‖)
    (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) {vh : V} (hvh : vh ∈ Vh) :
    ‖u - uh‖ ≤ M / α * ‖u - vh‖ := by
  have h3 : α * ‖u - uh‖ ^ 2 ≤ M * ‖u - uh‖ * ‖u - vh‖ := by
    refine (hcoer _).trans ?_
    rw [form_err_err hu huh hvh]
    exact (le_abs_self _).trans (hM _ _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hα]
  have hMw : 0 ≤ M * ‖u - vh‖ := by
    rcases (norm_nonneg (u - vh)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]
    · have h4 := (abs_nonneg _).trans (hM (u - vh) (u - vh))
      have h5 : 0 ≤ M * ‖u - vh‖ * ‖u - vh‖ := h4
      exact nonneg_of_mul_nonneg_left h5 h0
  rcases (norm_nonneg (u - uh)).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    exact hMw
  · have h6 : ‖u - uh‖ * α * ‖u - uh‖ ≤ M * ‖u - vh‖ * ‖u - uh‖ := by nlinarith
    exact le_of_mul_le_mul_right h6 h0

/-- **Céa's lemma** with the infimum: `‖u - u_h‖ ≤ (M / α) dist(u, V_h)`. -/
theorem cea_infDist {M α : ℝ} (hα : 0 < α) (hM0 : 0 < M) (hM : ∀ v w, |a v w| ≤ M * ‖v‖ * ‖w‖)
    (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) :
    ‖u - uh‖ ≤ M / α * Metric.infDist u (Vh : Set V) := by
  have key : α / M * ‖u - uh‖ ≤ Metric.infDist u (Vh : Set V) := by
    rw [Metric.le_infDist ⟨0, Vh.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm, div_mul_eq_mul_div, div_le_iff₀ hM0]
    have h := cea hα hM hcoer hu huh hy
    rw [div_mul_eq_mul_div, le_div_iff₀ hα] at h
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hα]
  rw [div_mul_eq_mul_div, div_le_iff₀ hM0] at key
  linarith

/-- **Céa's lemma** with the operator norm `M = ‖a‖` as continuity constant. -/
theorem cea_opNorm {α : ℝ} (hα : 0 < α) (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v)
    (hu : IsWeakSolution a ℓ u) (huh : IsGalerkinSolution a ℓ Vh uh) {vh : V} (hvh : vh ∈ Vh) :
    ‖u - uh‖ ≤ ‖a‖ / α * ‖u - vh‖ :=
  cea hα (fun v w => by rw [← Real.norm_eq_abs]; exact a.le_opNorm₂ v w) hcoer hu huh hvh

section Symmetric

variable (hsymm : ∀ v w, a v w = a w v)
include hsymm

/-- **Pythagoras in the energy norm** for a symmetric form: `u_h` is the `a`-orthogonal
projection of `u` onto `V_h`, and
`a(u - v_h, u - v_h) = a(u - u_h, u - u_h) + a(u_h - v_h, u_h - v_h)`. -/
theorem energy_pythagoras (hu : IsWeakSolution a ℓ u) (huh : IsGalerkinSolution a ℓ Vh uh)
    {vh : V} (hvh : vh ∈ Vh) :
    a (u - vh) (u - vh) = a (u - uh) (u - uh) + a (uh - vh) (uh - vh) := by
  have h0 : a (u - uh) (uh - vh) = 0 := orthogonality hu huh (Vh.sub_mem huh.1 hvh)
  have h0' : a (uh - vh) (u - uh) = 0 := by rw [hsymm]; exact h0
  have h2 : u - vh = (u - uh) + (uh - vh) := by abel
  rw [h2]
  simp only [map_add, add_apply, h0, h0']
  ring

/-- **Energy-norm best approximation**: for a symmetric nonnegative form,
`a(u - u_h, u - u_h) ≤ a(u - v_h, u - v_h)` for every `v_h ∈ V_h`. -/
theorem energy_best_approx (hpos : ∀ v, 0 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) {vh : V} (hvh : vh ∈ Vh) :
    a (u - uh) (u - uh) ≤ a (u - vh) (u - vh) := by
  rw [energy_pythagoras hsymm hu huh hvh]
  linarith [hpos (uh - vh)]

/-- The energy splits as `a(u, u) = a(u_h, u_h) + a(u - u_h, u - u_h)`. -/
theorem form_eq_add (hu : IsWeakSolution a ℓ u) (huh : IsGalerkinSolution a ℓ Vh uh) :
    a u u = a uh uh + a (u - uh) (u - uh) := by
  have h := energy_pythagoras hsymm hu huh Vh.zero_mem
  simp only [sub_zero] at h
  linarith

/-- **The discrete model is too stiff**: the strain energy of the Galerkin solution
underestimates that of the exact solution, `a(u_h, u_h) ≤ a(u, u)`. -/
theorem form_galerkin_le (hpos : ∀ v, 0 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) : a uh uh ≤ a u u := by
  rw [form_eq_add hsymm hu huh]
  linarith [hpos (u - uh)]

/-- The **compliance** is underestimated: `ℓ(u_h) ≤ ℓ(u)`. -/
theorem load_galerkin_le (hpos : ∀ v, 0 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) : ℓ uh ≤ ℓ u := by
  rw [← hu u, ← huh.2 uh huh.1]
  exact form_galerkin_le hsymm hpos hu huh

/-- The total potential energy `J(v) = ½ a(v, v) - ℓ(v)`. -/
noncomputable def energy (a : V →L[ℝ] V →L[ℝ] ℝ) (ℓ : V →L[ℝ] ℝ) (v : V) : ℝ :=
  2⁻¹ * a v v - ℓ v

omit hsymm in
/-- At the Galerkin solution, `J(u_h) = -½ a(u_h, u_h)`. -/
theorem energy_galerkin (huh : IsGalerkinSolution a ℓ Vh uh) :
    energy a ℓ uh = -(2⁻¹ * a uh uh) := by
  rw [energy, ← huh.2 uh huh.1]
  ring

/-- `J(v_h) = J(u_h) + ½ a(v_h - u_h, v_h - u_h)` for `v_h ∈ V_h`. -/
theorem energy_eq_add_galerkin (huh : IsGalerkinSolution a ℓ Vh uh) {vh : V} (hvh : vh ∈ Vh) :
    energy a ℓ vh = energy a ℓ uh + 2⁻¹ * a (vh - uh) (vh - uh) := by
  have h1 := huh.2 (vh - uh) (Vh.sub_mem hvh huh.1)
  have h2 := hsymm uh vh
  have h3 := huh.2 uh huh.1
  simp only [energy, map_sub, sub_apply] at h1 ⊢
  linarith

/-- **Discrete minimum potential energy**: the Galerkin solution minimises `J` on `V_h`. -/
theorem isMinOn_energy_galerkin (hpos : ∀ v, 0 ≤ a v v) (huh : IsGalerkinSolution a ℓ Vh uh) :
    IsMinOn (energy a ℓ) (Vh : Set V) uh := fun vh hvh => by
  change energy a ℓ uh ≤ energy a ℓ vh
  rw [energy_eq_add_galerkin hsymm huh hvh]
  linarith [hpos (vh - uh)]

/-- `J(u_h) = J(u) + ½ a(u - u_h, u - u_h)`: the Galerkin energy exceeds the exact one by half
the energy of the error. -/
theorem energy_galerkin_eq_add (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) :
    energy a ℓ uh = energy a ℓ u + 2⁻¹ * a (u - uh) (u - uh) := by
  rw [energy_galerkin huh, energy, ← hu u, form_eq_add hsymm hu huh]
  ring

/-- `J(u) ≤ J(u_h)`. -/
theorem energy_le_energy_galerkin (hpos : ∀ v, 0 ≤ a v v) (hu : IsWeakSolution a ℓ u)
    (huh : IsGalerkinSolution a ℓ Vh uh) : energy a ℓ u ≤ energy a ℓ uh := by
  rw [energy_galerkin_eq_add hsymm hu huh]
  linarith [hpos (u - uh)]

end Symmetric

end Normed

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The restriction `a|_{V_h × V_h}` of a bilinear form to a subspace. -/
noncomputable def restrict (a : V →L[ℝ] V →L[ℝ] ℝ) (Vh : Submodule ℝ V) :
    Vh →L[ℝ] Vh →L[ℝ] ℝ :=
  a.bilinearComp Vh.subtypeL Vh.subtypeL

/-- Evaluation of the restricted form. -/
theorem restrict_apply (a : V →L[ℝ] V →L[ℝ] ℝ) (Vh : Submodule ℝ V) (v w : Vh) :
    restrict a Vh v w = a v w := rfl

/-- A coercive form stays coercive on every subspace. -/
theorem isCoercive_restrict {a : V →L[ℝ] V →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v) (Vh : Submodule ℝ V) : IsCoercive (restrict a Vh) :=
  ⟨α, hα, fun v => by
    rw [restrict_apply, mul_assoc, ← sq]
    exact hcoer v⟩

/-- **Well-posedness of the Galerkin problem** on a complete (closed) subspace `V_h`, by
Lax–Milgram on `V_h`: there is exactly one `u_h ∈ V_h` with `a(u_h, v_h) = ℓ(v_h)` on `V_h`. -/
theorem existsUnique_galerkin {a : V →L[ℝ] V →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v) (ℓ : V →L[ℝ] ℝ) (Vh : Submodule ℝ V) [CompleteSpace Vh] :
    ∃! uh : V, IsGalerkinSolution a ℓ Vh uh := by
  have hB := isCoercive_restrict hα hcoer Vh
  set ℓh : Vh →L[ℝ] ℝ := ℓ.comp Vh.subtypeL
  set g := (InnerProductSpace.toDual ℝ Vh).symm ℓh
  have hg : ∀ w, ⟪g, w⟫_ℝ = ℓh w := fun w => InnerProductSpace.toDual_symm_apply
  have hw0 : ∀ w, restrict a Vh (hB.continuousLinearEquivOfBilin.symm g) w = ℓh w := fun w => by
    rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hg]
  refine ⟨hB.continuousLinearEquivOfBilin.symm g,
    ⟨Submodule.coe_mem _, fun vh hvh => hw0 ⟨vh, hvh⟩⟩, fun y hy => ?_⟩
  obtain ⟨hy1, hy2⟩ := hy
  have h := hB.unique_continuousLinearEquivOfBilin (v := ⟨y, hy1⟩) (f := g)
    fun w => by rw [hg]; exact (hy2 w w.2).symm
  have h' : (⟨y, hy1⟩ : Vh) = hB.continuousLinearEquivOfBilin.symm g := by
    rw [h, ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val h'

/-- **Existence and uniqueness** of the Galerkin solution on a finite-dimensional subspace
(a finite element space). -/
theorem existsUnique_galerkin_of_finiteDimensional {a : V →L[ℝ] V →L[ℝ] ℝ} {α : ℝ}
    (hα : 0 < α) (hcoer : ∀ v, α * ‖v‖ ^ 2 ≤ a v v) (ℓ : V →L[ℝ] ℝ) (Vh : Submodule ℝ V)
    [FiniteDimensional ℝ Vh] : ∃! uh : V, IsGalerkinSolution a ℓ Vh uh :=
  haveI : CompleteSpace Vh := FiniteDimensional.complete ℝ Vh
  existsUnique_galerkin hα hcoer ℓ Vh

end Hilbert

end Galerkin

/-! ### Linear finite elements for the fixed–fixed bar -/

namespace Beams.Bar

open Sobolev1D MeasureTheory

variable (b : Bar)

/-- The (derivative of the) shape on the cell `(x_j, x_{j+1}]`: `χ_(0,x_{j+1}] - χ_(0,x_j]`,
the indicator of the cell when `x_j ≤ x_{j+1}`. -/
noncomputable def cellChi (x : ℕ → ℝ) (j : ℕ) : L2 b.L := chi b.L (x (j + 1)) - chi b.L (x j)

/-- Cellwise constant functions on the mesh `x₀, …, xₙ`. -/
noncomputable def pcSpace (x : ℕ → ℝ) (n : ℕ) : Submodule ℝ (L2 b.L) :=
  Submodule.span ℝ (Set.range fun j : Fin n => b.cellChi x j)

/-- The **linear finite element space** in the derivative model: cellwise constant strains
with zero integral, i.e. derivatives of continuous piecewise-linear displacements vanishing at
`0` and `L`. -/
noncomputable def femSpace (x : ℕ → ℝ) (n : ℕ) : Submodule ℝ (L2 b.L) :=
  b.pcSpace x n ⊓ b.H10

/-- The cellwise constants form a finite-dimensional space. -/
instance (x : ℕ → ℝ) (n : ℕ) : FiniteDimensional ℝ (b.pcSpace x n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The finite element space is finite-dimensional. -/
instance (x : ℕ → ℝ) (n : ℕ) : FiniteDimensional ℝ (b.femSpace x n) :=
  Submodule.finiteDimensional_inf_left _ _

/-- `χ_(0,0] = 0`. -/
theorem chi_zero : chi b.L 0 = 0 := by
  have h : ⟪chi b.L 0, chi b.L 0⟫_ℝ = 0 := by
    rw [← prim_apply, prim_eq_setIntegral]
    simp
  exact inner_self_eq_zero.mp h

/-- `(P χ_(0,L])(L) = L`. -/
theorem prim_chi_self : prim (chi b.L b.L) b.L = b.L := by
  rw [prim_eq_setIntegral, chi, setIntegral_indicatorConstLp measurableSet_Ioc]
  simp [Measure.real, b.L_pos.le]

/-- `χ_(0,x_i] = ∑_{j < i} (cell j)` lies in the cellwise constants (for `x₀ = 0`). -/
theorem chi_mem_pcSpace {x : ℕ → ℝ} {n : ℕ} (hx0 : x 0 = 0) {i : ℕ} (hi : i ≤ n) :
    chi b.L (x i) ∈ b.pcSpace x n := by
  have h : ∑ j ∈ Finset.range i, b.cellChi x j = chi b.L (x i) := by
    have := Finset.sum_range_sub (fun j => chi b.L (x j)) i
    simp only [hx0, b.chi_zero, sub_zero] at this
    exact this
  rw [← h]
  refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ⟨⟨j, ?_⟩, rfl⟩
  exact lt_of_lt_of_le (Finset.mem_range.mp hj) hi

/-- The **discrete Green's function** of node `x_i`:
`g_i = χ_(0,x_i] - ((P χ_(0,x_i])(L) / L) χ_(0,L]`. -/
noncomputable def greenFn (x : ℕ → ℝ) (i : ℕ) : L2 b.L :=
  chi b.L (x i) - (prim (chi b.L (x i)) b.L / b.L) • chi b.L b.L

/-- The Green's function represents nodal evaluation on `H¹₀`: `⟪g_i, w⟫ = (P w)(x_i)`. -/
theorem inner_greenFn (x : ℕ → ℝ) (i : ℕ) {w : L2 b.L} (hw : w ∈ b.H10) :
    ⟪b.greenFn x i, w⟫_ℝ = prim w (x i) := by
  rw [greenFn, inner_sub_left, real_inner_smul_left, ← prim_apply, ← prim_apply,
    (b.mem_H10).1 hw, mul_zero, sub_zero]

/-- The discrete Green's function is a finite element function. -/
theorem greenFn_mem {x : ℕ → ℝ} {n : ℕ} (hx0 : x 0 = 0) (hxn : x n = b.L) {i : ℕ}
    (hi : i ≤ n) : b.greenFn x i ∈ b.femSpace x n := by
  refine ⟨b.pcSpace x n |>.sub_mem (b.chi_mem_pcSpace hx0 hi)
    (Submodule.smul_mem _ _ ?_), ?_⟩
  · have := b.chi_mem_pcSpace (n := n) hx0 le_rfl
    rwa [hxn] at this
  · rw [SetLike.mem_coe, mem_H10, greenFn, prim_apply, inner_sub_right, real_inner_smul_right,
      ← prim_apply, ← prim_apply, prim_chi_self, div_mul_cancel₀ _ b.L_pos.ne', sub_self]

/-- **Nodal exactness of linear finite elements** for the fixed–fixed bar: if `u ∈ H¹₀`
solves `EA ⟪u, w⟫ = ℓ(w)` on `H¹₀` and `u_h` solves the same equations on the finite element
space, then `(P u_h)(x_i) = (P u)(x_i)` at every node: the finite element displacement
interpolates the exact displacement, for every load `ℓ`. [Strang1973], §1.3. -/
theorem nodal_exact {x : ℕ → ℝ} {n : ℕ} (hx0 : x 0 = 0) (hxn : x n = b.L)
    {ℓ : L2 b.L → ℝ} {u uh : L2 b.L} (hu : u ∈ b.H10 ∧ ∀ w ∈ b.H10, b.EA * ⟪u, w⟫_ℝ = ℓ w)
    (huh : uh ∈ b.femSpace x n ∧ ∀ w ∈ b.femSpace x n, b.EA * ⟪uh, w⟫_ℝ = ℓ w) {i : ℕ}
    (hi : i ≤ n) : prim uh (x i) = prim u (x i) := by
  have hg := b.greenFn_mem hx0 hxn hi
  have h : b.EA * ⟪uh, b.greenFn x i⟫_ℝ = b.EA * ⟪u, b.greenFn x i⟫_ℝ :=
    (huh.2 _ hg).trans (hu.2 _ hg.2).symm
  have h' := mul_left_cancel₀ b.EA_pos.ne' h
  calc prim uh (x i) = ⟪b.greenFn x i, uh⟫_ℝ := (b.inner_greenFn x i huh.1.2).symm
    _ = ⟪uh, b.greenFn x i⟫_ℝ := real_inner_comm _ _
    _ = ⟪u, b.greenFn x i⟫_ℝ := h'
    _ = ⟪b.greenFn x i, u⟫_ℝ := real_inner_comm _ _
    _ = prim u (x i) := b.inner_greenFn x i hu.1

/-- **Nodal exactness for the classical problem** `EA u'' + f = 0`, `u(0) = u(L) = 0`: the
linear finite element solution `u_h` (a strain in `femSpace` with `P u_h` the displacement)
reproduces the exact displacement at every node of the mesh in `[0, L]`. -/
theorem nodal_exact_classical {x : ℕ → ℝ} {n : ℕ} (hx0 : x 0 = 0) (hxn : x n = b.L)
    {f u : ℝ → ℝ} (hf : Continuous f) (hu : ContDiff ℝ 2 u) (heq : b.Equilibrium f u)
    (hbc : b.FixedFixed u) {uh : L2 b.L}
    (huh : uh ∈ b.femSpace x n ∧
      ∀ w ∈ b.femSpace x n, b.EA * ⟪uh, w⟫_ℝ = ∫ t, f t * prim w t ∂μ b.L)
    {i : ℕ} (hi : i ≤ n) (hxi : x i ∈ Set.Icc 0 b.L) : prim uh (x i) = u (x i) := by
  obtain ⟨hw, hreal⟩ := b.weakFixedFixed_of_classical hf hu heq hbc
  rw [b.nodal_exact hx0 hxn hw huh hi, hreal _ hxi]

/-- **Existence and uniqueness** of the linear finite element solution of the bar for every
continuous linear load (Lax–Milgram on the finite element space). -/
theorem femSpace_existsUnique (x : ℕ → ℝ) (n : ℕ) (ℓ : L2 b.L →L[ℝ] ℝ) :
    ∃! uh : L2 b.L, uh ∈ b.femSpace x n ∧ ∀ w ∈ b.femSpace x n, b.EA * ⟪uh, w⟫_ℝ = ℓ w := by
  have ha : ∀ v w : L2 b.L, (b.EA • innerSL ℝ (E := L2 b.L)) v w = b.EA * ⟪v, w⟫_ℝ :=
    fun v w => by simp [innerSL_apply_apply]
  have h := Galerkin.existsUnique_galerkin_of_finiteDimensional b.EA_pos
    (a := b.EA • innerSL ℝ (E := L2 b.L))
    (fun v => by rw [ha, real_inner_self_eq_norm_sq]) ℓ (b.femSpace x n)
  simpa only [Galerkin.IsGalerkinSolution, ha] using h

/-- **Best approximation** of the strain: the linear finite element strain `u_h` is the `L²`
(energy-norm) best approximation of the exact strain `u` from the finite element space,
`‖u - u_h‖ ≤ ‖u - v_h‖` (Céa's lemma with `M / α = 1`). -/
theorem fem_best_approx {x : ℕ → ℝ} {n : ℕ} {ℓ : L2 b.L → ℝ} {u uh : L2 b.L}
    (hu : u ∈ b.H10 ∧ ∀ w ∈ b.H10, b.EA * ⟪u, w⟫_ℝ = ℓ w)
    (huh : uh ∈ b.femSpace x n ∧ ∀ w ∈ b.femSpace x n, b.EA * ⟪uh, w⟫_ℝ = ℓ w) {vh : L2 b.L}
    (hvh : vh ∈ b.femSpace x n) : ‖u - uh‖ ≤ ‖u - vh‖ := by
  have hw : uh - vh ∈ b.femSpace x n := (b.femSpace x n).sub_mem huh.1 hvh
  have h1 : b.EA * ⟪u - uh, uh - vh⟫_ℝ = 0 := by
    rw [inner_sub_left, mul_sub, huh.2 _ hw, hu.2 _ hw.2, sub_self]
  have h0 : ⟪u - uh, uh - vh⟫_ℝ = 0 := (mul_eq_zero.mp h1).resolve_left b.EA_pos.ne'
  have h2 : u - vh = (u - uh) + (uh - vh) := by abel
  have h3 : ‖u - vh‖ ^ 2 = ‖u - uh‖ ^ 2 + ‖uh - vh‖ ^ 2 := by
    rw [h2, norm_add_sq_real, h0]
    ring
  have h4 : ‖u - uh‖ ^ 2 ≤ ‖u - vh‖ ^ 2 := by rw [h3]; linarith [sq_nonneg ‖uh - vh‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h4

/-- The uniform mesh `x_i = i L / n`. -/
noncomputable def uniformNode (n : ℕ) (i : ℕ) : ℝ := i * b.L / n

/-- **Nodal exactness on the uniform mesh** `x_i = i L / n` (`n ≥ 1`). -/
theorem nodal_exact_uniform {n : ℕ} (hn : 0 < n) {ℓ : L2 b.L → ℝ} {u uh : L2 b.L}
    (hu : u ∈ b.H10 ∧ ∀ w ∈ b.H10, b.EA * ⟪u, w⟫_ℝ = ℓ w)
    (huh : uh ∈ b.femSpace (b.uniformNode n) n ∧
      ∀ w ∈ b.femSpace (b.uniformNode n) n, b.EA * ⟪uh, w⟫_ℝ = ℓ w)
    {i : ℕ} (hi : i ≤ n) : prim uh (i * b.L / n) = prim u (i * b.L / n) :=
  b.nodal_exact (x := b.uniformNode n) (by simp [uniformNode])
    (by simp [uniformNode, mul_div_cancel_left₀, (Nat.cast_pos.mpr hn).ne']) hu huh hi

end Beams.Bar

end ContinuumMechanics
