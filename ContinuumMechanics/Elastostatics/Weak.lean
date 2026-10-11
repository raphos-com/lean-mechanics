import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Abstract weak formulation of linear elastostatics

Let `V` be the Hilbert space of kinematically admissible displacements (in applications a closed
subspace of `H¹(Ω; ℝ³)` vanishing on the clamped part of `∂Ω`), `H` the Hilbert space of strain
fields (`L²(Ω; Sym)`), `ε : V → H` the strain operator and `ℂ : H → H` the elasticity operator.
The weak problem of linear elastostatics is

`find u ∈ V:  a(u, v) = ⟪ℂ ε(u), ε(v)⟫ = ℓ(v)`  for all `v ∈ V`,

with `ℓ` the (continuous) load functional `v ↦ ∫ b·v + ∫ s·v`. Under

* `ℂ` symmetric and uniformly positive (`⟪ℂe, e⟫ ≥ c‖e‖²`), and
* **Korn's inequality** `‖v‖ ≤ K ‖ε(v)‖` on `V`,

the problem is **well posed** (Lax–Milgram) and its solution is the **unique minimiser of the total
potential energy** `J(v) = ½ a(v, v) - ℓ(v)` ([Ciarlet1988], §6.3; [Brezis2011], §9.4).

Korn's inequality, the trace theorem (continuity of `ℓ`), and the identification of `V` with a
subspace of `H¹` need Sobolev spaces on 3D domains, which Mathlib does not have; they are packaged
in the hypothesis structure `KornSetting` (see `docs/GAPS.md`). The 1D bar of `Sobolev1D/BarWeak`
is an
instance (`ε = id`, Korn with `K = 1`).

## Main results

* `KornSetting.existsUnique_weak`: well-posedness.
* `KornSetting.energy_eq_add`: `J(v) = J(u) + ½ a(v - u, v - u)`.
* `KornSetting.isMinOn_energy`, `KornSetting.eq_of_energy_eq`: `u` is the unique minimiser of `J`.

## References

* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.3.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §9.4.
-/

open scoped InnerProductSpace

namespace ContinuumMechanics

/-- **Hypothesis structure** for the weak formulation of linear elastostatics: a strain operator
`ε : V → H`, a symmetric uniformly positive elasticity operator `ℂ`, and **Korn's inequality**
`‖v‖ ≤ K ‖ε v‖`. [Ciarlet1988], §6.3. See `docs/GAPS.md`. -/
structure KornSetting (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The strain operator `ε`. -/
  strain : V →L[ℝ] H
  /-- The elasticity operator `ℂ`. -/
  C : H →L[ℝ] H
  C_symm : ∀ e f, ⟪C e, f⟫_ℝ = ⟪e, C f⟫_ℝ
  /-- Uniform positivity constant of `ℂ`. -/
  c : ℝ
  c_pos : 0 < c
  C_pos : ∀ e, c * ‖e‖ ^ 2 ≤ ⟪C e, e⟫_ℝ
  /-- Korn constant. -/
  K : ℝ
  K_pos : 0 < K
  korn : ∀ v, ‖v‖ ≤ K * ‖strain v‖

namespace KornSetting

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : KornSetting V H)

/-- The **energy bilinear form** `a(u, v) = ⟪ℂ ε u, ε v⟫`. -/
noncomputable def form : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip S.strain).comp ((innerSL ℝ).comp (S.C.comp S.strain))

theorem form_apply (u v : V) : S.form u v = ⟪S.C (S.strain u), S.strain v⟫_ℝ := by
  simp [form, ContinuousLinearMap.compL_apply, innerSL_apply_apply]

theorem form_comm (u v : V) : S.form u v = S.form v u := by
  rw [form_apply, form_apply, S.C_symm, real_inner_comm]

/-- `a(v, v) ≥ (c / K²) ‖v‖²`, from positivity of `ℂ` and Korn's inequality. -/
theorem form_coercive_bound (v : V) : S.c / S.K ^ 2 * ‖v‖ ^ 2 ≤ S.form v v := by
  rw [form_apply]
  refine le_trans ?_ (S.C_pos _)
  have hK := S.K_pos
  have hk := S.korn v
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : ‖v‖ ^ 2 ≤ (S.K * ‖S.strain v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hk 2
  nlinarith [S.c_pos]

theorem form_nonneg (v : V) : 0 ≤ S.form v v :=
  le_trans (by have := S.c_pos; have := S.K_pos; positivity) (S.form_coercive_bound v)

theorem isCoercive : IsCoercive S.form :=
  ⟨S.c / S.K ^ 2, by have := S.c_pos; have := S.K_pos; positivity, fun v => by
    rw [mul_assoc, ← sq]; exact S.form_coercive_bound v⟩

/-- **Well-posedness of the weak problem** (Lax–Milgram). [Ciarlet1988], Thm. 6.3-2. -/
theorem existsUnique_weak [CompleteSpace V] (ℓ : V →L[ℝ] ℝ) : ∃! u : V, ∀ v, S.form u v = ℓ v := by
  set g := (InnerProductSpace.toDual ℝ V).symm ℓ
  have hg : ∀ w, ⟪g, w⟫_ℝ = ℓ w := fun w => InnerProductSpace.toDual_symm_apply
  have hc := S.isCoercive
  refine ⟨hc.continuousLinearEquivOfBilin.symm g, fun w => ?_, fun v hv => ?_⟩
  · rw [← hc.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hg]
  · have := hc.unique_continuousLinearEquivOfBilin (v := v) (f := g) fun w => by rw [hg, hv]
    rw [this, ContinuousLinearEquiv.symm_apply_apply]

/-- The **total potential energy** `J(v) = ½ a(v, v) - ℓ(v)`. -/
noncomputable def energy (ℓ : V →L[ℝ] ℝ) (v : V) : ℝ := 2⁻¹ * S.form v v - ℓ v

/-- `J(v) = J(u) + ½ a(v - u, v - u)` for the weak solution `u`. [Ciarlet1988], Thm. 6.3-2. -/
theorem energy_eq_add {ℓ : V →L[ℝ] ℝ} {u : V} (hu : ∀ v, S.form u v = ℓ v) (v : V) :
    S.energy ℓ v = S.energy ℓ u + 2⁻¹ * S.form (v - u) (v - u) := by
  have h1 := hu (v - u)
  have h2 := S.form_comm u v
  have h3 := hu u
  simp only [energy, map_sub, sub_apply] at h1 ⊢
  linarith

/-- **Principle of minimum potential energy**: the weak solution minimises `J`. -/
theorem isMinOn_energy {ℓ : V →L[ℝ] ℝ} {u : V} (hu : ∀ v, S.form u v = ℓ v) :
    IsMinOn (S.energy ℓ) Set.univ u := fun v _ => by
  change S.energy ℓ u ≤ S.energy ℓ v
  rw [S.energy_eq_add hu v]
  linarith [S.form_nonneg (v - u)]

/-- The minimiser is unique: `J(v) = J(u)` forces `v = u`. -/
theorem eq_of_energy_eq {ℓ : V →L[ℝ] ℝ} {u : V} (hu : ∀ v, S.form u v = ℓ v) {v : V}
    (hv : S.energy ℓ v = S.energy ℓ u) : v = u := by
  rw [S.energy_eq_add hu v, add_eq_left, mul_eq_zero] at hv
  have h0 : S.form (v - u) (v - u) = 0 := hv.resolve_left (by norm_num)
  have hb := S.form_coercive_bound (v - u)
  rw [h0] at hb
  have : ‖v - u‖ ^ 2 ≤ 0 := by
    have hpos : 0 < S.c / S.K ^ 2 := by have := S.c_pos; have := S.K_pos; positivity
    nlinarith [sq_nonneg ‖v - u‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm this (sq_nonneg _))))

end KornSetting

/-- **Non-vacuity**: an isotropic material `ℂ = k I` with `ε = id` (the setting of the 1D bar,
`V = H`) satisfies the hypotheses with `c = k`, `K = 1`. -/
noncomputable def KornSetting.ofIdentity (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k : ℝ} (hk : 0 < k) : KornSetting V V where
  strain := ContinuousLinearMap.id ℝ V
  C := k • ContinuousLinearMap.id ℝ V
  C_symm e f := by simp [real_inner_smul_left, real_inner_smul_right]
  c := k
  c_pos := hk
  C_pos e := by simp [real_inner_smul_left]
  K := 1
  K_pos := one_pos
  korn v := by simp

end ContinuumMechanics
