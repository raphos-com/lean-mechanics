import ContinuumMechanics.Sobolev1D.BeamWeak

/-!
# Weak Euler–Bernoulli beams with clamped–clamped and clamped–pinned ends

As in `Sobolev1D.BeamWeak`, the unknown is the curvature `κ = w'' ∈ L²` and the deflection is the
double primitive `w = P² κ`, which builds in the clamped conditions `w(0) = w'(0) = 0` at `x = 0`.
The boundary conditions at `x = L` become linear constraints on `κ`:

* **clamped–clamped** (`w(L) = w'(L) = 0`): `(P κ)(L) = ∫₀ᴸ κ = 0` and
  `(P² κ)(L) = ∫₀ᴸ (L - t) κ(t) dt = 0`; the admissible curvatures form the closed subspace
  `H20 = ker (κ ↦ ((P κ)(L), (P² κ)(L)))`;
* **clamped–pinned** (propped cantilever, `w(L) = 0`, `w''(L) = 0` natural): only
  `(P² κ)(L) = 0`; the admissible curvatures form the closed subspace `HCP = ker (κ ↦ (P² κ)(L))`.

On either subspace `S` the principle of virtual work reads

`κ ∈ S`, `EI ⟪κ, η⟫ = ∫₀ᴸ q (P² η)` for all `η ∈ S`,

which is **well posed** by Lax–Milgram (a kernel of continuous linear functionals is closed, hence
complete). A classical `C⁴` solution of `EI w'''' = q` with the corresponding boundary conditions
gives the weak solution `κ = w''`, and `P² w'' = w` ([Reddy2007], §4.2).

The key identity is the general bending-moment formula
`EI w''(t) = EI w''(L) - EI w'''(L) (L - t) + ∫_tᴸ ∫_sᴸ q`, which yields, for every `η ∈ L²`,
`EI ⟪w'', η⟫ = EI w''(L) (P η)(L) - EI w'''(L) (P² η)(L) + ∫₀ᴸ q (P² η)`.

## Main results

* `Sobolev1D.existsUnique_weak_submodule`: Lax–Milgram on a complete subspace.
* `Sobolev1D.prim_primL2_end`: `(P² κ)(L) = ∫₀ᴸ (L - t) κ(t) dt`.
* `Beams.EBBeam.moment_eq`, `Beams.EBBeam.virtualWork`: the general moment / virtual-work identity.
* `Beams.EBBeam.weakClampedClamped_existsUnique`, `Beams.EBBeam.weakClampedClamped_of_classical`.
* `Beams.EBBeam.weakClampedPinned_existsUnique`, `Beams.EBBeam.weakClampedPinned_of_classical`.

## References

* [Reddy2007] J. N. Reddy, *An Introduction to the Finite Element Method*, §4.2.
* [Brezis2011] H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, §8.4.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §9.2.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace

namespace ContinuumMechanics

namespace Sobolev1D

/-- **Lax–Milgram on a complete subspace** `S`: for `k > 0` and every continuous linear `ℓ` there
is exactly one `v ∈ S` with `k ⟪v, w⟫ = ℓ(w)` for all `w ∈ S`. [Brezis2011], Cor. 5.8. -/
theorem existsUnique_weak_submodule {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (S : Submodule ℝ V) [CompleteSpace S] {k : ℝ} (hk : 0 < k) (ℓ : V →L[ℝ] ℝ) :
    ∃! v : V, v ∈ S ∧ ∀ w ∈ S, k * ⟪v, w⟫_ℝ = ℓ w := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_weak hk (ℓ.comp S.subtypeL)
  refine ⟨v, ⟨v.2, fun w hw => hv ⟨w, hw⟩⟩, fun v' hv' => ?_⟩
  have := huniq ⟨v', hv'.1⟩ fun w => hv'.2 w w.2
  rw [← this]

variable {L : ℝ}

/-- `⟪1, v⟫ = (P v)(L)`, with `1` written as `toL2` of a constant. -/
theorem inner_one_eq (h1 : Continuous fun _ : ℝ => (1 : ℝ)) (v : L2 L) :
    ⟪toL2 (L := L) h1, v⟫_ℝ = prim v L :=
  (prim_end v).symm

/-- `(P² κ)(L) = ∫₀ᴸ (L - t) κ(t) dt`. -/
theorem prim_primL2_end (hL : 0 ≤ L) (κ : L2 L) :
    prim (primL2 hL κ) L = ∫ t, (L - t) * κ t ∂μ L := by
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  rw [← inner_one_eq h1, ← inner_resultant_eq hL h1, inner_toL2]
  refine integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioc fun t _ => ?_)
  simp [resultant]

end Sobolev1D

namespace Beams.EBBeam

open Sobolev1D

variable (b : EBBeam)

/-! ### Admissible curvatures -/

/-- The end-constraint map `κ ↦ ((P κ)(L), (P² κ)(L)) = (w'(L), w(L))`. -/
noncomputable def endCLM : L2 b.L →L[ℝ] ℝ × ℝ :=
  (primCLM b.L b.L).prod ((primCLM b.L b.L).comp (primL2 b.L_pos.le))

/-- Admissible curvatures of the **clamped–clamped** beam: `(P κ)(L) = (P² κ)(L) = 0`. -/
noncomputable def H20 : Submodule ℝ (L2 b.L) := LinearMap.ker (b.endCLM : L2 b.L →ₗ[ℝ] ℝ × ℝ)

/-- Membership in `H20`: `w'(L) = (P κ)(L) = 0` and `w(L) = (P² κ)(L) = 0`. -/
theorem mem_H20 {κ : L2 b.L} :
    κ ∈ b.H20 ↔ prim κ b.L = 0 ∧ prim (primL2 b.L_pos.le κ) b.L = 0 := by
  simp only [H20, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, endCLM,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, Prod.mk_eq_zero]
  rfl

instance : CompleteSpace b.H20 :=
  (ContinuousLinearMap.isClosed_ker b.endCLM).completeSpace_coe

/-- Admissible curvatures of the **clamped–pinned** beam: `(P² κ)(L) = 0`. -/
noncomputable def HCP : Submodule ℝ (L2 b.L) :=
  LinearMap.ker ((primCLM b.L b.L).comp (primL2 b.L_pos.le) : L2 b.L →ₗ[ℝ] ℝ)

/-- Membership in `HCP`: `w(L) = (P² κ)(L) = 0`. -/
theorem mem_HCP {κ : L2 b.L} : κ ∈ b.HCP ↔ prim (primL2 b.L_pos.le κ) b.L = 0 := Iff.rfl

instance : CompleteSpace b.HCP :=
  (ContinuousLinearMap.isClosed_ker ((primCLM b.L b.L).comp (primL2 b.L_pos.le))).completeSpace_coe

/-- Clamped–clamped curvatures are admissible for the clamped–pinned beam. -/
theorem H20_le_HCP : b.H20 ≤ b.HCP := fun _ h => ((b.mem_H20).1 h).2

/-! ### Weak problems and well-posedness -/

/-- The distributed-load functional `η ↦ ∫₀ᴸ q (P² η)`. -/
noncomputable def loadDist (q : ℝ → ℝ) (η : L2 b.L) : ℝ :=
  ∫ x, q x * prim (primL2 b.L_pos.le η) x ∂μ b.L

/-- The distributed-load functional is continuous and linear. -/
noncomputable def loadDistCLM {q : ℝ → ℝ} (hq : Continuous q) : L2 b.L →L[ℝ] ℝ :=
  (innerSL ℝ (toL2 (continuous_resultant (L := b.L) hq))).comp (primL2 b.L_pos.le)

/-- `loadDistCLM` evaluates to `loadDist`. -/
theorem loadDistCLM_apply {q : ℝ → ℝ} (hq : Continuous q) (η : L2 b.L) :
    b.loadDistCLM hq η = b.loadDist q η := by
  simp only [loadDistCLM, ContinuousLinearMap.comp_apply, innerSL_apply_apply, loadDist,
    integral_mul_prim_eq hq]

/-- The **weak form** of the clamped–clamped beam under the distributed load `q`. -/
def WeakClampedClamped (q : ℝ → ℝ) (κ : L2 b.L) : Prop :=
  κ ∈ b.H20 ∧ ∀ η ∈ b.H20, b.EI * ⟪κ, η⟫_ℝ = b.loadDist q η

/-- The **weak form** of the clamped–pinned (propped cantilever) beam under the load `q`. -/
def WeakClampedPinned (q : ℝ → ℝ) (κ : L2 b.L) : Prop :=
  κ ∈ b.HCP ∧ ∀ η ∈ b.HCP, b.EI * ⟪κ, η⟫_ℝ = b.loadDist q η

/-- **Well-posedness** of the clamped–clamped beam (Lax–Milgram on `H20`). -/
theorem weakClampedClamped_existsUnique {q : ℝ → ℝ} (hq : Continuous q) :
    ∃! κ, b.WeakClampedClamped q κ := by
  obtain ⟨κ, hκ, huniq⟩ := existsUnique_weak_submodule b.H20 b.EI_pos (b.loadDistCLM hq)
  refine ⟨κ, ⟨hκ.1, fun η hη => (hκ.2 η hη).trans (b.loadDistCLM_apply hq η)⟩,
    fun κ' hκ' => huniq κ' ⟨hκ'.1, fun η hη => ?_⟩⟩
  rw [hκ'.2 η hη, b.loadDistCLM_apply hq]

/-- **Well-posedness** of the clamped–pinned beam (Lax–Milgram on `HCP`). -/
theorem weakClampedPinned_existsUnique {q : ℝ → ℝ} (hq : Continuous q) :
    ∃! κ, b.WeakClampedPinned q κ := by
  obtain ⟨κ, hκ, huniq⟩ := existsUnique_weak_submodule b.HCP b.EI_pos (b.loadDistCLM hq)
  refine ⟨κ, ⟨hκ.1, fun η hη => (hκ.2 η hη).trans (b.loadDistCLM_apply hq η)⟩,
    fun κ' hκ' => huniq κ' ⟨hκ'.1, fun η hη => ?_⟩⟩
  rw [hκ'.2 η hη, b.loadDistCLM_apply hq]

/-! ### Classical solutions are weak solutions -/

/-- The curvature `w''` of a `C⁴` deflection, as an element of `L²`. -/
noncomputable def curvature {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) : L2 b.L :=
  toL2 (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous

variable {b}

/-- The **bending moment** of a classical solution:
`EI w''(t) = EI w''(L) - EI w'''(L) (L - t) + ∫_tᴸ ∫_sᴸ q`. [TimoshenkoGere1997], §9.2. -/
theorem moment_eq {q w : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w) (heq : b.Equation q w)
    {t : ℝ} (ht : t ∈ Icc 0 b.L) :
    b.EI * iteratedDeriv 2 w t = b.EI * iteratedDeriv 2 w b.L -
      b.EI * iteratedDeriv 3 w b.L * (b.L - t) + resultant b.L (resultant b.L q) t := by
  have c2 : ContDiff ℝ 2 (iteratedDeriv 2 w) := contDiff_iteratedDeriv hw rfl
  have c3 : ContDiff ℝ 1 (iteratedDeriv 3 w) := contDiff_iteratedDeriv hw rfl
  have d2 : deriv (iteratedDeriv 2 w) = iteratedDeriv 3 w := (iteratedDeriv_succ).symm
  have d3 : deriv (iteratedDeriv 3 w) = iteratedDeriv 4 w := (iteratedDeriv_succ).symm
  -- shear force
  have hV : ∀ s ∈ Icc 0 b.L, b.EI * iteratedDeriv 3 w s =
      b.EI * iteratedDeriv 3 w b.L - resultant b.L q s := fun s hs => by
    rw [eq_sub_integral_deriv c3 s b.L, d3, mul_sub, ← intervalIntegral.integral_const_mul,
      resultant]
    have : ∫ x in s..b.L, b.EI * iteratedDeriv 4 w x = ∫ x in s..b.L, q x :=
      integral_congr fun x hx => by
        rw [uIcc_of_le hs.2] at hx
        exact heq x ⟨hs.1.trans hx.1, hx.2⟩
    rw [this]
  have hR : Continuous (resultant b.L q) := continuous_resultant hq
  rw [eq_sub_integral_deriv (c2.of_le one_le_two) t b.L, d2, mul_sub,
    ← intervalIntegral.integral_const_mul]
  have : ∫ x in t..b.L, b.EI * iteratedDeriv 3 w x =
      ∫ x in t..b.L, (b.EI * iteratedDeriv 3 w b.L - resultant b.L q x) :=
    integral_congr fun x hx => by
      rw [uIcc_of_le ht.2] at hx
      exact hV x ⟨ht.1.trans hx.1, hx.2⟩
  rw [this, intervalIntegral.integral_sub intervalIntegrable_const (hR.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul,
    show resultant b.L (resultant b.L q) t = ∫ x in t..b.L, resultant b.L q x from rfl]
  ring

/-- The **virtual-work identity** of a classical solution: for every `η ∈ L²`,
`EI ⟪w'', η⟫ = EI w''(L) (P η)(L) - EI w'''(L) (P² η)(L) + ∫₀ᴸ q (P² η)`. -/
theorem virtualWork {q w : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w)
    (heq : b.Equation q w) (η : L2 b.L) :
    b.EI * ⟪b.curvature hw, η⟫_ℝ = b.EI * iteratedDeriv 2 w b.L * prim η b.L -
      b.EI * iteratedDeriv 3 w b.L * prim (primL2 b.L_pos.le η) b.L + b.loadDist q η := by
  have hL := b.L_pos.le
  have hR := continuous_resultant (L := b.L) hq
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  set c₁ := b.EI * iteratedDeriv 2 w b.L
  set c₂ := -(b.EI * iteratedDeriv 3 w b.L)
  have hM : b.EI • b.curvature hw = c₁ • toL2 h1 + c₂ • toL2 (continuous_resultant (L := b.L) h1)
      + toL2 (continuous_resultant (L := b.L) hR) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul b.EI (b.curvature hw),
      Lp.coeFn_add (c₁ • toL2 h1 + c₂ • toL2 (continuous_resultant (L := b.L) h1))
        (toL2 (continuous_resultant (L := b.L) hR)),
      Lp.coeFn_add (c₁ • toL2 (L := b.L) h1) (c₂ • toL2 (continuous_resultant (L := b.L) h1)),
      Lp.coeFn_smul c₁ (toL2 (L := b.L) h1),
      Lp.coeFn_smul c₂ (toL2 (continuous_resultant (L := b.L) h1)),
      toL2_ae_eq (L := b.L) (contDiff_iteratedDeriv hw (n := 2) (k := 2) rfl).continuous,
      toL2_ae_eq (L := b.L) h1,
      toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) h1),
      toL2_ae_eq (L := b.L) (continuous_resultant (L := b.L) hR),
      ae_restrict_mem measurableSet_Ioc] with t e1 e2 e3 e4 e5 e6 e7 e8 e9 ht
    rw [e1, e2, Pi.add_apply, e3, Pi.add_apply, e4, e5, Pi.smul_apply, Pi.smul_apply,
      Pi.smul_apply, curvature, e6, e7, e8, e9, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      moment_eq hq hw heq (Ioc_subset_Icc_self ht)]
    simp only [c₁, c₂, resultant, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  rw [← real_inner_smul_left, hM, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, inner_one_eq, inner_resultant_eq hL h1, inner_one_eq,
    inner_resultant_eq hL hR, loadDist, integral_mul_prim_eq hq]
  ring

/-- `(P w'')(x) = w'(x) - w'(0)` on `[0, L]`. -/
theorem prim_curvature {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) {x : ℝ} (hx : x ∈ Icc 0 b.L) :
    prim (b.curvature hw) x = iteratedDeriv 1 w x - iteratedDeriv 1 w 0 := by
  have hw1 : ContDiff ℝ 1 (deriv w) := by
    have := contDiff_iteratedDeriv hw (n := 3) (k := 1) rfl
    rw [iteratedDeriv_one] at this
    exact this.of_le (by norm_num)
  have hd2 : iteratedDeriv 2 w = deriv (deriv w) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [curvature, prim_toL2 _ hx, hd2, iteratedDeriv_one, integral_deriv_eq_sub' (deriv w) rfl
    (fun t _ => (hw1.differentiable one_ne_zero) t) (hw1.continuous_deriv le_rfl).continuousOn]

/-- `(P² w'')(x) = w(x)` on `[0, L]` when `w(0) = w'(0) = 0`. -/
theorem prim_primL2_curvature {w : ℝ → ℝ} (hw : ContDiff ℝ 4 w) (h0 : w 0 = 0)
    (h1 : iteratedDeriv 1 w 0 = 0) {x : ℝ} (hx : x ∈ Icc 0 b.L) :
    prim (primL2 b.L_pos.le (b.curvature hw)) x = w x := by
  have hw1 : ContDiff ℝ 1 (deriv w) := by
    have := contDiff_iteratedDeriv hw (n := 3) (k := 1) rfl
    rw [iteratedDeriv_one] at this
    exact this.of_le (by norm_num)
  rw [primL2_apply, prim_toL2 (continuous_prim _) hx]
  have : ∫ y in (0 : ℝ)..x, prim (b.curvature hw) y = ∫ y in (0 : ℝ)..x, deriv w y :=
    integral_congr fun y hy => by
      rw [uIcc_of_le hx.1] at hy
      rw [prim_curvature hw ⟨hy.1, hy.2.trans hx.2⟩, h1, sub_zero, iteratedDeriv_one]
  rw [this, integral_deriv_eq_sub' w rfl (fun t _ => (hw.differentiable (by norm_num)) t)
    hw1.continuous.continuousOn, h0, sub_zero]

/-- **Classical ⇒ weak** (clamped–clamped): the curvature `w''` of a classical solution solves
the weak problem, and `P² w'' = w`. -/
theorem weakClampedClamped_of_classical {q w : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w)
    (heq : b.Equation q w) (hbc : b.ClampedClamped w) :
    b.WeakClampedClamped q (b.curvature hw) ∧
      ∀ x ∈ Icc 0 b.L, prim (primL2 b.L_pos.le (b.curvature hw)) x = w x := by
  have hLm : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  have hrec := fun x (hx : x ∈ Icc 0 b.L) => prim_primL2_curvature hw hbc.1 hbc.2.1 hx
  refine ⟨⟨(b.mem_H20).2 ⟨?_, ?_⟩, fun η hη => ?_⟩, hrec⟩
  · rw [prim_curvature hw hLm, hbc.2.1, hbc.2.2.2, sub_zero]
  · rw [hrec _ hLm, hbc.2.2.1]
  · obtain ⟨e1, e2⟩ := (b.mem_H20).1 hη
    rw [virtualWork hq hw heq, e1, e2]
    ring

/-- **Classical ⇒ weak** (clamped–pinned, propped cantilever): the curvature `w''` of a classical
solution solves the weak problem, and `P² w'' = w`. -/
theorem weakClampedPinned_of_classical {q w : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w)
    (heq : b.Equation q w) (hbc : b.ClampedPinned w) :
    b.WeakClampedPinned q (b.curvature hw) ∧
      ∀ x ∈ Icc 0 b.L, prim (primL2 b.L_pos.le (b.curvature hw)) x = w x := by
  have hLm : b.L ∈ Icc 0 b.L := ⟨b.L_pos.le, le_rfl⟩
  have hrec := fun x (hx : x ∈ Icc 0 b.L) => prim_primL2_curvature hw hbc.1 hbc.2.1 hx
  refine ⟨⟨?_, fun η hη => ?_⟩, hrec⟩
  · rw [mem_HCP, hrec _ hLm, hbc.2.2.1]
  · rw [virtualWork hq hw heq, (b.mem_HCP).1 hη, hbc.2.2.2]
    ring

end Beams.EBBeam

end ContinuumMechanics
