import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Long-wave limits of Bloch problems

Two reusable ingredients of frame-to-continuum convergence proofs (used for the nexorade in
`papers/Nexorade/Frame.lean`):

* **Discrete Laplacian.** For lattice vectors `t₁, …, t_m` and a wave vector `k`,
  `Σⱼ (2 cos ⟪k, tⱼ⟫ - 2) = -Σⱼ ⟪k, tⱼ⟫² + o(‖k‖²)` (`tendsto_discreteLaplacian`); for an
  isotropic family (`Σⱼ ⟪k, tⱼ⟫² = c ‖k‖²`, e.g. two orthogonal vectors of the same length `ℓ`,
  `c = ℓ²`) the symbol divided by `‖k‖²` tends to `-c` (`tendsto_discreteLaplacian_isotropic`).
* **Solutions through an adjugate.** If `N(x) M(x) = δ(x) I` (e.g. `N` the adjugate of `M`),
  `N → N₀`, the right-hand side `y → y₀` and `δ / s → δ₀ ≠ 0`, then every solution of
  `M(x) z(x) = y(x)` satisfies `s(x) z(x) → δ₀⁻¹ (N₀ y₀)` (`tendsto_smul_solution`). With `s = ‖k‖²`
  (forces) or `‖k‖⁴` (deflections) this is the long-wave limit of a Bloch problem whose determinant
  vanishes to second order at `k = 0`.
-/

open Filter Topology Matrix
open scoped InnerProductSpace

noncomputable section

namespace DiscreteMechanics

/-! ### The discrete Laplacian -/

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (t : Fin m → E)

/-- `|2 cos x - 2 + x²| ≤ x⁴ / 4` for `|x| ≤ 1`. -/
theorem abs_two_cos_sub_two_add_sq_le {x : ℝ} (hx : |x| ≤ 1) :
    |2 * Real.cos x - 2 + x ^ 2| ≤ x ^ 4 / 4 := by
  have h := Real.cos_bound hx
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
  rw [h4] at h
  rw [show 2 * Real.cos x - 2 + x ^ 2 = 2 * (Real.cos x - (1 - x ^ 2 / 2)) by ring, abs_mul,
    abs_two]
  nlinarith [sq_nonneg (x ^ 2)]

/-- **Long-wave expansion of the discrete Laplacian**:
`(Σⱼ (2 cos ⟪k, tⱼ⟫ - 2) + Σⱼ ⟪k, tⱼ⟫²) / ‖k‖² → 0` as `k → 0`. -/
theorem tendsto_discreteLaplacian :
    Tendsto (fun k : E => ((∑ j, (2 * Real.cos ⟪k, t j⟫_ℝ - 2)) + ∑ j, ⟪k, t j⟫_ℝ ^ 2) / ‖k‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  set C : ℝ := ∑ j, ‖t j‖ ^ 4 / 4
  -- eventually `‖k‖ ‖tⱼ‖ ≤ 1` for all `j`
  have hsmall : ∀ᶠ k : E in 𝓝 0, ∀ j, ‖k‖ * ‖t j‖ ≤ 1 := by
    rw [eventually_all]
    intro j
    have hc : Continuous fun k : E => ‖k‖ * ‖t j‖ := by fun_prop
    have : Tendsto (fun k : E => ‖k‖ * ‖t j‖) (𝓝 0) (𝓝 0) := by
      simpa using hc.tendsto (0 : E)
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hbound : Tendsto (fun k : E => C * ‖k‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun k : E => C * ‖k‖ ^ 2) (𝓝 0) (𝓝 (C * ‖(0 : E)‖ ^ 2)) :=
      (continuous_const.mul (continuous_norm.pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with k hk hs
  have hn : 0 < ‖k‖ := norm_pos_iff.2 hk
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (a := ‖k‖ ^ 2) (by positivity),
    div_le_iff₀ (by positivity),
    ← Finset.sum_add_distrib]
  calc |∑ j, (2 * Real.cos ⟪k, t j⟫_ℝ - 2 + ⟪k, t j⟫_ℝ ^ 2)|
      ≤ ∑ j, |2 * Real.cos ⟪k, t j⟫_ℝ - 2 + ⟪k, t j⟫_ℝ ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ⟪k, t j⟫_ℝ ^ 4 / 4 := Finset.sum_le_sum fun j _ =>
        abs_two_cos_sub_two_add_sq_le
          ((abs_real_inner_le_norm k (t j)).trans (hs j))
    _ ≤ ∑ j, (‖k‖ * ‖t j‖) ^ 4 / 4 := Finset.sum_le_sum fun j _ => by
        have h := abs_real_inner_le_norm k (t j)
        have : ⟪k, t j⟫_ℝ ^ 4 = |⟪k, t j⟫_ℝ| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
        rw [this]
        gcongr
    _ = C * ‖k‖ ^ 2 * ‖k‖ ^ 2 := by
        simp only [C, Finset.sum_mul, mul_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- For an **isotropic** family of lattice vectors (`Σⱼ ⟪k, tⱼ⟫² = c ‖k‖²`) the symbol of the
discrete Laplacian, divided by `‖k‖²`, tends to `-c`. -/
theorem tendsto_discreteLaplacian_isotropic {c : ℝ}
    (hc : ∀ k : E, ∑ j, ⟪k, t j⟫_ℝ ^ 2 = c * ‖k‖ ^ 2) :
    Tendsto (fun k : E => (∑ j, (2 * Real.cos ⟪k, t j⟫_ℝ - 2)) / ‖k‖ ^ 2) (𝓝[≠] 0) (𝓝 (-c)) := by
  have := (tendsto_discreteLaplacian t).sub_const c
  rw [zero_sub] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hn : ‖k‖ ^ 2 ≠ 0 := by positivity
  rw [hc, add_div, mul_div_cancel_right₀ _ hn, add_sub_cancel_right]

end Laplacian

/-! ### Long-wave limit of solutions -/

section Solutions

variable {X ι : Type*} [Fintype ι] [DecidableEq ι] {l : Filter X}

/-- **Long-wave limit of a Bloch solution**: if `N(x) M(x) = δ(x) I`, `N → N₀`, `y → y₀` and
`δ / s → δ₀ ≠ 0`, every solution of `M z = y` satisfies `s z → δ₀⁻¹ N₀ y₀`. -/
theorem tendsto_smul_solution {M N : X → Matrix ι ι ℂ} {δ s : X → ℂ} {y z : X → ι → ℂ}
    {N₀ : Matrix ι ι ℂ} {y₀ : ι → ℂ} {δ₀ : ℂ}
    (hNM : ∀ x, N x * M x = δ x • 1) (hN : Tendsto N l (𝓝 N₀)) (hy : Tendsto y l (𝓝 y₀))
    (hδ : Tendsto (fun x => δ x / s x) l (𝓝 δ₀)) (hδ₀ : δ₀ ≠ 0)
    (hz : ∀ᶠ x in l, M x *ᵥ z x = y x) :
    Tendsto (fun x => s x • z x) l (𝓝 (δ₀⁻¹ • (N₀ *ᵥ y₀))) := by
  have hmv : Tendsto (fun x => N x *ᵥ y x) l (𝓝 (N₀ *ᵥ y₀)) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    simp only [mulVec, dotProduct]
    refine tendsto_finsetSum _ fun j _ => Tendsto.mul ?_ ((tendsto_pi_nhds.1 hy) j)
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto N₀).comp hN
  have h2 : Tendsto (fun x => (δ x / s x)⁻¹ • (N x *ᵥ y x)) l (𝓝 (δ₀⁻¹ • (N₀ *ᵥ y₀))) :=
    (hδ.inv₀ hδ₀).smul hmv
  refine h2.congr' ?_
  filter_upwards [hz, hδ.eventually_ne hδ₀] with x hx hd
  have hδx : δ x ≠ 0 := fun h => hd (by rw [h, zero_div])
  have hsx : s x ≠ 0 := fun h => hd (by rw [h, div_zero])
  rw [← hx, mulVec_mulVec, hNM, smul_mulVec, one_mulVec, smul_smul, inv_div,
    div_mul_cancel₀ _ hδx]

end Solutions

end DiscreteMechanics
