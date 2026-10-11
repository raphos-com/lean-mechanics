import ClassicalMechanics.Particles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The virial theorem

For a system of particles, the **virial** `G = Σ mᵢ xᵢ · vᵢ` satisfies (`hasDerivAt_virialG`)

`Ġ = 2T + Σ xᵢ · Fᵢ`,

where `Fᵢ = Σⱼ Fᵢⱼ + Fᵢᵉ` is the total force on particle `i` and `T` the kinetic energy. The
**virial theorem** (`virial`) follows by averaging over a long time: if `G` stays bounded (for
instance, if the motion stays in a bounded region of phase space), the time average of
`2T + Σ xᵢ · Fᵢ` over `[0, τ]` tends to `0` as `τ → ∞`, i.e. `⟨2T⟩ = -⟨Σ xᵢ · Fᵢ⟩`.

For a potential energy homogeneous of degree `k` (Euler's identity `Σ xᵢ · Fᵢ = -k U`),
`virial_homogeneous` gives `⟨2T⟩ = k ⟨U⟩`: `⟨2T⟩ = -⟨U⟩` for Kepler/Coulomb forces (`k = -1`)
and `⟨T⟩ = ⟨U⟩` for harmonic forces (`k = 2`).

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §3.4.
* [Landau1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §10.
-/

open Matrix Filter Topology

noncomputable section

namespace ClassicalMechanics

namespace ParticleSystem

variable {ι : Type*} [Fintype ι] (S : ParticleSystem ι)

/-- The virial `G = Σ mᵢ xᵢ · vᵢ`. -/
def virialG (t : ℝ) : ℝ := ∑ i, S.m i * (S.x t i ⬝ᵥ S.v t i)

/-- The virial of the forces, `Σ xᵢ · Fᵢ`. -/
def virialF (t : ℝ) : ℝ := ∑ i, S.x t i ⬝ᵥ (∑ j, S.F t i j + S.Fe t i)

/-- `Ġ = 2T + Σ xᵢ · Fᵢ`. -/
theorem hasDerivAt_virialG (t : ℝ) :
    HasDerivAt S.virialG (2 * S.kinetic t + S.virialF t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_dot (S.hasDerivAt_x t i) (S.hasDerivAt_v t i)).const_mul (S.m i)
  convert h using 1
  · rfl
  simp only [kinetic, virialF, normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← S.newton t i, dotProduct_smul, smul_eq_mul]
  ring

/-- Integrated form: `G(τ) - G(0) = ∫₀^τ (2T + Σ xᵢ · Fᵢ)`, for continuous accelerations. -/
theorem integral_eq (ha : ∀ i, Continuous fun t => S.a t i) (τ : ℝ) :
    ∫ t in (0)..τ, (2 * S.kinetic t + S.virialF t) = S.virialG τ - S.virialG 0 := by
  have hx : ∀ i, Continuous fun t => S.x t i := fun i =>
    continuous_iff_continuousAt.2 fun t => (S.hasDerivAt_x t i).continuousAt
  have hv : ∀ i, Continuous fun t => S.v t i := fun i =>
    continuous_iff_continuousAt.2 fun t => (S.hasDerivAt_v t i).continuousAt
  -- the integrand is `Σ mᵢ (|vᵢ|² + xᵢ · aᵢ)`, which is continuous
  have e : (fun t => 2 * S.kinetic t + S.virialF t) =
      fun t => ∑ i, S.m i * (S.v t i ⬝ᵥ S.v t i + S.x t i ⬝ᵥ S.a t i) := by
    funext t
    simp only [kinetic, virialF, normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← S.newton t i, dotProduct_smul, smul_eq_mul]
    ring
  have hc : Continuous fun t => 2 * S.kinetic t + S.virialF t := by
    rw [e]
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    simp only [dotProduct]
    exact (continuous_finsetSum _ fun k _ =>
      ((continuous_apply k).comp (hv i)).mul ((continuous_apply k).comp (hv i))).add
      (continuous_finsetSum _ fun k _ =>
        ((continuous_apply k).comp (hx i)).mul ((continuous_apply k).comp (ha i)))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => S.hasDerivAt_virialG t)
    (hc.intervalIntegrable _ _)

/-- **Virial theorem**: if the virial `G` stays bounded, the time average of
`2T + Σ xᵢ · Fᵢ` over `[0, τ]` tends to `0`: `⟨2T⟩ = -⟨Σ xᵢ · Fᵢ⟩`. -/
theorem virial (ha : ∀ i, Continuous fun t => S.a t i) {C : ℝ} (hG : ∀ t, |S.virialG t| ≤ C) :
    Tendsto (fun τ => τ⁻¹ * ∫ t in (0)..τ, (2 * S.kinetic t + S.virialF t)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun τ : ℝ => 2 * C * τ⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (2 * C)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [S.integral_eq ha, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hτ, mul_comm]
  have h1 : |S.virialG τ - S.virialG 0| ≤ 2 * C := by
    have := abs_sub (S.virialG τ) (S.virialG 0)
    linarith [hG τ, hG 0]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hτ.le)

/-- **Virial theorem for homogeneous potentials**: if `Σ xᵢ · Fᵢ = -k U` (Euler's identity for a
potential energy `U` homogeneous of degree `k`), then `⟨2T - kU⟩ → 0`, i.e. `⟨2T⟩ = k ⟨U⟩`. -/
theorem virial_homogeneous (ha : ∀ i, Continuous fun t => S.a t i) {C : ℝ}
    (hG : ∀ t, |S.virialG t| ≤ C) {U : ℝ → ℝ} {k : ℝ} (hU : ∀ t, S.virialF t = -k * U t) :
    Tendsto (fun τ => τ⁻¹ * ∫ t in (0)..τ, (2 * S.kinetic t - k * U t)) atTop (𝓝 0) := by
  convert S.virial ha hG using 3 with τ
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hU]
  ring

end ParticleSystem

end ClassicalMechanics
