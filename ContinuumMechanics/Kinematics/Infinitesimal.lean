import ContinuumMechanics.Kinematics.Strain

/-!
# Infinitesimal strain

For a displacement gradient `H = ∇u` (so `F = I + H`), the **infinitesimal strain** is
`ε = sym H` ([Gurtin1981], §§7, 12; [Ciarlet1988], §6.2). It is the linearisation of the
Green–Lagrange strain: exactly,

`E(I + H) = ε(H) + ½ Hᵀ H`,

so `‖E - ε‖ ≤ ½ ‖H‖²` (operator norm) — a quantitative form of `E = ε + O(‖H‖²)`.

## Main results

* `Lin.greenLagrange_one_add`: `E(I + H) = sym H + ½ HᵀH`.
* `Lin.norm_greenLagrange_sub_sym_le`: `‖E(I + H) - sym H‖ ≤ ½ ‖H‖²`.
* `Lin.hasDerivAt_greenLagrange`: `d/dt E(I + tH)|_{t=0} = sym H`.
* `Lin.sym_eq_zero_iff`: the infinitesimal strain vanishes iff `H` is skew.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §§7, 12.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.2.
-/

open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Lin

/-- `E(I + H) = sym H + ½ Hᵀ H`. [Ciarlet1988], §1.8. -/
theorem greenLagrange_one_add (H : Lin E) :
    greenLagrange (1 + H) = sym H + (2⁻¹ : ℝ) • (Hᵀ * H) := by
  rw [greenLagrange, rightCG, transpose_add, transpose_one, sym_apply]
  noncomm_ring
  module

/-- **Linearisation of the Green–Lagrange strain**: `‖E(I + H) - ε(H)‖ ≤ ½ ‖H‖²`.
[Gurtin1981], §12. -/
theorem norm_greenLagrange_sub_sym_le (H : Lin E) :
    ‖greenLagrange (1 + H) - sym H‖ ≤ 2⁻¹ * ‖H‖ ^ 2 := by
  rw [greenLagrange_one_add, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by norm_num)]
  gcongr
  calc ‖Hᵀ * H‖ ≤ ‖Hᵀ‖ * ‖H‖ := norm_mul_le _ _
    _ = ‖H‖ ^ 2 := by rw [transpose_eq_adjoint, LinearIsometryEquiv.norm_map, sq]

/-- The infinitesimal strain is the derivative of the Green–Lagrange strain:
`d/dt E(I + tH)|_{t=0} = sym H`. -/
theorem hasDerivAt_greenLagrange (H : Lin E) :
    HasDerivAt (fun t : ℝ => greenLagrange (1 + t • H)) (sym H) 0 := by
  have e : (fun t : ℝ => greenLagrange (1 + t • H)) =
      fun t => t • sym H + (t ^ 2) • ((2⁻¹ : ℝ) • (Hᵀ * H)) := by
    ext1 t
    rw [greenLagrange_one_add, map_smul, transpose_smul, smul_mul_smul_comm]
    module
  rw [e]
  have h1 := (hasDerivAt_id (0 : ℝ)).smul_const (sym H)
  have h2 := ((hasDerivAt_pow 2 (0 : ℝ)).smul_const ((2⁻¹ : ℝ) • (Hᵀ * H)))
  convert h1.add h2 using 1
  · ext t; simp
  · simp

/-- The infinitesimal strain vanishes iff the displacement gradient is skew (an infinitesimal
rotation). [Gurtin1981], §12. -/
theorem sym_eq_zero_iff {H : Lin E} : sym H = 0 ↔ H ∈ Skw E := by
  constructor
  · intro h
    rw [← skw_eq_self_iff, ← sym_add_skw H, h, zero_add, skw_skw]
  · exact sym_eq_zero_of_mem_skw

end Lin

end ContinuumMechanics
