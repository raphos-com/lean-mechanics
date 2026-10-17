# Topology optimization: a Lean formalization

Machine-checked formalization (Lean 4 + Mathlib, no axioms, no `sorry`) of the mathematical core of
density-based topology optimization by compliance minimization (the SIMP method):

> O. Sigmund, **Topology optimization: a tool for the tailoring of structures and materials**,
> Phil. Trans. R. Soc. Lond. A 358, 211–227 (2000).
>
> M. P. Bendsøe, N. Kikuchi, **Generating optimal topologies in structural design using a
> homogenization method**, Comput. Methods Appl. Mech. Engrg. 71, 197–224 (1988).
>
> O. Sigmund, **A 99 line topology optimization code written in Matlab**, Struct. Multidisc.
> Optim. 21, 120–127 (2001).
>
> M. P. Bendsøe, O. Sigmund, **Topology Optimization: Theory, Methods and Applications**,
> Springer (2003).

Sigmund (2000) is a survey: it describes the method (finite-element discretization, element
densities as design variables, sensitivity analysis, iterative update, filtering against mesh
dependency) without equations. The statements below are the standard discrete formulation of that
method, as in the 99-line code and Bendsøe–Sigmund §1.2.

The design is a density (or weight) `wₑ` per element, with stiffness `K(w) = Σₑ wₑ Kₑ`
(`wₑ = xₑᵖ` for SIMP), displacement `K u = f` and compliance `c = fᵀu`.

✅ proved as stated.

| Claim | Lean | Status |
|---|---|---|
| Compliance is the strain energy `uᵀKu`, `c ≥ 0`, `c > 0` for `f ≠ 0` | `Compliance`: `compliance_eq_energy`, `compliance_nonneg`, `compliance_pos` | ✅ |
| Complementary energy: `c(w) = sup_v (2fᵀv − Σ wₑ vᵀKₑv)` | `compliance_variational`, `compliance_isGreatest`, `compliance_eq_iSup` | ✅ |
| Adding material never increases compliance | `compliance_antitone` | ✅ |
| Compliance is convex in linear stiffness weights (variable-thickness sheet, `p = 1`) | `compliance_convexOn`, `compliance_convexOn_pos` | ✅ |
| Sensitivity `∂c/∂wₑ = −uᵀKₑu ≤ 0`; SIMP `∂c/∂xₑ = −p xₑ^{p−1} uᵀKₑu` (self-adjoint problem) | `hasDerivAt_compliance_single`, `sensitivity_nonpos`, `hasDerivAt_simpCompliance`, `simp_sensitivity_nonpos` | ✅ |
| SIMP penalizes intermediate densities: `xᵖ < x` for `0 < x < 1 < p` | `simp_penalization` | ✅ |
| The OC update respects the box `[xmin, 1]` and the move limit `m` | `OptimalityCriteria`: `ocUpdate_mem_box`, `abs_ocUpdate_sub_le` | ✅ |
| The volume is antitone and continuous in the multiplier `λ`; bisection finds `λ` with the target volume | `ocVolume_antitoneOn`, `ocVolume_continuousOn`, `exists_ocVolume_eq_of_bounds` | ✅ |
| Fixed points of the OC update are exactly the KKT points (`Bₑ = 1` on intermediate densities, `≤ 1` at `xmin`, `≥ 1` at `1`) | `ocUpdate_fixed_iff_kkt`, `neg_dc_eq_of_fixed` | ✅ |
| Density filter: convex combination (keeps the box), preserves constants, linear; cone weights give a positive normalizer | `filterDensity_mem_box`, `filterDensity_const`, `filterDensity_linear`, `coneWeight_sum_pos` | ✅ |
| Sensitivity filter of the 99-line code keeps `dĉ ≤ 0`; chain rule through the density filter | `filterSens_nonpos`, `fderiv_comp_filterDensity` | ✅ |

Not formalized: existence of optimal designs (needs relaxation/homogenization or a filter in the
continuum setting), convergence of the OC iteration, and Michell's optimality conditions.

## Building

```sh
(cd papers && lake build TopologyOptimization)
scripts/check_no_sorry_axiom.sh
```
