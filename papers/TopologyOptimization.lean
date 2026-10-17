import TopologyOptimization.Compliance
import TopologyOptimization.OptimalityCriteria

/-!
# Topology optimization

Formalization of the mathematical core of density-based (SIMP) topology optimization by
compliance minimization ([BendsoeKikuchi1988], [Sigmund2000], [Sigmund2001],
[BendsoeSigmund2003]):

* `TopologyOptimization.Compliance`: the stiffness `K(w) = Σ wₑ Kₑ`, compliance `c = fᵀu`, its
  complementary-energy characterization, monotonicity, convexity and sensitivities.
* `TopologyOptimization.OptimalityCriteria`: the optimality-criteria update of the 99-line code,
  the bisection on the Lagrange multiplier, fixed points as KKT points, density and sensitivity
  filters.
-/
