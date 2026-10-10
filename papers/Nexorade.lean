import Nexorade.OutOfPlane
import Nexorade.InPlane
import Nexorade.Parametric
import Nexorade.Plate
import Nexorade.Homogenized
import Nexorade.Optimum

/-!
# Nexorade

Formalization of L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of
reciprocal systems using homogenization techniques* (2013): homogenization of the square
nexorade as a (degenerate) Kirchhoff–Love plate. Built on the `ContinuumMechanics` library.

| Paper | File |
|---|---|
| §3, static homogenization (plate energy = minimum cell complementary energy) | `Homogenized` |
| App. 8, out-of-plane cell problem, degeneracy, (8.8), (8.10) | `OutOfPlane` |
| App. 8, in-plane cell problem, `A₂₂₁₁ = 0` | `InPlane` |
| §§4–5, parametric study, (5.3), (5.5), (5.6), optimum `φ = π/8` | `Parametric` |
| §5, degenerate plate, Navier solution (5.7)–(5.8) | `Plate` |
| §§3–4 (final version), formulas in `a/l`, (31)–(33), stiffness optima, trade-off | `Optimum` |

Uses from `ContinuumMechanics`: the Kirchhoff–Love plate (`Plates.KirchhoffLove`; the
equivalent plate is the case `ν = 1`) and its Navier solutions (`Plates.Navier`). The
frame-to-plate convergence of homogenization is a modelling assumption (`GAPS.md`).
-/
