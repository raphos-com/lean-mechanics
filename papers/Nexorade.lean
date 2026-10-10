import Nexorade.OutOfPlane
import Nexorade.InPlane
import Nexorade.Parametric
import Nexorade.Plate
import Nexorade.Homogenized
import Nexorade.Optimum
import Nexorade.Frame

/-!
# Nexorade

Formalization of L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of
reciprocal systems using homogenization techniques* (2013): homogenization of the square
nexorade as a (degenerate) Kirchhoff–Love plate. Built on the `ContinuumMechanics` library.

| Paper | File |
|---|---|
| §2.2, static homogenization (plate energy = minimum cell complementary energy) | `Homogenized` |
| §3.2, out-of-plane cell problem, (20), localization (22)–(23), compliance (28) | `OutOfPlane` |
| §2.2 applied to membrane forces (left to future work in the paper), `A₂₂₁₁ = 0` | `InPlane` |
| §3.1 and §4, `(L, φ)` parametrization (19), (22), (23), (29), optimum `φ = π/8` | `Parametric` |
| (24)–(27), degenerate plate; §5.1, Navier solution (34)–(36) | `Plate` |
| §§3–4, formulas in `a/l`, (29)–(33), stiffness optima, trade-off | `Optimum` |
| scale separation: the frame converges to the plate (single-mode loads) | `Frame` |

Uses from `ContinuumMechanics`: the Kirchhoff–Love plate (`Plates.KirchhoffLove`; the
equivalent plate is the case `ν = 1`) and its Navier solutions (`Plates.Navier`). The
frame-to-plate convergence is proved for the nexorade under single-mode loads (`Frame`); the
general statement is a modelling assumption (`GAPS.md`).
-/
