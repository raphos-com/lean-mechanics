# Miura-ori: a Lean formalization

Machine-checked formalization (Lean 4 + Mathlib, no axioms, no `sorry`) of the rigid-folding
kinematics of the Miura-ori and of its in-plane Poisson's ratio:

> M. Schenk, S. D. Guest, **Geometry of Miura-folded metamaterials**, PNAS 110(9), 3276–3281 (2013).
>
> Z. Y. Wei, Z. V. Guo, L. Dudte, H. Y. Liang, L. Mahadevan, **Geometric mechanics of periodic
> pleated origami**, Phys. Rev. Lett. 110, 215501 (2013).
>
> C. Lv, D. Krishnaraju, G. Konjevod, H. Yu, H. Jiang, **Origami based mechanical metamaterials**,
> Sci. Rep. 4, 5979 (2014).

✅ proved as stated; ❌ the statement is wrong, and the Lean result proves the corrected one.

| Claim | Lean (`Miura/Kinematics.lean`) | Status |
|---|---|---|
| Unit-cell dimensions `H = a sin θ sin α`, `L = a √(1 − sin²θ sin²α)`, `S`, `V` describe a rigid folding (facets keep sides `a`, `b` and angle `α`) | `Facet.facet_isometry` | ✅ |
| In-plane Poisson's ratio `ν_SL = −cos²θ tan²α < 0` (Schenk–Guest) | `Facet.poisson_SL`, `Facet.poisson_SL_neg` | ✅ |
| A finite pattern can have a positive in-plane Poisson's ratio (Lv et al.) | `Facet.poisson_pattern_pos_iff`: for `n` cells it is positive **iff** `b cos α > 2na(1 − sin²θ sin²α)` | ✅ (sharpened to an exact criterion) |
| The pattern value tends to the unit-cell value as the pattern grows | `Facet.tendsto_poisson_pattern` | ✅ |
| Out-of-plane (bending) Poisson's ratio is the opposite of the in-plane one (Wei et al.) | — | not formalized: needs a facet-bending model |

## Building

```sh
(cd papers && lake build Miura)
scripts/check_no_sorry_axiom.sh
```
