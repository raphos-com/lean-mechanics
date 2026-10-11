# Kane–Lubensky: a Lean formalization

Machine-checked formalization (Lean 4 + Mathlib, no axioms, no `sorry`) of parts of

> C. L. Kane, T. C. Lubensky, **Topological boundary modes in isostatic lattices**,
> Nature Physics 10, 39–45 (2014). [arXiv:1308.0554](https://arxiv.org/abs/1308.0554)

built on the frame theory of [`DiscreteMechanics`](../../DiscreteMechanics).

✅ proved as stated.

| Claim | Lean | Status |
|---|---|---|
| Maxwell–Calladine counting `N₀ − N_ss = d·N − N_b` | `Truss.maxwell_calladine` | ✅ |
| … at every wave vector of a periodic lattice | `PeriodicTruss.maxwell_calladine_bloch` | ✅ |
| A periodic Maxwell lattice has at least `d` self-stresses at `k = 0` | `PeriodicTruss.le_finrank_selfStresses_zero` | ✅ |
| 1D Maxwell chain: one zero mode, no self-stress | `Chain.eq_smul_mode`, `Chain.compat_mode`, `Chain.selfStress_eq_zero` | ✅ |
| 1D: winding number of `C(q)` is 1 or 0 | `Chain.winding_eq_one`, `Chain.winding_eq_zero` | ✅ |
| 1D bulk–edge correspondence: the winding number decides the edge carrying the zero mode | `Chain.winding_eq_one_iff_left` | ✅ |
| Square lattice: no zero modes off the lines `kᵢ = 0`; floppy modes on them | `square_zeroModes_eq_bot`, `square_selfStresses_eq_bot`, `square_floppy_line` | ✅ |
| Kagome lattice is a Maxwell lattice with self-stresses at `k = 0` | `kagome_zeroModes_eq_selfStresses`, `kagome_selfStresses_zero` | ✅ |
| Argument principle: the winding number of a polynomial Bloch determinant around the unit circle is its number of roots in the unit disk; it is additive under products | `DiscreteMechanics.winding_eq_card_roots`, `DiscreteMechanics.winding_mul` | ✅ |
| Topological polarization `R_T` of deformed kagome lattices and the boundary-mode count `ν = ...` | — | not formalized: needs the explicit deformed-kagome Bloch matrices of the paper |

## Building

```sh
(cd papers && lake build KaneLubensky)
scripts/check_no_sorry_axiom.sh
```
