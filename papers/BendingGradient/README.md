# Bending-Gradient plates: a Lean formalization

Machine-checked results (Lean 4 + Mathlib, no axioms, no `sorry`) from

> A. Lebée, K. Sab, **A Bending-Gradient model for thick plates. Part I: Theory**,
> Int. J. Solids Struct. 48(20), 2878–2888 (2011).

Third-order tensors `R_αβγ` (symmetric in `αβ`) are vectors indexed by `Fin 2 × Fin 2 × Fin 2`; the
map `Q ↦ i · Q` is the matrix `embed`, and `i ∴ R` is `embedᵀ R`.

✅ proved as stated.

| Paper | Lean (`BendingGradient/Basic.lean`) | Status |
|---|---|---|
| (47c), §5.2.1: the shear force is `Q = i ∴ R`, i.e. `Q₁ = R₁₁₁ + R₁₂₂`, `Q₂ = R₁₂₁ + R₂₂₂` | `shear_eq`, `shear_components` | ✅ |
| §5.2.1: `R₁₁₂`, `R₂₂₁` are self-equilibrated (no shear force) | `shear_selfEquilibrated` | ✅ |
| Identity behind the factor `2/3`: `(i·)ᵀ(i·) = (3/2) I` | `embed_transpose_mul` | ✅ |
| (55)–(56), §6.1: for a homogeneous plate, `f = (6/5h) i·S·i` and the Bending-Gradient energy is Reissner's with shear factor 5/6 | `homogeneous_energy` | ✅ |
| (64)–(67), §6.2: `f_RM = (2/3) i ∴ f ∴ (2/3) i` is the orthogonal projection on Reissner–Mindlin compliances | `rmProj_orthogonal`, `rmProj_rm`, `rmProj_homogeneous` | ✅ |
| 3D localization, Reissner's shear fields (Section 4), boundary conditions (App. A.5) | — | not formalized |

## Building

```sh
lake build BendingGradient
scripts/check_no_sorry_axiom.sh
```
