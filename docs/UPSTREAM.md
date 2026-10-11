# Upstream candidates for Mathlib

Lemmas and constructions general enough to contribute to Mathlib. Marked in the
source with `-- upstream candidate`.

| Declaration | File | Note |
|---|---|---|
| `Lin.instContinuousFunctionalCalculus` | `ContinuumMechanics/Tensor/Positive.lean` | real CFC on finite-dim `E →L[ℝ] E` via `ContinuousFunctionalCalculus.transfer` |
| `Lin.instStarOrderedRing` | `ContinuumMechanics/Tensor/Positive.lean` | follows from the above via `instStarOrderedRingRCLike` |
| `Lin.mul_eq_one_comm` | `ContinuumMechanics/Tensor/Orthogonal.lean` | one-sided inverses in finite-dim `E →L[𝕜] E` |
| `Lin.det_transpose` | `ContinuumMechanics/Tensor/Second.lean` | `det (adjoint A) = conj (det A)` |
| `Lin.dcontr`, `Frob` | `ContinuumMechanics/Tensor/Contraction.lean` | Hilbert–Schmidt inner product on operators |
| `Matrix.charpoly_fin_three` | `ContinuumMechanics/Tensor/Invariants.lean` | explicit `3 × 3` characteristic polynomial |

| `Lin.polarRotation` & co. | `ContinuumMechanics/Tensor/Polar.lean` | polar decomposition in finite-dim real inner product spaces |
| `Lin.contDiff_det`, `Lin.hasFDerivAt_det` | `ContinuumMechanics/Tensor/DetDeriv.lean` | smoothness of `det` and Jacobi's formula on `E →L[ℝ] E` |
| `Lin4.IsIsotropic.exists_lame` | `ContinuumMechanics/Tensor/Isotropic4.lean` | isotropic 4th-order tensors (reflection proof, any dim ≥ 2) |
| `index_matrix`, `index_matrix_conjTranspose` | `DiscreteMechanics/Truss.lean`, `Periodic.lean` | `dim ker A − dim ker Aᵀ = #cols − #rows` |
| `Korn.korn_identity` | `ContinuumMechanics/Elastostatics/Korn.lean` | `∫|∇u|² + ∫(div u)² = 2∫|ε(u)|²` for compactly supported fields |
| `tendsto_smul_solution` | `DiscreteMechanics/LongWave.lean` | limits of solutions of linear systems through an adjugate |

Still planned: `H²` on an interval, `H¹₀(Ω; ℝⁿ)`.
