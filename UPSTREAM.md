# Upstream candidates for Mathlib

Lemmas and constructions general enough to contribute to Mathlib. Marked in the
source with `-- upstream candidate`.

| Declaration | File | Note |
|---|---|---|
| `Lin.instContinuousFunctionalCalculus` | `Tensor/Positive.lean` | real CFC on finite-dim `E →L[ℝ] E` via `ContinuousFunctionalCalculus.transfer` |
| `Lin.instStarOrderedRing` | `Tensor/Positive.lean` | follows from the above via `instStarOrderedRingRCLike` |
| `Lin.mul_eq_one_comm` | `Tensor/Orthogonal.lean` | one-sided inverses in finite-dim `E →L[𝕜] E` |
| `Lin.det_transpose` | `Tensor/Second.lean` | `det (adjoint A) = conj (det A)` |
| `Lin.dcontr`, `Frob` | `Tensor/Contraction.lean` | Hilbert–Schmidt inner product on operators |
| `Matrix.charpoly_fin_three` | `Tensor/Invariants.lean` | explicit `3 × 3` characteristic polynomial |

| `Lin.polarRotation` & co. | `Tensor/Polar.lean` | polar decomposition in finite-dim real inner product spaces |

Still planned: Jacobi's formula for `det`, H¹/H² on an
interval, Wirtinger's inequality.
