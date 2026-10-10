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
| `Lin.contDiff_det`, `Lin.hasFDerivAt_det` | `Tensor/DetDeriv.lean` | smoothness of `det` and Jacobi's formula on `E →L[ℝ] E` |
| `Lin4.IsIsotropic.exists_lame` | `Tensor/Isotropic4.lean` | isotropic 4th-order tensors (reflection proof, any dim ≥ 2) |

Still planned: H¹/H² on an
interval, Wirtinger's inequality.
