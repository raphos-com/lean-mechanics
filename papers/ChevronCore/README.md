# Chevron folded cores: a Lean formalization

Machine-checked formalization (Lean 4 + Mathlib, no axioms, no `sorry`) of the analytical results of

> A. Lebée, K. Sab, **Transverse shear stiffness of a chevron folded core used in sandwich
> construction**, Int. J. Solids Struct. 47, 2620–2629 (2010).

Notation: member angle `δ`, closure angle `φ`, wall Poisson ratio `ν`, normalized moduli
`𝓔_α = G_α3 / (ρ G_s)`, `S = sin²δ cos²δ`.

✅ proved as stated; ➕ proved, beyond what the paper states.

| Paper | Lean (`ChevronCore/Bounds.lean`) | Status |
|---|---|---|
| (14)–(15), §3.1: normalization of `G₁₃⁻` gives `𝓔₁⁻ = 2(1 + ν) S` | `normalize_lower` | ✅ |
| §3.3: `𝓔₁⁻` is maximal for `δ = π/4`, as for Warren truss beams | `lowerE1_le`, `lowerE1_quarter` | ✅ |
| (21): `𝓔₁⁻ ≤ 𝓔₁⁺`, proved from the closed forms, with the identity `(1 - ν)(𝓔₁⁺ - 𝓔₁⁻) = (1 - 4S)(1 - ν)cos²φ + 2S(sin²φ - 1 + ν)²` | `lowerE1_le_upperE1` | ➕ |
| §3.3: for `δ = π/4`, `cos²φ = ν` the bounds coincide, `𝓔₁ = (1 + ν)/2` (exact solution) | `exact_quarter` | ✅ |
| §3.3: for the prismatic pattern `φ = π/2`, `𝓔₂⁺ = sin²δ` | `upperE2_prismatic` | ✅ |
| (23): `𝓔₁⁺ + 𝓔₂⁺ = R⁺ = (2x/(1 - ν) + 1)(1 - x)`, `x = cos²δ sin²φ` | `upper_sum` | ✅ |
| (24)–(25): `max R⁺ = (3 - ν)²/(8(1 - ν))` at `x = (1 + ν)/4`, attained by actual geometries | `Rplus_le`, `Rplus_max`, `exists_max_geometry` | ✅ |
| (22), §4.3: honeycomb upper bounds always sum to `1` | `honeycomb_sum` | ✅ |
| §4.3: chevron cores can outperform honeycombs (by `(1 + ν)²/(8(1 - ν))`; ≈ 40% for `ν = 0.4`) | `chevron_beats_honeycomb`, `forty_percent` | ✅ |
| §3.1: lower bound `𝓔₂⁻` in direction 2 | — | not formalized (formula garbled in the available PDF text) |
| §4: finite-element bounds | — | numerical, out of scope |

The upper bounds `𝓔₁⁺`, `𝓔₂⁺` are read from the PDF text; the reading is confirmed by
`upper_sum` (they add up to the paper's eq. 23) and `exact_quarter` (they reproduce the exact
value stated in §3.3).

## Building

```sh
(cd papers && lake build ChevronCore)
scripts/check_no_sorry_axiom.sh
```
