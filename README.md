# lean-mechanics

[![CI](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml)

Lean 4 libraries of mechanics built on Mathlib. No axioms; `main` is `sorry`-free.

* **`ClassicalMechanics`**: systems of particles and their conservation laws, the Kepler
  problem, rigid bodies, oscillators and Lagrangian mechanics.
* **`ContinuumMechanics`**: tensor algebra, kinematics, stress, constitutive theory, linear
  elastostatics, beams and plates.
* **`DiscreteMechanics`**: pin-jointed and periodic frames, Maxwell–Calladine counting, Bloch
  analysis and long-wave limits.

Documentation:

* API documentation: <https://raphos-com.github.io/lean-mechanics/> (generated on every push to
  `main`)
* Design: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
* Plan and status: [`docs/ROADMAP.md`](docs/ROADMAP.md)
* Assumptions not yet provable from Mathlib: [`docs/GAPS.md`](docs/GAPS.md)
* Changes: [`docs/CHANGELOG.md`](docs/CHANGELOG.md)

## Papers

[`papers/`](papers) contains formalisations of papers based on these libraries.

## Building

```sh
lake exe cache get              # download prebuilt Mathlib
lake build                      # ClassicalMechanics, ContinuumMechanics, DiscreteMechanics
(cd papers && lake build)       # paper formalizations
scripts/check_no_sorry_axiom.sh
```
