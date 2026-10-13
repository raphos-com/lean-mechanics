# lean-mechanics

[![CI](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23352091.svg)](https://doi.org/10.5281/zenodo.23352091)

Classical, continuum and discrete mechanics formalized in [Lean 4](https://lean-lang.org) on top
of [Mathlib](https://github.com/leanprover-community/mathlib4). Every theorem is checked by Lean:
no axioms beyond Lean's three standard ones, and `main` is `sorry`-free (both enforced in CI).

* **`ClassicalMechanics`**: systems of particles, the Kepler problem and scattering, rigid bodies
  and tops, rotating frames, oscillators, Lagrangian and Hamiltonian mechanics, stability.
* **`ContinuumMechanics`**: tensor algebra, kinematics, stress, constitutive theory
  (hyperelastic, viscoelastic), linear elastostatics, beams, plates, torsion, ideal fluids.
* **`DiscreteMechanics`**: pin-jointed and periodic frames, the stiffness method,
  Maxwell–Calladine counting, Bloch analysis and long-wave limits.

## Highlights

Each link goes to the statement in the API documentation.

**Classical mechanics**

* [Noether's theorem](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Noether.html#ClassicalMechanics.LagrangianN.noether):
  every symmetry of a Lagrangian on `ℝⁿ` gives a conserved quantity.
* [Kepler's third law](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/KeplerPeriod.html#ClassicalMechanics.KeplerMotion.kepler_third_period)
  `T² = 4π² m a³ / k` for the actual period of a bound orbit, via Kepler's equation; the orbit is a
  [conic](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Kepler.html#ClassicalMechanics.KeplerMotion.orbit_equation)
  (Laplace–Runge–Lenz vector).
* [Rutherford's cross section](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Rutherford.html#ClassicalMechanics.Rutherford.rutherford_cross_section)
  `(k / 4E)² / sin⁴(Θ/2)`.
* [The Jacobi identity](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Jacobi.html#ClassicalMechanics.jacobi)
  for Poisson brackets and
  [Liouville's theorem](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/LiouvilleFlow.html#ClassicalMechanics.PhaseFlow.measure_image):
  divergence-free flows preserve volume.
* [The Lagrange–Dirichlet theorem](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Stability.html#ClassicalMechanics.NaturalSystem.lagrange_dirichlet):
  a strict minimum of the potential is a stable equilibrium.
* [The tennis-racket theorem](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/EulerStability.html#ClassicalMechanics.rate_pos_iff):
  rotation about the intermediate principal axis is unstable.
* [The virial theorem](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Virial.html#ClassicalMechanics.ParticleSystem.virial).

**Continuum mechanics**

* [Korn's inequality in `H¹₀`](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/H10.html#ContinuumMechanics.Sobolev.korn_first)
  and [existence and uniqueness](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/Existence.html#ContinuumMechanics.Sobolev.existsUnique_clamped)
  of weak solutions of clamped linear elastostatics (Poincaré inequality, Lax–Milgram).
* [Navier–Lamé equations ⇔ stationary energy](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/NavierLame.html#ContinuumMechanics.NavierLame.isStationary_iff).
* [Saint-Venant compatibility](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Kinematics/SaintVenantStar.html#ContinuumMechanics.saintVenant_sufficient_of_starConvex)
  on star-shaped domains.
* [Torsion of an elliptic bar](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/Torsion.html#ContinuumMechanics.Torsion.torque_ellip)
  `T = μαπ a³b³ / (a² + b²)`.
* [Castigliano's second theorem](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/Castigliano.html#ContinuumMechanics.Castigliano.castigliano_second).
* [Kelvin's circulation theorem](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fluids/Ideal.html#ContinuumMechanics.Fluids.circulation_const)
  for ideal fluids.

**Discrete mechanics**

* [The Maxwell–Calladine index theorem](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Truss.html#DiscreteMechanics.Truss.maxwell_calladine)
  for pin-jointed frames.
* [The stiffness method](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Stiffness.html#DiscreteMechanics.existsUnique_displacement):
  a supported truss without mechanisms has unique displacements under any load.
* [Winding numbers of Bloch polynomials](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Winding.html#DiscreteMechanics.winding_eq_card_roots)
  count roots in the unit disk (topological polarization of Maxwell lattices).

## Papers

[`papers/`](papers) contains formalizations of research papers built on these libraries:

* [`BendingGradient`](papers/BendingGradient): Lebée–Sab, *A Bending-Gradient model for thick
  plates*.
* [`ChevronCore`](papers/ChevronCore): Lebée–Sab, *Transverse shear stiffness of a chevron folded
  core used in sandwich construction*.
* [`Gridshells`](papers/Gridshells): Baek, Sageman-Furnas, Jawed, Reis, *Form finding in elastic
  gridshells*.
* [`KaneLubensky`](papers/KaneLubensky): Kane–Lubensky, *Topological boundary modes in isostatic
  lattices*.
* [`Miura`](papers/Miura): Schenk–Guest and Wei et al. on the Miura-ori.
* [`Nexorade`](papers/Nexorade): Greco–Lebée–Douthe, *Investigation of the elastic behavior of
  reciprocal systems using homogenization techniques*.

## Documentation

* API documentation: <https://raphos-com.github.io/lean-mechanics/> (generated on every push to
  `main`)
* Design: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
* Plan and status: [`docs/ROADMAP.md`](docs/ROADMAP.md)
* Assumptions not yet provable from Mathlib: [`docs/GAPS.md`](docs/GAPS.md)
* Changes: [`docs/CHANGELOG.md`](docs/CHANGELOG.md)

## Building

```sh
lake exe cache get              # download prebuilt Mathlib
lake build                      # ClassicalMechanics, ContinuumMechanics, DiscreteMechanics
(cd papers && lake build)       # paper formalizations
scripts/check_no_sorry_axiom.sh
```

## Using it as a dependency

Add to your `lakefile.toml` (the Lake package is named `ContinuumMechanics` and provides all three
libraries):

```toml
[[require]]
name = "ContinuumMechanics"
git = "https://github.com/raphos-com/lean-mechanics.git"
rev = "main"
```

then `import ClassicalMechanics`, `import ContinuumMechanics` or `import DiscreteMechanics`. Use the
same Lean toolchain as [`lean-toolchain`](lean-toolchain).

## How this was written

This library was developed with substantial help from AI assistance (Anthropic's Claude), under the
direction of the author. That is a statement about how the proofs were found, not about whether
they are right: every result is checked by Lean's kernel, CI rebuilds everything from scratch on
each push, and a guard script rejects `sorry` and any axiom beyond Lean's standard ones. Statements
(definitions and hypotheses) are where human review matters most; issues and corrections are
welcome.

## Citing

Archived on Zenodo: [doi:10.5281/zenodo.23352091](https://doi.org/10.5281/zenodo.23352091). See
[`CITATION.cff`](CITATION.cff) (GitHub shows a "Cite this repository" button).

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
