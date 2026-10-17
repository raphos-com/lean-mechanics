# lean-mechanics

[![CI](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/raphos-com/lean-mechanics/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23352090.svg)](https://doi.org/10.5281/zenodo.23352090)

Classical, continuum and discrete mechanics formalized in [Lean 4](https://lean-lang.org) on top
of [Mathlib](https://github.com/leanprover-community/mathlib4). Every theorem is checked by Lean:
no axioms beyond Lean's three standard ones, and `main` is `sorry`-free (both enforced in CI).

* **`ClassicalMechanics`**: particles and conservation laws, Kepler orbits, orbital mechanics and
  scattering, rigid bodies and tops, rotating frames, oscillators and structural dynamics,
  Lagrangian and Hamiltonian mechanics, stability, special relativity.
* **`ContinuumMechanics`**: tensor algebra, kinematics, stress, constitutive theory (elastic,
  hyperelastic, viscoelastic, plastic), elastostatics, beams, plates, fatigue and fracture,
  contact, geotechnics, heat conduction and thermoelasticity, fluid mechanics.
* **`DiscreteMechanics`**: pin-jointed and periodic frames, the stiffness method,
  Maxwell–Calladine counting, Bloch analysis, lattice dynamics.

## Coverage by area

| Area | Modules |
|---|---|
| **Structural dynamics** | `SmallOscillations`, `NormalModes`, `ModalDamping` (classical and Rayleigh damping, modal superposition), `ForcedOscillator` (resonance), `Duhamel` (impulse response, response spectra), `Beams/String`, `Beams/Vibration`, `Plates/Dynamics`, `Plates/Membrane`, `DoublePendulum`, `DiscreteMechanics/Chain` |
| **Buckling and stability** | `Beams/Buckling`, `Beams/BucklingBC` (all end conditions, imperfections, lateral–torsional), `Beams/Rayleigh`, `Plates/Dynamics` (plate buckling), `Stability` (Lagrange–Dirichlet), `EulerStability` |
| **Solids** | `Tensor/`, `Kinematics/` (Saint-Venant compatibility), `Stress/` (Cauchy, Mohr's circle, yield criteria), `Constitutive/` (linear, hyperelastic, viscoelastic, plasticity), `Elastostatics/` (Navier–Lamé, Korn, existence in `H¹₀`, Castigliano, Airy, Lamé cylinder, torsion, Saint-Venant's principle) |
| **Beams and plates** | `Beams/` (Euler–Bernoulli, Timoshenko, weak forms), `Plates/` (Kirchhoff–Love, Mindlin–Reissner, grillages, circular plates) |
| **Fatigue and fracture** | `Fatigue/Basic` (Basquin, Goodman/Gerber/Soderberg, Miner, Paris), `Fracture/Basic` (Griffith, Irwin, compliance method, DCB) |
| **Contact** | `Contact/Hertz` |
| **Geotechnics** | `Geotechnics/Consolidation` (Terzaghi), `Geotechnics/Strength` (Mohr–Coulomb, Rankine, slopes, bearing capacity), `Geotechnics/Seepage` (Darcy, quick condition, Dupuit) |
| **Fluid dynamics** | `Fluids/Ideal` (Euler, Bernoulli, Kelvin), `Fluids/Viscous` (Navier–Stokes, Couette, Poiseuille), `Fluids/Unsteady` (Stokes' problems), `Fluids/Waves` (acoustics, water waves) |
| **Heat** | `Thermal/Heat`, `Thermal/Thermoelastic` |

Modules without a prefix are in `ClassicalMechanics/`; the others are in `ContinuumMechanics/`
unless marked.

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
* [Resonance](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/ForcedOscillator.html#ClassicalMechanics.Driven.amplitude_le_resonance)
  of the driven damped oscillator, and the
  [brachistochrone](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Variational.html#ClassicalMechanics.cycloid_beltrami)
  and [tautochrone](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Variational.html#ClassicalMechanics.tautochrone)
  properties of the cycloid.
* [The Foucault pendulum](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Foucault.html#ClassicalMechanics.Foucault.solves_of_pendulum)
  precesses at `Ω sin φ`.
* [Relativistic energy and momentum](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Relativistic.html#ClassicalMechanics.Relativity.energy_momentum)
  `E² = (pc)² + (mc²)²` and [velocity addition](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Relativistic.html#ClassicalMechanics.Relativity.abs_velAdd_lt).
* [Poincaré recurrence](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Recurrence.html#ClassicalMechanics.hamiltonian_recurrence)
  for Hamiltonian flows.
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
* [Lamé's thick-walled cylinder](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/LameCylinder.html#ContinuumMechanics.LameCylinder.lame_equilibrium)
  and [d'Alembert's solution](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Beams/String.html#ContinuumMechanics.Strings.dAlembert_solves)
  of the vibrating string.
* [Mohr's circle](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Stress/Mohr.html#ContinuumMechanics.PlaneStress.mohr_circle)
  and principal stresses.
* [Uniqueness for the heat equation](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Thermal/Heat.html#ContinuumMechanics.Heat.unique)
  and [beam vibrations](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Beams/Vibration.html#ContinuumMechanics.Beams.Vibration.unique).
* [Castigliano's second theorem](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/Castigliano.html#ContinuumMechanics.Castigliano.castigliano_second).
* [Kelvin's circulation theorem](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fluids/Ideal.html#ContinuumMechanics.Fluids.circulation_const)
  for ideal fluids and
  [Hagen–Poiseuille flow](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fluids/Viscous.html#ContinuumMechanics.Fluids.hagen_flowRate)
  `Q = πGR⁴/(8μ)`.

**Engineering**

* [Saint-Venant's principle](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Elastostatics/SaintVenantPrinciple.html#ContinuumMechanics.SaintVenant.energy_le_exp):
  the energy of a self-equilibrated end load decays like `e^(-2πx/b)` along a strip.
* [Clamped–pinned column buckling](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Beams/BucklingBC.html#ContinuumMechanics.Beams.EBBeam.clampedPinned_critical_load_bounds)
  with proved bounds `20.16 EI/L² < P_cr < 20.25 EI/L²`, and
  [lateral–torsional buckling](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Beams/BucklingBC.html#ContinuumMechanics.Beams.LTBeam.critical_moment).
* [Plate buckling](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Plates/Dynamics.html#ContinuumMechanics.Plates.Plate.critical_load)
  `N_cr = 4π²D/b²` and
  [Rayleigh damping](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/ModalDamping.html#ClassicalMechanics.DampedStructure.rayleigh_modal).
* [Duhamel's integral](https://raphos-com.github.io/lean-mechanics/ClassicalMechanics/Duhamel.html#ClassicalMechanics.SDOF.duhamel_solves)
  and response-spectrum bounds.
* [Paris-law crack-growth life](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fatigue/Basic.html#ContinuumMechanics.Fatigue.paris_cycles_eq)
  and [Griffith's criterion](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fracture/Basic.html#ContinuumMechanics.Fracture.griffith_criterion).
* [Hertz contact](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Contact/Hertz.html#ContinuumMechanics.Contact.force_balance).
* [Terzaghi consolidation](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Geotechnics/Consolidation.html#ContinuumMechanics.Geotechnics.tendsto_degreeFull),
  [Mohr–Coulomb failure](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Geotechnics/Strength.html#ContinuumMechanics.PlaneStress.exists_failure_plane_iff)
  and [Rankine earth pressure](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Geotechnics/Strength.html#ContinuumMechanics.Geotechnics.activeThrust_cohesionless).
* [Collapse loads of beams](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Constitutive/Plasticity.html#Plasticity.ss_collapse) by limit analysis.
* [The water-wave dispersion relation](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fluids/Waves.html#ContinuumMechanics.Fluids.Waves.freeSurfaceBC_travellingPotential_iff)
  `ω² = gk tanh(kh)` and
  [Stokes' first problem](https://raphos-com.github.io/lean-mechanics/ContinuumMechanics/Fluids/Unsteady.html#ContinuumMechanics.Fluids.stokesI_diffusion).

**Discrete mechanics**

* [The Maxwell–Calladine index theorem](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Truss.html#DiscreteMechanics.Truss.maxwell_calladine)
  for pin-jointed frames.
* [The stiffness method](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Stiffness.html#DiscreteMechanics.existsUnique_displacement):
  a supported truss without mechanisms has unique displacements under any load.
* [The band gap of a diatomic chain](https://raphos-com.github.io/lean-mechanics/DiscreteMechanics/Chain.html#DiscreteMechanics.Chain.band_gap).
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

Archived on Zenodo: [doi:10.5281/zenodo.23352090](https://doi.org/10.5281/zenodo.23352090). See
[`CITATION.cff`](CITATION.cff) (GitHub shows a "Cite this repository" button).

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
