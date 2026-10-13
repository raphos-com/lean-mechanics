# Roadmap

The repository contains three libraries built on Mathlib (Lean `v4.34.1`):

* **`ClassicalMechanics`**: systems of particles and their conservation laws, the Kepler
  problem, rigid bodies, oscillators and Lagrangian mechanics;
* **`ContinuumMechanics`**: tensor algebra, kinematics, stress, constitutive theory, linear
  elastostatics, beams and plates;
* **`DiscreteMechanics`**: pin-jointed and periodic frames, Maxwell–Calladine counting, Bloch
  analysis and long-wave limits.

Formalizations of papers are a separate Lake project in [`papers/`](../papers), each with its own
README; they are not tracked here.

Each milestone ends with: definitions → API lemmas → main theorems → `example` blocks → commit, a
[`CHANGELOG.md`](CHANGELOG.md) entry and updates to [`GAPS.md`](GAPS.md), [`TODO.md`](TODO.md),
[`UPSTREAM.md`](UPSTREAM.md).

Status: ✅ done; 🟡 partly done (what is open is stated); ⬜ planned.

---

## ContinuumMechanics

### Tensor algebra (`Tensor/`)

| File | Content | Status |
|---|---|---|
| `Second.lean` | `Lin E`, transpose, trace, determinant, dyads | ✅ |
| `SymSkew.lean` | `Sym E ⊕ Skw E` | ✅ |
| `Contraction.lean` | `A ⊡ B = tr(AᵀB)`, Frobenius inner product (`Frob E`) | ✅ |
| `Spherical.lean` | spherical/deviatoric decomposition | ✅ |
| `Invariants.lean` | principal invariants, Cayley–Hamilton (d = 3) | ✅ |
| `Spectral.lean` | spectral decomposition of symmetric tensors | ✅ |
| `Orthogonal.lean` | orthogonal tensors, rotations | ✅ |
| `Positive.lean` | real continuous functional calculus on `Lin E`, square roots | ✅ |
| `Polar.lean` | polar decomposition `F = RU = VR` | ✅ |
| `DetDeriv.lean` | Jacobi's formula | ✅ |
| `Fourth.lean` | fourth-order tensors, symmetries | ✅ |
| `Isotropic4.lean` | isotropic fourth-order tensors `λ I⊗I + 2μ 𝕀ˢʸᵐ` | ✅ |
| `Matrix.lean` | `Fin 3` matrix bridge | ✅ |

### Kinematics (`Kinematics/`)

| File | Content | Status |
|---|---|---|
| `Body.lean`, `Strain.lean` | deformations, `F`, `J`, `C`, `B`, Green–Lagrange, Almansi | ✅ |
| `Infinitesimal.lean` | `ε = sym ∇u`, linearisation estimate | ✅ |
| `Rigid.lean` | skew gradient ⇒ infinitesimal rigid displacement | ✅ |
| `Observer.lean` | change of observer, objectivity | ✅ |
| `Compatibility.lean`, `SaintVenant.lean`, `PoincareStar.lean`, `SaintVenantStar.lean` | Saint-Venant compatibility: necessity; sufficiency on open convex and **star-shaped** domains (Poincaré lemma for star-shaped sets) | 🟡 general simply connected domains open |

### Stress and balance laws (`Stress/`)

| File | Content | Status |
|---|---|---|
| `Cauchy.lean`, `Triangle.lean` | Cauchy's theorem by the tetrahedron argument | ✅ |
| `Balance.lean`, `BoxRegion.lean`, `Regions.lean` | local balance laws, symmetry of `σ`; divergence theorem as a hypothesis, witnessed on boxes | ✅ |
| `Piola.lean` | Piola–Kirchhoff stresses | ✅ |
| `Criteria.lean` | invariants, von Mises, Tresca | ✅ |

### Constitutive theory (`Constitutive/`)

| File | Content | Status |
|---|---|---|
| `Hyperelastic/Linearization.lean` | frame indifference and isotropy of SVK, neo-Hookean and Mooney–Rivlin; Fréchet derivative of the stress at `I` is the isotropic elasticity tensor; second-order energy expansion; uniaxial tension `σ = μ(λ² - 1/λ)` | ✅ |
| `Viscoelastic.lean` | 1D viscoelasticity: Kelvin–Voigt creep, Maxwell relaxation and creep, Zener solid (existence, uniqueness, limits), energy dissipation, complex modulus and loss per cycle `π η ω ε₀²` | ✅ |
| `Hyperelastic.lean` | hyperelasticity, frame indifference | ✅ |
| `Hyperelastic/SVK.lean`, `NeoHookean.lean`, `MooneyRivlin.lean` | classical hyperelastic materials | ✅ |
| `LinearIsotropic.lean` | Lamé/Young/bulk conversions, positivity | ✅ |
| `Ellipticity.lean` | acoustic tensor, strong ellipticity `μ > 0 ∧ λ + 2μ > 0`, longitudinal and transverse plane waves | ✅ |
| `RivlinEricksen.lean` | representation of isotropic tensor functions | ✅ |

### Linear elastostatics (`Elastostatics/`)

| File | Content | Status |
|---|---|---|
| `Basic.lean` | work, Clapeyron, Betti, Kirchhoff uniqueness | ✅ |
| `MinimumEnergy.lean` | minimum potential energy | ✅ |
| `Weak.lean` | Lax–Milgram well-posedness | 🟡 under the `KornSetting` hypothesis (`GAPS.md`) |
| `Korn.lean` | Korn's first inequality for compactly supported `C²` fields | ✅ |
| `Variational.lean` | integration by parts for compactly supported fields, fundamental lemma of the calculus of variations on open sets | ✅ |
| `NavierLame.lean` | isotropic strain energy, Navier–Lamé equations ⇔ stationary energy | ✅ |
| `PlaneWave.lean` | residual of plane waves; travelling waves solve the equations of motion under the propagation condition | ✅ |

### Fluids (`Fluids/`)

| File | Content | Status |
|---|---|---|
| `Ideal.lean` | material derivative and chain rule, incompressible Euler equations, Lamb identity, **Bernoulli's theorem** (streamlines; everywhere for irrotational flow), potential flow with the unsteady Bernoulli pressure, **Kelvin's circulation theorem** | ✅ |

### Beams and 1D Sobolev spaces (`Beams/`, `Sobolev1D/`)

| File | Content | Status |
|---|---|---|
| `Interval.lean`, `Poly.lean` | calculus on an interval, polynomial deflections | ✅ |
| `Bar.lean` | axial bar | ✅ |
| `EulerBernoulli/` | equation, boundary conditions, uniqueness, energy, closed-form solutions | ✅ |
| `Timoshenko/` | equations, uniqueness, Euler–Bernoulli limit | ✅ |
| `Buckling.lean`, `Wirtinger.lean`, `Rayleigh.lean` | Euler buckling, Wirtinger's inequality, Rayleigh quotient | ✅ |
| `Sobolev1D/` | `L²` primitives, weak bar, weak Euler–Bernoulli beams (cantilever, clamped–clamped, propped cantilever), weak Timoshenko cantilever: well-posedness and classical ⇒ weak | ✅ |

### Plates (`Plates/`)

| File | Content | Status |
|---|---|---|
| `KirchhoffLove.lean` | plate equation, moments, simply supported edges | ✅ |
| `Energy.lean` | Kirchhoff–Love bending energy; null Lagrangian `∫∇²w:∇²v = ∫ΔwΔv`; strong ⇔ stationary on open sets; minimum potential energy for clamped plates | ✅ |
| `Navier.lean` | single-mode Navier solutions | ✅ |
| `Grillage.lean` | orthotropic plates, Navier solution; square beam grillage as an orthotropic plate, isotropic iff `GJ = EI` | ✅ |
| `MindlinReissner.lean` | equations, Navier solution, Kirchhoff limit | ✅ |
| `MindlinEnergy.lean` | Mindlin–Reissner energy form, integration by parts, strong ⇔ stationary, nonnegativity | ✅ |

### Planned

| Item | Content | Status |
|---|---|---|
| `Airy.lean` | plane elasticity: Airy stresses satisfy equilibrium, compatibility ⇔ biharmonic (plane stress and strain), uniaxial tension, pure bending, end-loaded cantilever, simply supported beam under uniform load | ✅ |
| `LameCylinder.lean` | **Lamé's problem**: radial equilibrium ⇔ Euler ODE, general solution `Ar + B/r` (with uniqueness), pressurized thick cylinder (stresses, BCs, constant axial stress), maximum hoop stress at the bore, thin-wall (Barlow) limit, thick spherical shell | ✅ |
| `Castigliano.lean` | Castigliano's first and second theorems, Clapeyron, Maxwell–Betti, unit-load method; determinate trusses `δ = Σ N n L/(EA)`; cantilever `U* = P²L³/(6EI)`, tip deflection `PL³/(3EI)` | ✅ |
| `Existence.lean` | **Poincaré inequality** on bounded domains (via integration by parts), coercivity of the Lamé energy on `H¹₀`, **existence and uniqueness of weak solutions** of clamped isotropic elastostatics (Lax–Milgram), minimum potential energy | ✅ |
| `Torsion.lean` | Saint-Venant torsion: warping displacement, strains, Navier–Lamé ⇔ harmonic warping, Prandtl stress function `ΔΦ = -2μα`; circular shaft `T = μJα`, elliptic bar `T = μαπa³b³/(a² + b²)` | ✅ |
| `H10.lean` | `H¹₀(Ω; ℝⁿ)` as the closure of smooth compactly supported fields in `L² × L²`; **Korn's identity and inequality by density**, coercivity of the isotropic energy | ✅ |
| Saint-Venant on simply connected domains | needs Mathlib's Poincaré lemma beyond convex sets | ⬜ |

## DiscreteMechanics

| File | Content | Status |
|---|---|---|
| `Truss.lean` | pin-jointed frames, compatibility/equilibrium matrices, virtual work, Maxwell–Calladine index theorem, rigid motions | ✅ |
| `Stiffness.lean` | direct stiffness method: `K = Cᵀ diag(k) C` symmetric, positive semidefinite, `ker K = ker C`, assembly from element matrices, supports ⇒ positive definite reduced stiffness, unique displacements, minimum potential energy, Maxwell–Betti, two-bar example | ✅ |
| `Periodic.lean` | periodic frames, Bloch compatibility matrix, Bloch reduction, Maxwell–Calladine per wave vector, Maxwell lattices | ✅ |
| `LongWave.lean` | long-wave expansion of the discrete Laplacian; long-wave limit of Bloch solutions through an adjugate | ✅ |
| `Winding.lean` | winding numbers of polynomial Bloch determinants; argument principle (roots in the unit disk), additivity | ✅ |
| periodic beam frames | beam frames with rigid or pinned joints, their Bloch problem, convergence to an equivalent plate | ⬜ |

## ClassicalMechanics

| File | Content | Status |
|---|---|---|
| `Vector.lean` | product rules for dot and cross products of trajectories in `ℝ³` | ✅ |
| `Particles.lean` | systems of particles: momentum, centre of mass, angular momentum (central forces), kinetic energy theorem, energy conservation | ✅ |
| `Galilean.lean` | Galilean boosts, rotations and time shifts of particle systems; transformation of `P` and `T`; conserved boost charge `M x_G - t P`, uniform motion of the centre of mass | ✅ |
| `Virial.lean` | virial `G = Σ mᵢ xᵢ·vᵢ`, `Ġ = 2T + Σ xᵢ·Fᵢ`; **virial theorem** for bounded motions, homogeneous potentials `⟨2T⟩ = k⟨U⟩` | ✅ |
| `TwoBody.lean` | reduction of the two-body problem: `μ r̈ = F` with the reduced mass, `T = ½M|v_G|² + ½μ|ṙ|²` | ✅ |
| `Rocket.lean` | variable mass: the rocket equation, **Tsiolkovsky** `Δv = u log(m₀/m)`, with gravity, constant burn rate | ✅ |
| `Collisions.lean` | 1D collisions with restitution (explicit final velocities, kinetic energy loss `½μ(1 - e²)(u₁ - u₂)²`), elastic collisions: relative speed preserved, equal masses scatter at right angles | ✅ |
| `Kepler.lean` | Kepler problem: conservation of `L`, `E` and the Laplace–Runge–Lenz vector, Kepler's first and second laws, eccentricity–energy relation | ✅ |
| `KeplerThird.lean` | semi-axes from `E` and `L`, `a = -k/(2E)`, `b² = a p`, peri/apoapsis bounds; **Kepler's third law** `T² = 4π² m a³ / k` (given that one period sweeps the area `π a b`) | ✅ |
| `KeplerPeriod.lean` | eccentric anomaly and **Kepler's equation**; the motion is periodic with least period `2π/n`, `n = √(k/(m a³))`; **Kepler's third law** `T² = 4π² m a³ / k` for the actual period (no swept-area hypothesis) | ✅ |
| `EffectivePotential.lean` | general central potentials: energy and angular momentum, `E = ½mṙ² + U_eff(r)`, allowed region `U_eff(r) ≤ E`, turning points | ✅ |
| `Rutherford.lean` | hyperbolic orbits (`e > 1` iff `E > 0`), the orbit stays in a cone about the LRL vector, deflection angle `tan(Θ/2) = |k|/(2Eb)`, **Rutherford cross section** `(k/4E)²/sin⁴(Θ/2)` | ✅ |
| `Constraints.lean` | d'Alembert's principle ⇔ Lagrange multiplier, ideal constraints do no work, energy conservation; spherical pendulum (vertical angular momentum, energy, tension), simple pendulum | ✅ |
| `RigidBody.lean` | inertia tensor (symmetric, positive semidefinite), Steiner, König, Euler's equations and their invariants | ✅ |
| `Oscillator.lean` | harmonic oscillator (solution, uniqueness, periodicity), damped oscillator (dissipation, underdamped solution) | ✅ |
| `Lagrangian.lean` | Lagrangian mechanics with one degree of freedom: Beltrami energy, cyclic coordinates, Hamilton's principle ⇔ Euler–Lagrange, natural systems | ✅ |
| `EulerStability.lean` | stability of steady rotations: linearized Euler equations, `λ < 0` iff largest/smallest axis, explicit exponentially growing solution about the intermediate axis; nonlinear stability bounds from the conserved `|L|² - 2I₁T` | ✅ |
| `HeavyTop.lean` | Lagrange's heavy symmetric top (Euler–Poisson equations): energy, vertical angular momentum, spin; reduction to `I₁²u̇² = I₁(2E' - 2Mgℓu)(1 - u²) - (b - au)²`; sleeping top under `(I₃ω₃)² > 4I₁Mgℓ` | ✅ |
| `Rotation.lean` | rigid-body kinematics: `Ω = ṘRᵀ`, `W = RᵀṘ` skew, `Ω = RWRᵀ`, axial vector, Poisson's formula, rigid velocity field, isometry | ✅ |
| `RotatingFrame.lean` | motion relative to a rotating frame: `ẍ = R(a + 2w×v + w×(w×y) + ẇ×y)`; Coriolis, centrifugal and Euler forces | ✅ |
| `Hamiltonian.lean` | Hamilton's equations, Poisson brackets, evolution `Ḟ = {F, H}`, energy conservation, Liouville (divergence-free Hamiltonian field), natural systems, Legendre transform (Euler–Lagrange solutions are Hamiltonian flows) | ✅ |
| `Jacobi.lean` | Poisson bracket of `C²` functions: antisymmetry, **Jacobi identity** | ✅ |
| `LinearHamiltonian.lean` | linear Hamiltonian systems `ż = -J S z`: Hamiltonian matrices, the flow is symplectic and `det Φ(t) = 1` (Liouville) | ✅ |
| `HamiltonJacobi.lean` | **Jacobi's theorem** (1 DOF, time-dependent, mixed partials as hypotheses); harmonic oscillator in action–angle variables: `H = ωI`, Jacobian `1`, flow, action = phase-space area / 2π | ✅ |
| `Canonical.lean` | linear canonical transformations: Poisson brackets and Hamiltonian flows are preserved by symplectic matrices, symplectic group, linear Hamiltonian flows are canonical | ✅ |
| `LiouvilleFlow.lean` | for a `C²` flow of a vector field: variational equation, **Liouville formula** `∂ₜ det DΦ = (div X) det DΦ`, `det DΦ = 1` and **volume preservation** for divergence-free fields, applied to Hamiltonian flows (flow taken as data: Mathlib has no smooth dependence on initial conditions) | ✅ |
| `Noether.lean` | Lagrangians on `ℝⁿ`: energy conservation, Noether's theorem, translation and linear (rotation) symmetries | ✅ |
| `Routh.lean` | cyclic coordinates: conserved momenta; **Routh reduction** (two coordinates, local inversion), the Routhian obeys Euler–Lagrange; planar central motion reduces to `m r̈ = -V_eff'(r)` | ✅ |
| `SmallOscillations.lean` | `M q̈ + K q = 0`: energy, normal modes, superposition, Rayleigh quotient, stability, modal orthogonality | ✅ |
| `Stability.lean` | natural systems `M q̈ = -∇U`: equilibria, energy, **Lagrange–Dirichlet theorem** (strict minimum ⇒ Lyapunov stable in phase space), linearization, positive definite Hessian ⇒ strict minimum ⇒ stable | ✅ |
| `NormalModes.lean` | complete set of `M`-orthonormal normal modes for positive definite `M` and positive semidefinite `K` (simultaneous diagonalization) | ✅ |

## Review decisions

1. **Real CFC instance**: defined library-wide as a global instance
   `ContinuousFunctionalCalculus ℝ (Lin E) IsSelfAdjoint` for finite-dimensional `E`; to be
   replaced if Mathlib gains its own.
2. **Beam ends**: smooth-setting theorems take `w : ℝ → ℝ` defined on all of `ℝ` (only values on
   `[0, L]` matter). Point loads use smooth pieces glued with `w, w', w''` continuous and a shear
   jump of `P`.
3. **Cauchy's theorem** is proved (not assumed), integrating over the flat faces of a
   tetrahedron.
4. **Papers** are a separate Lake project depending on both libraries, so that the libraries do
   not depend on, or cite, any particular paper.
