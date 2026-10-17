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
| `Mohr.lean` | plane stress transformation `σ' = RᵀσR`, invariants, **Mohr's circle**, principal stresses and angles, maximum in-plane shear, 2D von Mises identity | ✅ |
| `Piola.lean` | Piola–Kirchhoff stresses | ✅ |
| `Criteria.lean` | invariants, von Mises, Tresca | ✅ |

### Constitutive theory (`Constitutive/`)

| File | Content | Status |
|---|---|---|
| `Hyperelastic/Linearization.lean` | frame indifference and isotropy of SVK, neo-Hookean and Mooney–Rivlin; Fréchet derivative of the stress at `I` is the isotropic elasticity tensor; second-order energy expansion; uniaxial tension `σ = μ(λ² - 1/λ)` | ✅ |
| `Composites.lean` | **rule of mixtures** from equal strain/stress, Reuss ≤ Voigt (with equality cases), n-phase bounds `min ≤ harmonic ≤ arithmetic ≤ max`; orthotropic ply stiffness, transformed stiffness `Q̄(θ)` with explicit entries and an invariant; **classical lamination theory**: `ABD` matrices, symmetric laminates have `B = 0`, single layer `A = hQ`, `D = h³Q/12` | ✅ |
| `Plasticity.lean` | 1D elastoplasticity with hardening: **return mapping** (consistency, tangent `EH/(E+H)`), monotonic curve; von Mises **associated flow** and plastic incompressibility; **maximum plastic dissipation**; limit analysis: plastic moment and shape factor `3/2`, collapse loads `4M_p/L` (simply supported) and `16M_p/L²` (fixed–fixed) by matching upper and lower bounds | ✅ |
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
| `Hydrostatics.lean` | hydrostatic pressure (existence and uniqueness), force and **centre of pressure** on a vertical gate, **Archimedes' principle** for a box (plus the vertical divergence identity), **box barge stability**: metacentric height, `GM > 0 ⇔ B/H > √(6s(1-s))`, wall-sided righting arm | ✅ |
| `Ideal.lean` | material derivative and chain rule, incompressible Euler equations, Lamb identity, **Bernoulli's theorem** (streamlines; everywhere for irrotational flow), potential flow with the unsteady Bernoulli pressure, **Kelvin's circulation theorem** | ✅ |
| `OpenChannel.lean` | open-channel flow: **specific energy** (strictly convex, minimum at the **critical depth** `y_c = (q²/g)^{1/3}`, `Fr = 1`), alternate depths; **hydraulic jump** (Bélanger's sequent depths, depths straddle `y_c`, energy loss `(y₂-y₁)³/(4y₁y₂) ≥ 0`); Manning/Chézy, best rectangular section, weir discharge | ✅ |
| `Unsteady.lean` | unidirectional shear flows: Navier–Stokes ⇔ diffusion equation; **Stokes' second problem** (oscillating plate: penetration depth `√(2ν/ω)`, phase lag, wall shear); **Stokes' first problem** (impulsively started plate, `erfc` solution, wall shear `-μU/√(πνt)`), self-similarity | ✅ |
| `Waves.lean` | **linear acoustics** (wave equation for the pressure, plane waves and impedance `ρ₀c`, acoustic energy conservation, `c² = γp/ρ`); **linear water waves**: dispersion relation `ω² = gk tanh(kh)` (iff), deep and shallow water limits, longer waves are faster, group velocity `c/2 < c_g < c` | ✅ |
| `Viscous.lean` | incompressible **Navier–Stokes**, divergence of the viscous stress; exact solutions: plane **Couette**, plane **Poiseuille** (`Q = Gh³/(12μ)`), **Hagen–Poiseuille** pipe flow (`Q = πGR⁴/(8μ)`); energy dissipation `∫ v·Δv = -∫|∇v|²` | ✅ |

### Heat conduction (`Thermal/`)

| File | Content | Status |
|---|---|---|
| `Thermoelastic.lean` | **Duhamel–Neumann** law and its inverse, free expansion is stress-free, restrained bar `σ = -EαΔT` (and spring-restrained), **bimetallic strip** (Timoshenko's curvature, existence and uniqueness), thermal bending and the clamped-beam moment, thick cylinder under logarithmic temperature | ✅ |
| `Heat.lean` | 1D heat equation with Fourier's law: separated solutions and their decay, **energy decay**, **uniqueness**, exponential decay rate `E(t) ≤ E(0)e^{-2κ(π/L)²t}` (Wirtinger), steady conduction and convergence to the steady state | ✅ |

### Structures (`Structures/`)

| File | Content | Status |
|---|---|---|
| `Cables.lean` | **parabolic cable** under uniform load (`H = qL²/(8f)`, support tension is the maximum, length bounds), **catenary** (tension `= wy`, arc length `a sinh(x/a)`, lies above the osculating parabola), **funicular and three-hinged arches** (parabolic arch has zero bending moment, thrust `M₀(L/2)/f`) | ✅ |

### Fracture, fatigue and contact (`Fracture/`, `Fatigue/`, `Contact/`)

| File | Content | Status |
|---|---|---|
| `Fatigue/Basic.lean` | **Basquin** S–N law (inverse, monotone, log–log linear), **Goodman/Gerber/Soderberg** mean-stress corrections and their ranking, **Palmgren–Miner** damage (additive, order-independent, blocks to failure, equivalent amplitude), **Paris law** crack-growth life (closed form for `m ≠ 2` and `m = 2`), critical crack length | ✅ |
| `Fracture/Basic.lean` | **Griffith** energy balance (critical length, unstable maximum, fracture stress), energy release rate, `K_I = σ√(πa)`, **Irwin** `G = K²/E'`, compliance method (fixed load = fixed grip), **double cantilever beam** (unstable at fixed load, stable at fixed grip), near-tip scaling | ✅ |
| `Contact/Hertz.lean` | **Hertz contact** of spheres (effective radius and modulus, contact radius, approach, pressure distribution with **force balance**, `P = (4/3)E*√R δ^{3/2}`, contact stiffness `2E*a`, scaling laws) and cylinders | ✅ |

### Geotechnics (`Geotechnics/`)

| File | Content | Status |
|---|---|---|
| `Consolidation.lean` | Terzaghi effective stress (layered soils, water table), **1D consolidation** as the heat equation (energy decay, uniqueness, decay rate), series solution, **degree of consolidation** (`Σ 2/M² = 1` from `ζ(2)`, `U → 1`), settlement | ✅ |
| `Seepage.lean` | **Darcy's law** and continuity ⇒ Laplace's equation, anisotropic soils (coordinate stretch), 1D and layered seepage (`K_v ≤ K_h`), seepage force, **quick condition** and heave safety, **Dupuit** unconfined flow, Dirichlet principle and uniqueness | ✅ |
| `Strength.lean` | **Mohr–Coulomb** failure (circle tangent to the failure line, failure plane at `π/4 + φ/2`, principal-stress form), **Rankine** active/passive/at-rest coefficients and thrust, tension crack, **infinite slope** factor of safety (dry, cohesive, with seepage), bearing capacity factors (`N_c → π + 2`) | ✅ |

### Beams and 1D Sobolev spaces (`Beams/`, `Sobolev1D/`)

| File | Content | Status |
|---|---|---|
| `Interval.lean`, `Poly.lean` | calculus on an interval, polynomial deflections | ✅ |
| `Bar.lean` | axial bar | ✅ |
| `EulerBernoulli/` | equation, boundary conditions, uniqueness, energy, closed-form solutions | ✅ |
| `Timoshenko/` | equations, uniqueness, Euler–Bernoulli limit | ✅ |
| `Buckling.lean`, `Wirtinger.lean`, `Rayleigh.lean` | Euler buckling, Wirtinger's inequality, Rayleigh quotient | ✅ |
| `Vibration.lean` | free vibrations of Euler–Bernoulli beams: simply supported modes `ωₙ = (nπ/L)²√(EI/ρA)`, orthogonality, **energy conservation and uniqueness** for pinned, clamped and free ends, cantilever mode shapes and the frequency equation `cos βL cosh βL = -1` (root in `(π/2, π)`), Rayleigh quotient | ✅ |
| `BucklingBC.lean` | column buckling for all classical end conditions: general solution (with converse), **clamped–free** `π²EI/(4L²)`, **clamped–clamped** `4π²EI/L²`, **clamped–pinned** `kL ≈ 4.493` with proved bounds `20.16 < P_crL²/EI < 20.25` and effective-length factor in `(0.69, 0.70)`; imperfect columns and the amplification factor; **lateral–torsional buckling** `M_cr = (π/L)√(EI_y GJ)` | ✅ |
| `ThinWalled.lean` | thin-walled sections: second moments and the parallel-axis theorem, shear flow, **shear centre of a channel** `e = 3b²/(h + 6b)`, **Bredt–Batho** torsion (`T = 2Aq`, `J = 4A²/∮ds/t`, box and tube), open vs closed tube `J_closed/J_open = 3R²/t²` | ✅ |
| `Winkler.lean` | **beam on an elastic foundation**: homogeneous solutions `e^{±βx}(cos, sin)βx`, Hetényi's point-load solution (max deflection `Pβ/(2k)`, max moment `P/(4β)`, first zero at `3π/(4β)`), uniform load | ✅ |
| `String.lean` | vibrating string: **d'Alembert's formula** for the Cauchy problem, normal modes and their orthogonality, energy conservation and **uniqueness** with fixed ends, Mersenne's laws | ✅ |
| `Sobolev1D/` | `L²` primitives, weak bar, weak Euler–Bernoulli beams (cantilever, clamped–clamped, propped cantilever), weak Timoshenko cantilever: well-posedness and classical ⇒ weak | ✅ |

### Plates (`Plates/`)

| File | Content | Status |
|---|---|---|
| `KirchhoffLove.lean` | plate equation, moments, simply supported edges | ✅ |
| `Energy.lean` | Kirchhoff–Love bending energy; null Lagrangian `∫∇²w:∇²v = ∫ΔwΔv`; strong ⇔ stationary on open sets; minimum potential energy for clamped plates | ✅ |
| `Navier.lean` | single-mode Navier solutions | ✅ |
| `Circular.lean` | axisymmetric circular plates: general solution of `Δ_r²w = q/D`, **clamped** (`qa⁴/(64D)` at the centre) and **simply supported** plates, deflection ratio `(5+ν)/(1+ν)`, radial and tangential moments | ✅ |
| `Membrane.lean` | vibrating membranes: rectangular modes `ω_mn = cπ√((m/a)² + (n/b)²)` and their orthogonality, square-membrane degeneracy, static membrane under pressure | ✅ |
| `Shells.lean` | thin shells: pressure vessels from cut equilibrium (`pR/t`, `pR/(2t)`), **Laplace equation** for shells of revolution, thin-wall limit of Lamé, radial expansion, **cylindrical shell bending** as a Winkler beam with decay length `∝ √(Rt)` | ✅ |
| `Dynamics.lean` | simply supported rectangular plates: **free vibration** modes `ω_mn = π²((m/a)² + (n/b)²)√(D/ρh)`, square-plate degeneracy; **plate buckling** under uniaxial compression, buckling coefficient `k ≥ 4` with equality iff `a/b = m`, `N_cr = 4π²D/b²`; biaxial buckling | ✅ |
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
| `RayleighWaves.lean` | **Rayleigh surface waves**: `κ²` ranges, rationalized secular cubic, **existence and uniqueness** of a surface wave slower than the shear wave, Poisson solid `c_R = c_T√(2 - 2/√3)` with `0.919 < c_R/c_T < 0.920`, depth decay of the potentials | ✅ |
| `SaintVenantPrinciple.lean` | **Saint-Venant's principle** for antiplane shear in a strip: decaying modes `e^{-nπx/b}cos(nπy/b)`, section-independence of the resultant, zero-mean Wirtinger inequality, **energy decay** `E(x) ≤ E(0)e^{-2πx/b}` for self-equilibrated end loads (Horgan–Knowles) | ✅ |
| `Torsion.lean` | Saint-Venant torsion: warping displacement, strains, Navier–Lamé ⇔ harmonic warping, Prandtl stress function `ΔΦ = -2μα`; circular shaft `T = μJα`, elliptic bar `T = μαπa³b³/(a² + b²)` | ✅ |
| `H10.lean` | `H¹₀(Ω; ℝⁿ)` as the closure of smooth compactly supported fields in `L² × L²`; **Korn's identity and inequality by density**, coercivity of the isotropic energy | ✅ |
| Saint-Venant on simply connected domains | needs Mathlib's Poincaré lemma beyond convex sets | ⬜ |

## DiscreteMechanics

| File | Content | Status |
|---|---|---|
| `Truss.lean` | pin-jointed frames, compatibility/equilibrium matrices, virtual work, Maxwell–Calladine index theorem, rigid motions | ✅ |
| `Chain.lean` | lattice dynamics of spring chains: monatomic **dispersion relation** `ω² = (4k/m) sin²(qa/2)` (iff), Brillouin zone, sound speed `a√(k/m)`, fixed-end normal modes, diatomic chain: acoustic and optical branches and the **band gap** | ✅ |
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
| `Relativistic.lean` | special relativity: Lorentz boosts preserve the interval, **velocity addition** (speed of light not exceeded), rapidities add, time dilation, length contraction, **`E² = (pc)² + (mc²)²`**, Newtonian limit, work–energy theorem, hyperbolic motion, four-momentum conservation in all frames | ✅ |
| `Kepler.lean` | Kepler problem: conservation of `L`, `E` and the Laplace–Runge–Lenz vector, Kepler's first and second laws, eccentricity–energy relation | ✅ |
| `KeplerThird.lean` | semi-axes from `E` and `L`, `a = -k/(2E)`, `b² = a p`, peri/apoapsis bounds; **Kepler's third law** `T² = 4π² m a³ / k` (given that one period sweeps the area `π a b`) | ✅ |
| `KeplerPeriod.lean` | eccentric anomaly and **Kepler's equation**; the motion is periodic with least period `2π/n`, `n = √(k/(m a³))`; **Kepler's third law** `T² = 4π² m a³ / k` for the actual period (no swept-area hypothesis) | ✅ |
| `Orbits.lean` | orbital mechanics: **vis-viva** (elliptic, parabolic, hyperbolic), circular orbits and escape speed `√2 v_circ`, apsides (`v_p r_p = v_a r_a`, apsidal speeds), **Hohmann transfer** Δv's, transfer time, escape limit | ✅ |
| `EffectivePotential.lean` | general central potentials: energy and angular momentum, `E = ½mṙ² + U_eff(r)`, allowed region `U_eff(r) ≤ E`, turning points | ✅ |
| `Rutherford.lean` | hyperbolic orbits (`e > 1` iff `E > 0`), the orbit stays in a cone about the LRL vector, deflection angle `tan(Θ/2) = |k|/(2Eb)`, **Rutherford cross section** `(k/4E)²/sin⁴(Θ/2)` | ✅ |
| `IsotropicOscillator.lean` | `m ẍ = -k x` in space: explicit solution and uniqueness, all orbits periodic (isochronous), conserved energy, angular momentum and **Fradkin tensor**, elliptical orbits centred at the origin, `⟨T⟩ = ⟨U⟩` over a period | ✅ |
| `Friction.lean` | Coulomb friction: block on an incline (rest ⇔ `tan α ≤ μ_s`, angle of repose, optimal pulling angle `arctan μ`), **capstan equation** `T₂ = T₁e^{μθ}` (with uniqueness), oscillator with dry friction (linear amplitude decay `4μN/k` per cycle, rest zone), rolling without slipping | ✅ |
| `Constraints.lean` | d'Alembert's principle ⇔ Lagrange multiplier, ideal constraints do no work, energy conservation; spherical pendulum (vertical angular momentum, energy, tension), simple pendulum | ✅ |
| `RigidBody.lean` | inertia tensor (symmetric, positive semidefinite), Steiner, König, Euler's equations and their invariants | ✅ |
| `Oscillator.lean` | harmonic oscillator (solution, uniqueness, periodicity), damped oscillator (dissipation, underdamped solution) | ✅ |
| `ForcedOscillator.lean` | driven damped oscillator: steady state, amplitude–phase form, transients, **resonance** (maximum amplitude at `√(ω₀² - 2γ²)`), undamped secular growth, power balance over a period, beats | ✅ |
| `Duhamel.lean` | SDOF response to arbitrary loads: unit impulse response, **Duhamel's integral** solves the forced equation (and is the unique solution from rest), step load with dynamic amplification 2, **response spectrum** bounds `S_d ≤ (1/ω_d)∫|a_g|`, `S_a = ω²S_d` | ✅ |
| `Lagrangian.lean` | Lagrangian mechanics with one degree of freedom: Beltrami energy, cyclic coordinates, Hamilton's principle ⇔ Euler–Lagrange, natural systems | ✅ |
| `EulerStability.lean` | stability of steady rotations: linearized Euler equations, `λ < 0` iff largest/smallest axis, explicit exponentially growing solution about the intermediate axis; nonlinear stability bounds from the conserved `|L|² - 2I₁T` | ✅ |
| `HeavyTop.lean` | Lagrange's heavy symmetric top (Euler–Poisson equations): energy, vertical angular momentum, spin; reduction to `I₁²u̇² = I₁(2E' - 2Mgℓu)(1 - u²) - (b - au)²`; sleeping top under `(I₃ω₃)² > 4I₁Mgℓ` | ✅ |
| `Rotation.lean` | rigid-body kinematics: `Ω = ṘRᵀ`, `W = RᵀṘ` skew, `Ω = RWRᵀ`, axial vector, Poisson's formula, rigid velocity field, isometry | ✅ |
| `RotatingFrame.lean` | motion relative to a rotating frame: `ẍ = R(a + 2w×v + w×(w×y) + ẇ×y)`; Coriolis, centrifugal and Euler forces | ✅ |
| `Foucault.lean` | **Foucault pendulum**: horizontal Coriolis force, complex form, the solution is a pendulum rotated at `-Ω sin φ` (precession of the plane of oscillation), precession period, equator and poles, conserved energy and angular momentum | ✅ |
| `Hamiltonian.lean` | Hamilton's equations, Poisson brackets, evolution `Ḟ = {F, H}`, energy conservation, Liouville (divergence-free Hamiltonian field), natural systems, Legendre transform (Euler–Lagrange solutions are Hamiltonian flows) | ✅ |
| `Jacobi.lean` | Poisson bracket of `C²` functions: antisymmetry, **Jacobi identity** | ✅ |
| `LinearHamiltonian.lean` | linear Hamiltonian systems `ż = -J S z`: Hamiltonian matrices, the flow is symplectic and `det Φ(t) = 1` (Liouville) | ✅ |
| `Recurrence.lean` | **Poincaré recurrence**: volume-preserving maps of a finite-volume invariant region are conservative; for Hamiltonian (and divergence-free) flows a.e. point of any measurable subset of a bounded invariant region returns infinitely often | ✅ |
| `HamiltonJacobi.lean` | **Jacobi's theorem** (1 DOF, time-dependent, mixed partials as hypotheses); harmonic oscillator in action–angle variables: `H = ωI`, Jacobian `1`, flow, action = phase-space area / 2π | ✅ |
| `Canonical.lean` | linear canonical transformations: Poisson brackets and Hamiltonian flows are preserved by symplectic matrices, symplectic group, linear Hamiltonian flows are canonical | ✅ |
| `LiouvilleFlow.lean` | for a `C²` flow of a vector field: variational equation, **Liouville formula** `∂ₜ det DΦ = (div X) det DΦ`, `det DΦ = 1` and **volume preservation** for divergence-free fields, applied to Hamiltonian flows (flow taken as data: Mathlib has no smooth dependence on initial conditions) | ✅ |
| `Variational.lean` | Beltrami identity; plane geodesics are straight lines; **catenary** `a cosh((x-b)/a)` is an extremal; **brachistochrone**: the cycloid satisfies Beltrami and Euler–Lagrange; **tautochrone**: period on the cycloid independent of amplitude | ✅ |
| `Noether.lean` | Lagrangians on `ℝⁿ`: energy conservation, Noether's theorem, translation and linear (rotation) symmetries | ✅ |
| `Routh.lean` | cyclic coordinates: conserved momenta; **Routh reduction** (two coordinates, local inversion), the Routhian obeys Euler–Lagrange; planar central motion reduces to `m r̈ = -V_eff'(r)` | ✅ |
| `SmallOscillations.lean` | `M q̈ + K q = 0`: energy, normal modes, superposition, Rayleigh quotient, stability, modal orthogonality | ✅ |
| `ModalDamping.lean` | damped MDOF structures `Mq̈ + Cq̇ + Kq = f`: energy dissipation, modal coordinates, classical damping decouples the modes, **Rayleigh damping** (fitting α, β to two damping ratios), Caughey criterion, modal superposition of the free response | ✅ |
| `Rotordynamics.lean` | **Jeffcott rotor**: synchronous whirl, amplitude, **critical speed**, phase lag `π/2` at critical, self-centering above it; **gyroscopic systems** conserve energy and stay bounded; **gyroscopic stabilization** iff `g² ≥ (√k₁ + √k₂)²` | ✅ |
| `Stability.lean` | natural systems `M q̈ = -∇U`: equilibria, energy, **Lagrange–Dirichlet theorem** (strict minimum ⇒ Lyapunov stable in phase space), linearization, positive definite Hessian ⇒ strict minimum ⇒ stable | ✅ |
| `DoublePendulum.lean` | planar double pendulum: kinetic energy from positions, Lagrangian and Euler–Lagrange equations, energy conservation, positive definite mass matrix, **nonlinear stability** of the hanging position, normal-mode frequencies `(g/ℓ)(2 ± √2)`, inverted equilibria fail the second-derivative test | ✅ |
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
