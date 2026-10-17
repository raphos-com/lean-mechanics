# Changelog

## Unreleased

### Project
- Licensed under Apache-2.0 (`LICENSE`, Lake and `CITATION.cff` metadata); README with
  highlights linked to the API documentation, dependency instructions and a note on AI assistance.

### ClassicalMechanics (new library)
- `Particles`: systems of particles with action and reaction: momentum theorem and conservation,
  centre of mass theorem, angular momentum theorem for central internal forces, kinetic energy
  theorem, conservation of energy.
- `Kepler`: inverse-square central force: conservation of angular momentum (planar motion,
  Kepler's second law), energy and the Laplace–Runge–Lenz vector; orbit equation
  `A · x + m k r = |L|²` (conic with a focus at the origin); `|A|² = m²k² + 2mE|L|²`; ellipse iff
  `E < 0`.
- `RigidBody`: inertia tensor symmetric and positive semidefinite, Huygens–Steiner, angular
  momentum `Jω` and König's theorem for rigid velocity fields, torque-free Euler equations conserve
  energy and `|L|²`, steady rotations about principal axes.
- `Oscillator`: harmonic oscillator solution, uniqueness (energy argument) and periodicity; energy
  dissipation `Ė = -c ẋ²` and the underdamped solution of the damped oscillator.
- `Lagrangian`: chain rule, Beltrami energy conservation, cyclic coordinates, Hamilton's principle
  (stationary action for smooth variations in `(a, b)` ⇔ Euler–Lagrange), natural Lagrangians
  `½mv² - U(q)` give Newton's law.
- `Noether`: Lagrangians on `ℝⁿ`, energy conservation, **Noether's theorem** (conserved charge
  `L_v · ξ(q)` of an infinitesimal symmetry), translation and linear symmetries.
- `SmallOscillations`: `M q̈ + K q = 0`: energy, normal modes `cos(ωt) φ` with `Kφ = ω²Mφ`,
  superposition, Rayleigh quotient, stability for positive definite `K`, orthogonality of modes,
  existence of `n` orthonormal modes for `M = I` and positive semidefinite `K`.
- `Hamiltonian`: Hamilton's equations, Poisson brackets (antisymmetry), evolution `Ḟ = {F, H}`,
  constants of the motion, energy conservation, **Liouville's theorem** (the Hamiltonian vector
  field of a `C²` Hamiltonian is divergence-free), natural systems give Newton's law; Legendre
  transform: under the Legendre relations, Euler–Lagrange solutions are Hamiltonian flows.
- `Jacobi`: Poisson brackets of `C²` functions on phase space are antisymmetric and satisfy the
  **Jacobi identity** (differentiation of the bracket and symmetry of second derivatives).
- `LinearHamiltonian`: quadratic Hamiltonians `½ zᵀ S z`: the matrix `A = -J S` is Hamiltonian,
  the fundamental matrix of `ż = A z` is **symplectic** for all times and has **determinant 1**
  (Liouville's theorem for linear systems).
- `KeplerThird`: semi-major axis `a = -k/(2E)`, `b² = a p`, periapsis and apoapsis bounds on `r`,
  **Kepler's third law** `T² = 4π² m a³ / k` from the swept-area hypothesis.
- `Duhamel`: impulse response, Duhamel's integral and uniqueness from rest, step-load dynamic
  amplification, response spectrum bounds.
- `ModalDamping`: damped multi-degree-of-freedom structures, modal decoupling, Rayleigh damping,
  Caughey criterion, modal superposition.
- `DoublePendulum`: equations of motion, energy, mass matrix, Lyapunov stability of the hanging
  position, normal modes for equal masses and lengths.
- `Relativistic`: Lorentz boosts, velocity addition, rapidity, time dilation and length
  contraction, energy–momentum relation, Newtonian limit, hyperbolic motion, four-momentum.
- `Orbits`: vis-viva equation, circular orbits, escape speed, apsidal speeds, Hohmann transfers.
- `Foucault`: the Foucault pendulum: precession of the plane of oscillation at `Ω sin φ`, period,
  conserved quantities.
- `Recurrence`: Poincaré recurrence for divergence-free and Hamiltonian flows on bounded invariant
  regions, from Liouville's theorem and Mathlib's recurrence theorem.
- `ForcedOscillator`: steady-state response, resonance frequency and peak amplitude, undamped
  resonance, power balance, beats.
- `Variational`: Beltrami identity, straight-line geodesics, the catenary, the brachistochrone
  (cycloid) and the tautochrone property.
- `IsotropicOscillator`: solution, periodicity and isochronism, the Fradkin tensor, elliptical
  orbits, virial theorem over a period.
- `Rocket`: the rocket equation, Tsiolkovsky's formula, rockets in uniform gravity, constant
  burn rate.
- `Collisions`: restitution, kinetic energy loss, elastic collisions (relative speed, right-angle
  scattering of equal masses).
- `KeplerPeriod`: eccentric anomaly, Kepler's equation `E - e sin E = n t + const`, the bound
  orbit is periodic with least period `2π/n`, so **Kepler's third law** holds unconditionally.
- `EffectivePotential`: general central forces: conservation laws, radial energy
  `E = ½ m ṙ² + U_eff(r)`, allowed region and turning points.
- `Galilean`: boosts, rotations and time shifts of particle systems, transformation laws for
  momentum and kinetic energy, conserved boost charge, uniform motion of the centre of mass.
- `Routh`: conserved momenta of cyclic coordinates, Routh reduction, planar central motion.
- `HamiltonJacobi`: Jacobi's theorem for complete integrals of the Hamilton–Jacobi equation;
  action–angle variables of the harmonic oscillator.
- `Stability`: equilibria of natural systems, **Lagrange–Dirichlet theorem** (Lyapunov stability
  of strict minima of the potential), linearization `M ξ̈ + K ξ = 0`, positive definite Hessian ⇒
  quadratic growth ⇒ stability.
- `HeavyTop`: Lagrange's top: conservation of energy, vertical angular momentum and spin,
  reduction of the nutation to `u̇² = f(u)` with Lagrange's cubic, the fast sleeping top.
- `Rutherford`: hyperbolic Kepler orbits, cone inequality, deflection angle
  `tan(Θ/2) = |k|/(2Eb)` and the **Rutherford cross section** `(k/(4E))² / sin⁴(Θ/2)`.
- `Constraints`: d'Alembert's principle (no virtual work ⇔ Lagrange multiplier), ideal
  constraints do no work; spherical pendulum: conserved vertical angular momentum and energy,
  explicit tension; simple pendulum energy integral.
- `Canonical`: symplectic matrices preserve the symplectic form and Poisson brackets and map
  Hamiltonian flows to Hamiltonian flows; the flow of a linear Hamiltonian system is canonical.
- `EulerStability`: linearized Euler equations about a steady rotation, `δω̈₂ = λ δω₂` with
  `λ < 0` iff the axis is the largest or smallest (**tennis-racket theorem**), explicit growing
  solution otherwise; nonlinear stability bounds via the conserved `|L|² - 2 I₁ T`.
- `Virial`: `Ġ = 2T + Σ xᵢ · Fᵢ` for the virial `G = Σ mᵢ xᵢ · vᵢ`; **virial theorem** (bounded
  virial ⇒ `⟨2T + Σ xᵢ · Fᵢ⟩ → 0`) and `⟨2T⟩ = k⟨U⟩` for homogeneous potentials.
- `TwoBody`: reduction of an isolated pair to one body of reduced mass, `μ r̈ = F`, and the
  kinetic energy split `T = ½ M |v_G|² + ½ μ |ṙ|²`.
- `RotatingFrame`: velocity and acceleration relative to a rotating frame; Newton's law in the
  moving frame with **Coriolis**, **centrifugal** and **Euler** forces.
- `LiouvilleFlow`: for a `C²` flow `Φ` of a vector field `X`, the variational equation (from the
  symmetry of second derivatives), the **Liouville formula** `∂ₜ det DΦ = (div X)(Φ) det DΦ`,
  `det DΦ = 1` for divergence-free fields and **volume preservation** `μ(Φₜ(A)) = μ(A)`; applied
  to Hamiltonian vector fields.
- `Rotation`: rigid motions `x = c + R X`: spatial and body angular velocities are skew,
  `Ω = R W Rᵀ`, skew matrices act as cross products with their axial vector, **Poisson's formula**
  `ė = ω × e`, rigid velocity field `ẋ = ċ + ω × (x - c)`, distances preserved.
- `NormalModes`: **simultaneous diagonalization**: `n` `M`-orthonormal modes for any positive
  definite `M` and positive semidefinite `K`.

### Restructuring
- `Frames/` moved to the new library **`DiscreteMechanics`** (namespace `DiscreteMechanics`).
- `papers/` is a separate Lake project depending on both libraries; the root package and
  `CITATION.cff` describe the libraries only.
- Design and tracking documents moved to `docs/`.

### DiscreteMechanics
- `Chain`: monatomic and diatomic spring chains: dispersion relations, Brillouin zone, long-wave
  sound speed, fixed-end normal modes, acoustic/optical branches and the band gap.
- `Stiffness`: direct stiffness method for trusses: symmetry, positive semidefiniteness and kernel
  of `K = Cᵀ diag(k) C`, assembly, supported structures have positive definite reduced stiffness
  and unique displacements, minimum potential energy, Maxwell–Betti, a worked two-bar truss.
- `LongWave`: `(Σⱼ(2cos⟪k,tⱼ⟫ − 2) + Σⱼ⟪k,tⱼ⟫²)/‖k‖² → 0` for any lattice vectors, the
  isotropic limit `−c`, and the long-wave limit `s z → δ₀⁻¹ N₀ y₀` of Bloch solutions computed
  through an adjugate (`N M = δ I`).
- `Truss`: pin-jointed frames; compatibility matrix `C`, equilibrium matrix `Cᵀ`, virtual work;
  **Maxwell–Calladine** `N₀ − N_ss = d|N| − |B|` (index of a matrix by rank–nullity); rigid
  motions are zero modes; the triangle is rigid (`N₀ = 3`, `N_ss = 0`).
- `Periodic`: periodic frames; Bloch compatibility matrix `C(θ)`, Bloch reduction of the infinite
  frame, Maxwell–Calladine at every wave vector (complex index with `C(θ)ᴴ`), Maxwell lattices
  have as many zero modes as self-stresses at every `θ` and at least `d` self-stresses at `θ = 0`.
- `Winding`: winding number `(2πi)⁻¹∮ p'/p` of a polynomial around the unit circle; **argument
  principle**: it equals the number of roots in the open unit disk (with multiplicity), and is
  additive under products.

### Elastostatics
- `LameCylinder`: thick-walled cylinders and spheres under pressure (Lamé): general radial
  solution and uniqueness, stresses, maximum hoop stress, thin-wall limit.
- `Existence`: Poincaré inequality `‖u‖² ≤ 4R²‖∇u‖²` on slabs and bounded sets, coercivity of the
  Lamé energy on `H¹₀`, existence and uniqueness of weak solutions of clamped isotropic
  elastostatics by Lax–Milgram, and the principle of minimum potential energy.
- `Torsion`: Saint-Venant torsion: equilibrium ⇔ harmonic warping, Prandtl stress function,
  torsional rigidity of circular (`T = μJα`) and elliptic sections.
- `Airy`: Airy stress function: equilibrium, compatibility ⇔ `Δ²φ = 0` for plane stress and
  plane strain, polynomial solutions (tension, bending, cantilever, simply supported beam).
- `Castigliano`: Castigliano's theorems (`∂U/∂u = f`, `∂U*/∂f = u`), Clapeyron, Maxwell–Betti,
  unit-load method; truss deflections `Σ N n L/(EA)` and the cantilever tip deflection.
- `H10`: `H¹₀(Ω; ℝⁿ)` as the closure of the graphs of smooth compactly supported fields in
  `L² × L²`; Korn's identity `‖∇U‖² + ‖div U‖² = 2‖ε(U)‖²` and inequality by density;
  coercivity `μ‖∇U‖² ≤ 2μ‖ε(U)‖² + λ‖div U‖²`.
- `Elastostatics/Variational`: shared integration-by-parts toolkit (`∫ div φ div ψ`,
  `∫ ε(φ):ε(ψ)`), fundamental lemma of the calculus of variations on open sets.
- `Elastostatics/NavierLame`: strain energy `∫ λ div u div v + 2μ ε(u):ε(v)`, residual
  `−(μΔu + (λ+μ)∇div u)`, **Navier–Lamé equations ⇔ stationary energy** on open sets.
- `Elastostatics/PlaneWave`: the residual of `a g(k·x)` is `−A(k)a g''`; travelling waves
  `a g(k·x − ct)` solve `div σ = ρü` under the propagation condition `A(k)a = ρc²a`.
- `Elastostatics/Korn`: **Korn's first inequality** `∫|∇u|² ≤ 2∫|ε(u)|²` for compactly supported
  `C²` fields in `ℝⁿ`, via `∫|∇u|² + ∫(div u)² = 2∫|ε(u)|²` (integration by parts twice and
  symmetry of second derivatives).

### Constitutive
- `Hyperelastic/Linearization`: frame indifference and isotropy of the SVK, neo-Hookean and
  Mooney–Rivlin energies; `DP(I)` is the isotropic elasticity tensor (Lamé moduli identified);
  second-order energy expansions; neo-Hookean uniaxial tension.
- `Viscoelastic`: Kelvin–Voigt, Maxwell and Zener models: creep and relaxation solutions,
  uniqueness, long-time limits, energy dissipation, harmonic response and loss per cycle.
- `Constitutive/Ellipticity`: isotropic acoustic tensor `μ|n|²I + (λ+μ)n⊗n`; **strong ellipticity
  iff `μ > 0 ∧ λ + 2μ > 0`** (dimension ≥ 2); plane waves are longitudinal with `ρc² = λ + 2μ` or
  transverse with `ρc² = μ`.

### Geotechnics
- `Geotechnics/Seepage`: Darcy flow, anisotropic and layered soils, quick condition, Dupuit flow,
  Dirichlet principle.
- `Geotechnics/Consolidation`: effective stress, Terzaghi consolidation (series solution, degree
  of consolidation, settlement), reusing the heat equation.
- `Geotechnics/Strength`: Mohr–Coulomb failure via Mohr's circle, Rankine earth pressures and
  thrust, infinite-slope factors of safety, bearing capacity factors.

### Thermal
- `Thermal/Heat`: the 1D heat equation: modes, energy decay, uniqueness, exponential decay rate,
  steady conduction and convergence to it.

### Fluids
- `Fluids/Viscous`: incompressible Navier–Stokes, viscous stress, Couette, plane Poiseuille and
  Hagen–Poiseuille flows with their flow rates, viscous energy dissipation.
- `Fluids/Ideal`: material derivative, incompressible Euler equations, Lamb identity, Bernoulli's
  theorem, potential flow, Kelvin's circulation theorem.

### Stress
- `Stress/Mohr`: plane stress transformation, invariants, Mohr's circle, principal stresses and
  maximum shear (attained), 2D von Mises identity.

### Kinematics
- `PoincareStar`: Poincaré lemma for closed 1-forms on open **star-shaped** sets (segment
  integrals from the centre, via convex cones over balls); `SaintVenantStar`: Saint-Venant
  sufficiency on open star-shaped domains.
- `Kinematics/SaintVenant`: **Saint-Venant sufficiency** on open convex domains: a symmetric `C²`
  strain satisfying the compatibility conditions is `sym ∇u`, by two applications of Mathlib's
  Poincaré lemma (rotation field `W` with `∂ₖWᵢⱼ = ∂ⱼεᵢₖ − ∂ᵢεⱼₖ`, then `∇u = ε + W`).

### Beams (weak forms)
- `Beams/Vibration`: beam vibration modes, orthogonality, energy conservation and uniqueness for
  pinned/clamped/free ends, the cantilever frequency equation, Rayleigh's quotient.
- `Beams/String`: the 1D wave equation: d'Alembert's formula, normal modes, orthogonality, energy
  conservation and uniqueness for a string with fixed ends, Mersenne's laws.
- `Sobolev1D/BeamWeakBC`: Lax–Milgram on closed subspaces; weak **clamped–clamped** and
  **propped-cantilever** Euler–Bernoulli beams: existence, uniqueness, classical ⇒ weak.
- `Sobolev1D/TimoshenkoWeak`: weak Timoshenko cantilever in (bending strain, shear strain):
  existence, uniqueness, classical ⇒ weak.

### Plates
- `Plates/Circular`: clamped and simply supported circular plates under uniform load, moments.
- `Plates/Membrane`: rectangular membrane modes and orthogonality, static circular membrane.
- `Plates/Dynamics`: vibration modes and frequencies of simply supported rectangular plates, plate
  buckling coefficient `k ≥ 4`, biaxial buckling.
- `Plates/Grillage`: orthotropic Kirchhoff–Love plates and their Navier solution; the square beam
  grillage homogenizes to `D₁₁ = D₂₂ = EI/ℓ`, `D₁₂ = 0`, `D₆₆ = GJ/2ℓ` (Timoshenko–Woinowsky §86),
  is isotropic iff `GJ = EI`, central deflection `q₀ℓa⁴/(2π⁴(EI + GJ))`.
- `Plates/Energy`: Kirchhoff–Love bending form `a(w,v) = D∫ν ΔwΔv + (1−ν)∇²w:∇²v` in `ℝⁿ`, the
  classical 2D density, **null Lagrangian** `∫∇²w:∇²v = ∫ΔwΔv`, `a(w,v) = D∫Δ²w v`,
  **strong ⇔ stationary** (`DΔ²w = q` in an open `U` iff `a(w,v) = ∫qv` for all test functions
  in `U`), and **minimum potential energy** for compactly supported solutions; the fundamental
  lemma of the calculus of variations on open sets (`eq_zero_on_of_integral`).
- `Plates/MindlinEnergy`: Mindlin–Reissner bilinear form
  `D∫ν divφ divψ + (1−ν)ε(φ):ε(ψ) + S∫γ·γ`, integration by parts to the residuals
  `−S(Δw + div φ)` and `−D(ν∇div φ + (1−ν)div ε(φ)) + Sγ`, **strong ⇔ stationary**, nonnegativity.

### Papers (`papers/`, see each README)
- `Nexorade`, `Miura`, `KaneLubensky`, `Gridshells`, `BendingGradient`.
- `ChevronCore` (Lebée–Sab 2010): analytical bounds on the transverse shear moduli of chevron
  folded cores, their ordering, the exact case, and the comparison with honeycombs.
- `Gridshells/Sphere`: a Chebyshev net on the unit sphere satisfies the sine-Gordon equation
  `ω_uv = −sin ω`; its quadrilaterals have area `< 2π`.

### Phase 7 — plates (in progress)
- `Plates/KirchhoffLove`: rectangular plate, partial derivatives, biharmonic operator, plate
  equation `DΔ²w = q`, bending moments, simply supported edges.
- `Plates/Navier`: `Δ²(sin αx sin βy) = (α² + β²)² sin αx sin βy`; **Navier's single-mode solution**
  of the simply supported plate; central deflection `q₀a⁴/(4π⁴D)` of a square plate.
- `Plates/MindlinReissner`: Mindlin–Reissner equations and hard simple supports; single-mode Navier
  solution `W = W_K(1 + Dk²/S)`, `φ = −∇w_K`; **Kirchhoff limit** `W − W_K = q₀/(Sk²) → 0`.

### Phase 5 — linear elastostatics
- `Elastostatics/Weak`: abstract weak formulation `⟪ℂε(u), ε(v)⟫ = ℓ(v)` under the `KornSetting`
  hypothesis structure (Korn's inequality); **Lax–Milgram well-posedness**; the weak solution is the
  unique minimiser of `½a(v,v) − ℓ(v)`; non-vacuity witness.
- `Elastostatics/Basic`: strain and stress fields `ε(u) = sym ∇u`, `σ = ℂε`; the **work
  identity** `∫_P σ : ε = ∫_∂P u·σn + ∫_P b·u`; **Clapeyron** `2U = ∫ b·u + ∫ u·σn`; **Betti
  reciprocity**; **Kirchhoff uniqueness** (solutions whose difference does no boundary work
  differ by an infinitesimal rigid displacement); `U ≥ 0`, and `U(u) = 0 ⇒ u` rigid.
- `Elastostatics/MinimumEnergy`: total potential energy `Φ`; `Φ(v) = Φ(u) + U(v − u)`;
  **principle of minimum potential energy** with the rigid-displacement equality case.

### Phase 4 — constitutive theory
- `Constitutive/RivlinEricksen`: **Rivlin–Ericksen representation theorem**: an isotropic tensor
  function satisfies `G(A) = p(A)` for a polynomial `p` (any dimension, via reflections and
  Lagrange interpolation), and `G(A) = φ₀I + φ₁A + φ₂A²` in 3D (Cayley–Hamilton).
- `Constitutive/Hyperelastic/MooneyRivlin`: compressible Mooney–Rivlin energy; exact splitting
  `W_MR = W_neoHooke(λ, κ) + W_SVK(4c₂, −2c₂)`; `P = 2c₁F + 2c₂(I₁(C)F − FC) + (λ ln J − κ)F⁻ᵀ`;
  stress-free reference; linearisation with `μ' = 2c₁ + 2c₂(d − 2)`, `λ' = λ + 4c₂`.
- `Tensor/DetDeriv`: `det` is smooth; **Jacobi's formula** `D det(F)[H] = det F · tr(F⁻¹H)`,
  i.e. `∂J/∂F = J F⁻ᵀ`.
- `Constitutive/Hyperelastic`: `P = ∂W/∂F` (`IsPiolaOf`), uniqueness of the stress;
  **frame indifference ⇔ `W(F) = Ŵ(FᵀF)`**; `P(QF) = Q P(F)` for frame-indifferent materials.
- `Constitutive/Hyperelastic/SVK`: `D E(F)[H] = sym(FᵀH)`; SVK energy, `P = F ℂ E` derived from
  `DW`; linearisation `d/dt P(I + tH)|₀ = ℂH`.
- `Constitutive/Hyperelastic/NeoHookean`: compressible neo-Hookean energy,
  `P = μF + (λ ln J − μ)F⁻ᵀ` derived from `DW`; linearisation to `λ tr(H) I + 2μ sym H`.
- `Constitutive/LinearIsotropic`: Lamé, `(E, ν)`, `(K, G)` moduli with round trips;
  **`λI⊗I + 2μ𝕀ˢʸᵐ` positive definite on `Sym` ⇔ `μ > 0 ∧ dλ + 2μ > 0`** (any `d ≥ 2`),
  ⇔ `E > 0 ∧ −1 < ν < ½` ⇔ `K > 0 ∧ G > 0` in 3D; steel example.

### Phase 3 — stress
- `Stress/BoxRegion`: **non-vacuity of `DivergenceRegion`**: the unit box of any orthonormal basis,
  with face measures and normals `±eᵢ`, via Mathlib's divergence theorem on boxes.
- `Stress/Regions`: homothetic images `c + rP` of divergence regions; small boxes around every
  point; **balance of forces / moments on small boxes ⇒ `div σ + b = 0` and `σ = σᵀ`**,
  hypothesis-free.
- `Stress/Triangle`: surface integrals over flat triangles (affine parametrisation, Gram-determinant
  area); `h⁻² ∫_{x+hT} f dA → area(T) f(x)`.
- `Stress/Cauchy`: **Cauchy's theorem by the tetrahedron argument**. From force balance on Cauchy
  tetrahedra (`TetraBalance`, with genuine face integrals and `O(h³)` volume estimate) and
  continuity of `t`: the tetrahedron identity, **Cauchy's reciprocal theorem** `t(x,-n) = -t(x,n)`,
  and `t(x, n) = σ(x) n` with `σ` continuous. No hypothesis structure needed.
- `Stress/Balance`: divergence of vector and tensor fields; `DivergenceRegion` hypothesis
  structure (first entry in `GAPS.md`); `∫_∂P σn = ∫_P div σ`; localisation; **integral force
  balance ⇒ `div σ + b = 0`**; **moment balance ⇒ `σ` symmetric** (coordinate-free, any
  dimension).
- `Stress/Piola`: first and second Piola–Kirchhoff stresses, conversions, and
  `σ sym ⇔ S sym ⇔ PFᵀ sym`.
- `Stress/Criteria`: `J₂`, von Mises; principal stresses in 3D; `J₂` principal formula;
  `(√3/2) σ_T ≤ σ_vM ≤ σ_T`.

### Phase 2 — kinematics (in progress)
- `Kinematics/Compatibility`: full symmetry of `D³u`; `D²ε = sym D³u`; **Saint-Venant compatibility
  (necessity)** in coordinate-free form, any dimension.
- `Kinematics/Strain`: `C`, `B`, Green–Lagrange, Almansi; `C = U²`, `B = V²`, `E = FᵀeF`,
  `C = I ⇔ F` orthogonal.
- `Kinematics/Observer`: objectivity of `B`, `V`; invariance of `C`, `E`, `U`; `R* = QR`.
- `Kinematics/Infinitesimal`: `E(I+H) = sym H + ½HᵀH`, `‖E − ε‖ ≤ ½‖H‖²`, `ε` as derivative of
  `E`; `ε = 0 ⇔ H` skew.
- `Kinematics/Body`: deformations of an open body, gradient, Jacobian, displacement,
  change of observer; `IsUnit F ↔ det F ≠ 0`.
- `Kinematics/Rigid`: skew displacement gradient (equivalently zero infinitesimal strain) on a
  connected open set ⇒ infinitesimal rigid displacement `u = a + Wx`.

### Phase 6 — 1D structural theories (in progress)
- `Sobolev1D/Primitive`: `H¹(0,L)` modelled by primitives `u = ∫₀ˣ v`, `v ∈ L²((0,L])`: point
  evaluation `⟪χ_(0,x], v⟫`, Sobolev embedding `|u(x)| ≤ √L ‖u'‖`, Poincaré `∫u² ≤ L²‖u'‖²`,
  continuity, and a Fubini lemma `∫ f (P w) = ⟪∫_·ᴸ f, w⟫`.
- `Sobolev1D/BarWeak`: Lax–Milgram for `EA⟪v,w⟫ = ℓ(w)`; **weak forms of the fixed–free and
  fixed–fixed bar are well posed**, and classical `C²` solutions are the weak solutions (`P u' = u`).
- `Sobolev1D/BeamWeak`: `P` as a bounded operator on `L²`; bending moment of a cantilever
  `EI w'' = P(L − t) + ∫∫q`; **weak form of the Euler–Bernoulli cantilever is well posed**, and
  classical `C⁴` solutions are the weak solutions (`P² w'' = w`).
- `Beams/Wirtinger`: **Wirtinger's inequality** `(π/L)² ∫u² ≤ ∫u'²` (`u(0) = u(L) = 0`), proved
  with Picone's identity against `sin(k(x + δ))` and `δ → 0⁺` (no Fourier series);
  `(π/L)² ∫w'² ≤ ∫w''²`.
- `Beams/Rayleigh`: Rayleigh quotient of a pinned column; **`P_cr = π²EI/L²` is its minimum**,
  attained by `sin(πx/L)`.
- `Beams/Interval`: vanishing `(n+1)`-th derivative on `[a, b]` ⇒ Taylor polynomial.
- `Beams/Bar`: axial bar equilibrium; closed-form fixed–free (uniform + end load, linear
  load) and fixed–fixed (uniform) solutions; uniqueness for both boundary conditions.
- `Beams/Poly`: derivatives of polynomial deflections; `beam_poly` tactic macro.
- `Beams/EulerBernoulli/Basic`: `EI w'''' = q`; simply supported, cantilever, clamped–clamped,
  clamped–pinned boundary conditions; uniqueness of `C⁴` solutions for all four.
- `Beams/EulerBernoulli/Solutions`: simply supported and cantilever beams under uniform load,
  cantilever with tip load, simply supported beam with a point load anywhere (piecewise, with
  continuity and shear-jump conditions); `5qL⁴/384EI`, `qL⁴/8EI`, `PL³/3EI`, `PL³/48EI`.
- `Beams/EulerBernoulli/Energy`: Green's formula; fundamental lemma of the calculus of
  variations on an interval; **strong form + natural BCs ⇔ weak form** for simply supported
  beams; exact expansion and Gateaux derivative of `Π`; **minimum potential energy**.
- `Beams/Timoshenko/Basic`: Timoshenko equations; simply supported and cantilever boundary
  conditions; explicit homogeneous solutions; uniqueness of `C²` solutions.
- `Beams/Timoshenko/Limit`: Timoshenko solution built from any `C⁴` Euler–Bernoulli solution
  (`θ = w'`, `w_T = w − EI(w'' − c)/κGA`); **uniform convergence `w_T → w_EB` as `κGA → ∞` for
  general loads** (simply supported and cantilever), with rate `2EI‖w''‖∞/κGA`; non-vacuity of
  the hypotheses; canonical shear corrections `qL²/8κGA` and `PL/κGA`.
- `Beams/Buckling`: pinned–pinned column `EI w'''' + P w'' = 0`: nontrivial solutions exist iff
  `P = n²π²EI/L²` (modes `sin(nπx/L)`); **Euler load `π²EI/L²` is the least buckling load**.

### Phase 1 — tensor algebra (complete)
- `Tensor/Second`: `Lin E`, transpose, trace, determinant (`det Aᵀ = det A`), dyads.
- `Tensor/SymSkew`: `Sym E`, `Skw E`, `sym`/`skw`, `Lin E = Sym ⊕ Skw` with uniqueness.
- `Tensor/Contraction`: double contraction `A ⊡ B = tr(AᵀB)` as an inner product;
  `Frob E` Hilbert-space synonym.
- `Tensor/Spherical`: spherical/deviatoric decomposition.
- `Tensor/Invariants`: `I₁ I₂ I₃`, orthogonal invariance, characteristic polynomial and
  Cayley–Hamilton `A³ − I₁A² + I₂A − I₃I = 0` in dimension three.
- `Tensor/Orthogonal`: `Orth E = unitary (Lin E)`, `Rot E` (`det = 1`), `det Q = ±1`.
- `Tensor/Positive`: continuous functional calculus on real `Lin E` (transferred from
  matrices), `StarOrderedRing`, existence and uniqueness of positive square roots.
- `Tensor/Polar`: polar decomposition `F = RU = VR`, `V = RURᵀ`, uniqueness,
  `det R = 1 ↔ det F > 0`.
- `Tensor/Spectral`: spectral decomposition `S = ∑ λᵢ eᵢ ⊗ eᵢ`; invariants via eigenvalues;
  `S ≥ 0 ↔ λᵢ ≥ 0`.
- `Tensor/Fourth`: `Lin4 E`, minor/major symmetry, `𝕀ˢʸᵐ`, `I ⊗ I`, the isotropic tensor
  `λ I⊗I + 2μ 𝕀ˢʸᵐ` and its symmetries.
- `Tensor/Isotropic4`: reflections; **representation theorem** — every isotropic fourth-order
  tensor equals `λ I⊗I + 2μ 𝕀ˢʸᵐ` on symmetric tensors (any dimension `≥ 2`), and conversely.
- `Tensor/Matrix`: `3 × 3` matrix bridge (`ofMatrix`) with trace/det/transpose/invariant
  lemmas; worked examples (invariants of `diag(1,2,3)`, simple shear).

### Phase 0 — project setup
- Design documents `ARCHITECTURE.md`, `ROADMAP.md` (reviewed).
- Lake project pinned to Lean `v4.34.1` and Mathlib `v4.34.1`.
- CI: build with warnings as errors, sorry/axiom guard
  (`scripts/check_no_sorry_axiom.sh`), doc-gen4 documentation published to
  GitHub Pages from `main`.
- `ContinuumMechanics/Basic/Notation.lean`: scoped transpose notation `Aᵀ`.
