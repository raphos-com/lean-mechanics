import ClassicalMechanics.Particles
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Galilean invariance of systems of particles

The **Galilean group** acts on the motions of a system of particles by boosts, translations,
rotations and time shifts. Newton's law `mᵢ aᵢ = Σⱼ Fᵢⱼ + Fᵢᵉ` is invariant under these
transformations, provided the forces transform covariantly ([Arnold1989], §§1–2;
[Goldstein2002], §1.2; [LandauLifshitz1976], §§3–4).

* **Boosts** (`ParticleSystem.boost`): `x'ᵢ(t) = xᵢ(t) + t w + c` with constant `w`, `c`. The
  accelerations are unchanged, as are relative positions and velocities (`boost_relPos`,
  `boost_relVel`), so forces depending only on them are unchanged and the transformed motion
  is again a `ParticleSystem` with the **same forces**.
* **Transformation laws** (`boost_momentum`, `boost_kinetic`, `boost_centerOfMass`):
  `P' = P + M w`, `T' = T + P · w + ½ M |w|²`, `x'_G = x_G + t w + c`.
* **Rotations and time shifts** (`ParticleSystem.rotate`, `ParticleSystem.timeShift`,
  `ParticleSystem.galilean`): for a constant matrix `A`, `x'ᵢ = A xᵢ` with forces `A Fᵢⱼ`,
  `A Fᵢᵉ`; for orthogonal `A` the kinetic energy is invariant (`rotate_kinetic`).
* **Boost charge** (`boostCharge_conserved`, `centerOfMass_uniform`): for an isolated system the
  Noether charge of boosts `K(t) = M x_G(t) - t P` is conserved, i.e. the centre of mass moves
  uniformly, `x_G(t) = x_G(0) + t P / M`. Under a boost, `K' = K + M c` (`boost_boostCharge`).

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§1–2.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §1.2.
* [LandauLifshitz1976] L. D. Landau, E. M. Lifshitz, *Mechanics*, 3rd ed., §§3–4, 8.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

namespace ParticleSystem

variable {ι : Type*} [Fintype ι] (S : ParticleSystem ι)

/-! ### Boosts -/

/-- The **Galilean boost** `x'ᵢ(t) = xᵢ(t) + t w + c` of a system of particles, with the same
masses and the same forces. -/
def boost (w c : Vec) : ParticleSystem ι where
  m := S.m
  x t i := S.x t i + t • w + c
  v t i := S.v t i + w
  a := S.a
  F := S.F
  Fe := S.Fe
  hasDerivAt_x t i := by
    have h := ((S.hasDerivAt_x t i).add ((hasDerivAt_id t).smul_const w)).add_const c
    simpa using h
  hasDerivAt_v t i := by simpa using (S.hasDerivAt_v t i).add_const w
  newton := S.newton
  reaction := S.reaction

variable (w c : Vec)

@[simp] theorem boost_m : (S.boost w c).m = S.m := rfl

@[simp] theorem boost_x (t : ℝ) (i : ι) : (S.boost w c).x t i = S.x t i + t • w + c := rfl

@[simp] theorem boost_v (t : ℝ) (i : ι) : (S.boost w c).v t i = S.v t i + w := rfl

@[simp] theorem boost_a : (S.boost w c).a = S.a := rfl

@[simp] theorem boost_F : (S.boost w c).F = S.F := rfl

@[simp] theorem boost_Fe : (S.boost w c).Fe = S.Fe := rfl

/-- Relative positions are invariant under boosts. -/
theorem boost_relPos (t : ℝ) (i j : ι) :
    (S.boost w c).x t i - (S.boost w c).x t j = S.x t i - S.x t j := by
  simp only [boost_x]; abel

/-- Relative velocities are invariant under boosts. -/
theorem boost_relVel (t : ℝ) (i j : ι) :
    (S.boost w c).v t i - (S.boost w c).v t j = S.v t i - S.v t j := by
  simp only [boost_v]; abel

/-- The total mass is invariant under boosts. -/
@[simp] theorem boost_mass : (S.boost w c).mass = S.mass := rfl

/-- The total external force is invariant under boosts. -/
@[simp] theorem boost_externalForce (t : ℝ) :
    (S.boost w c).externalForce t = S.externalForce t := rfl

/-- **Transformation of momentum** under a boost: `P' = P + M w`. -/
theorem boost_momentum (t : ℝ) :
    (S.boost w c).momentum t = S.momentum t + S.mass • w := by
  simp only [momentum, mass, boost_m, boost_v, smul_add, Finset.sum_add_distrib, Finset.sum_smul]

/-- Transformation of the mass moment under a boost: `Σ mᵢ x'ᵢ = Σ mᵢ xᵢ + M (t w + c)`. -/
theorem boost_massMoment (t : ℝ) :
    (S.boost w c).massMoment t = S.massMoment t + S.mass • (t • w + c) := by
  simp only [massMoment, mass, boost_m, boost_x, add_assoc, smul_add, Finset.sum_add_distrib,
    Finset.sum_smul]

/-- Transformation of the centre of mass under a boost: `x'_G = x_G + t w + c`. -/
theorem boost_centerOfMass (hM : S.mass ≠ 0) (t : ℝ) :
    (S.boost w c).centerOfMass t = S.centerOfMass t + (t • w + c) := by
  simp only [centerOfMass, boost_mass, boost_massMoment, smul_add, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- **Transformation of kinetic energy** under a boost: `T' = T + P · w + ½ M |w|²`. -/
theorem boost_kinetic (t : ℝ) :
    (S.boost w c).kinetic t = S.kinetic t + S.momentum t ⬝ᵥ w + S.mass / 2 * normSq w := by
  simp only [kinetic, momentum, mass, boost_m, boost_v, normSq, sum_dotProduct, smul_dotProduct,
    smul_eq_mul]
  rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm w (S.v t i)]
  ring

/-! ### Rotations and time shifts -/

/-- The system seen in a frame rotated by the constant matrix `A`: `x'ᵢ = A xᵢ`, with the forces
transformed covariantly, `F' = A F`. -/
def rotate (A : Matrix (Fin 3) (Fin 3) ℝ) : ParticleSystem ι where
  m := S.m
  x t i := A *ᵥ S.x t i
  v t i := A *ᵥ S.v t i
  a t i := A *ᵥ S.a t i
  F t i j := A *ᵥ S.F t i j
  Fe t i := A *ᵥ S.Fe t i
  hasDerivAt_x t i := by
    have h := (Matrix.toLin' A).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (S.hasDerivAt_x t i)
    convert h using 1 <;> simp [funext_iff]
  hasDerivAt_v t i := by
    have h := (Matrix.toLin' A).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (S.hasDerivAt_v t i)
    convert h using 1 <;> simp [funext_iff]
  newton t i := by
    rw [← mulVec_smul, S.newton, mulVec_add, mulVec_sum]
  reaction t i j := by rw [S.reaction, mulVec_neg]

/-- The time-shifted system `x'ᵢ(t) = xᵢ(t + τ)`, with forces `F'(t) = F(t + τ)`. -/
def timeShift (τ : ℝ) : ParticleSystem ι where
  m := S.m
  x t := S.x (t + τ)
  v t := S.v (t + τ)
  a t := S.a (t + τ)
  F t := S.F (t + τ)
  Fe t := S.Fe (t + τ)
  hasDerivAt_x t i := by
    have h := (S.hasDerivAt_x (t + τ) i).scomp t ((hasDerivAt_id t).add_const τ)
    convert h using 1
    · rfl
    · simp
  hasDerivAt_v t i := by
    have h := (S.hasDerivAt_v (t + τ) i).scomp t ((hasDerivAt_id t).add_const τ)
    convert h using 1
    · rfl
    · simp
  newton t := S.newton (t + τ)
  reaction t := S.reaction (t + τ)

/-- A general **Galilean transformation**: time shift by `τ`, rotation by `A`, then boost by
velocity `w` and translation by `c`. The result is again a system of particles obeying Newton's
law. -/
def galilean (τ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (w c : Vec) : ParticleSystem ι :=
  ((S.timeShift τ).rotate A).boost w c

/-- The positions after a general Galilean transformation: `x'ᵢ(t) = A xᵢ(t + τ) + t w + c`. -/
theorem galilean_x (τ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (i : ι) :
    (S.galilean τ A w c).x t i = A *ᵥ S.x (t + τ) i + t • w + c := rfl

/-- Momentum transforms covariantly under rotations: `P' = A P`. -/
theorem rotate_momentum (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (S.rotate A).momentum t = A *ᵥ S.momentum t := by
  simp only [momentum, rotate, mulVec_sum, mulVec_smul]

/-- An orthogonal matrix preserves `|v|²`. -/
theorem normSq_mulVec {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (v : Vec) :
    normSq (A *ᵥ v) = normSq v := by
  rw [normSq, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec,
    dotProduct_comm, normSq]

/-- The kinetic energy is invariant under orthogonal transformations. -/
theorem rotate_kinetic {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (t : ℝ) :
    (S.rotate A).kinetic t = S.kinetic t := by
  simp only [kinetic, rotate, normSq_mulVec hA]

/-! ### The boost charge and the motion of the centre of mass -/

/-- The **boost charge** `K(t) = M x_G(t) - t P(t) = Σ mᵢ xᵢ - t P`, the Noether charge
associated with Galilean boosts. -/
def boostCharge (t : ℝ) : Vec := S.massMoment t - t • S.momentum t

/-- `K̇ = -t Σ Fᵢᵉ`. -/
theorem hasDerivAt_boostCharge (t : ℝ) :
    HasDerivAt S.boostCharge (-(t • S.externalForce t)) t := by
  have h := (S.hasDerivAt_massMoment t).sub ((hasDerivAt_id t).smul (S.hasDerivAt_momentum t))
  convert h using 1
  · rfl
  · simp only [id, one_smul]; abel

/-- **Conservation of the boost charge** for an isolated system: `M x_G(t) - t P` is constant. -/
theorem boostCharge_conserved (h : ∀ t, S.externalForce t = 0) (s t : ℝ) :
    S.boostCharge s = S.boostCharge t :=
  eq_of_hasDerivAt_zero (fun t => by simpa [h t] using S.hasDerivAt_boostCharge t) s t

/-- Transformation of the boost charge under a boost: `K' = K + M c`. -/
theorem boost_boostCharge (t : ℝ) :
    (S.boost w c).boostCharge t = S.boostCharge t + S.mass • c := by
  simp only [boostCharge, boost_massMoment, boost_momentum, smul_add, smul_comm t S.mass w]
  abel

/-- **Uniform motion of the centre of mass** of an isolated system:
`x_G(t) = x_G(0) + t P(0) / M`. -/
theorem centerOfMass_uniform (h : ∀ t, S.externalForce t = 0) (t : ℝ) :
    S.centerOfMass t = S.centerOfMass 0 + t • (S.mass⁻¹ • S.momentum 0) := by
  have hK := S.boostCharge_conserved h t 0
  have hP := S.momentum_conserved h t 0
  simp only [boostCharge, zero_smul, sub_zero, hP] at hK
  simp only [centerOfMass, ← hK, smul_sub, smul_comm t S.mass⁻¹]
  abel

end ParticleSystem

end ClassicalMechanics
