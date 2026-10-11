import ClassicalMechanics.Vector

/-!
# Systems of particles: the general theorems of dynamics

A system of particles `i : ι` with masses `mᵢ`, trajectories `xᵢ(t)`, velocities `vᵢ = ẋᵢ` and
accelerations `aᵢ = v̇ᵢ` obeys **Newton's second law**

`mᵢ aᵢ = Σⱼ Fᵢⱼ + Fᵢᵉ`

with internal forces `Fᵢⱼ` (exerted on `i` by `j`) satisfying the **law of action and reaction**
`Fⱼᵢ = -Fᵢⱼ`, and external forces `Fᵢᵉ` ([Goldstein2002], §1.2; [Arnold1989], §5).

* **Momentum** (`hasDerivAt_momentum`, `momentum_conserved`): `Ṗ = Σ Fᵢᵉ`, so the total momentum
  `P = Σ mᵢ vᵢ` of an isolated system is conserved: internal forces cancel in pairs
  (`sum_internal`).
* **Centre of mass** (`hasDerivAt_massMoment`, `hasDerivAt_centerOfMass`): `M ẋ_G = P`, so the
  centre of mass moves like a particle of mass `M` acted on by the total external force.
* **Angular momentum** (`hasDerivAt_angMom`, `angMom_conserved`): if the internal forces are
  **central** (`Fᵢⱼ ∥ xᵢ - xⱼ`, the strong law of action and reaction), `L̇ = Σ xᵢ × Fᵢᵉ`, so the
  angular momentum `L = Σ mᵢ xᵢ × vᵢ` of an isolated system is conserved (`internal_torque`).
* **Kinetic energy** (`hasDerivAt_kinetic`, `energy_conserved`): `Ṫ` is the power of all the
  forces; if that power is `-U̇` for a potential energy `U`, then `T + U` is conserved.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §1.2.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §5.
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

/-- A **system of particles** indexed by `ι`, with its motion and the forces acting on it. -/
structure ParticleSystem (ι : Type*) [Fintype ι] where
  /-- Masses. -/
  m : ι → ℝ
  /-- Positions. -/
  x : ℝ → ι → Vec
  /-- Velocities. -/
  v : ℝ → ι → Vec
  /-- Accelerations. -/
  a : ℝ → ι → Vec
  /-- Internal forces: `F t i j` is exerted on `i` by `j`. -/
  F : ℝ → ι → ι → Vec
  /-- External forces. -/
  Fe : ℝ → ι → Vec
  hasDerivAt_x : ∀ t i, HasDerivAt (fun s => x s i) (v t i) t
  hasDerivAt_v : ∀ t i, HasDerivAt (fun s => v s i) (a t i) t
  /-- Newton's second law. -/
  newton : ∀ t i, m i • a t i = ∑ j, F t i j + Fe t i
  /-- The law of action and reaction. -/
  reaction : ∀ t i j, F t j i = -F t i j

namespace ParticleSystem

variable {ι : Type*} [Fintype ι] (S : ParticleSystem ι)

/-- Total momentum `P = Σ mᵢ vᵢ`. -/
def momentum (t : ℝ) : Vec := ∑ i, S.m i • S.v t i

/-- Total external force `Σ Fᵢᵉ`. -/
def externalForce (t : ℝ) : Vec := ∑ i, S.Fe t i

/-- Total mass `M = Σ mᵢ`. -/
def mass : ℝ := ∑ i, S.m i

/-- First mass moment `Σ mᵢ xᵢ = M x_G`. -/
def massMoment (t : ℝ) : Vec := ∑ i, S.m i • S.x t i

/-- Centre of mass `x_G = M⁻¹ Σ mᵢ xᵢ`. -/
def centerOfMass (t : ℝ) : Vec := S.mass⁻¹ • S.massMoment t

/-- Angular momentum about the origin, `L = Σ mᵢ xᵢ × vᵢ`. -/
def angMom (t : ℝ) : Vec := ∑ i, S.m i • (S.x t i ⨯₃ S.v t i)

/-- Torque of the external forces about the origin, `Σ xᵢ × Fᵢᵉ`. -/
def externalTorque (t : ℝ) : Vec := ∑ i, S.x t i ⨯₃ S.Fe t i

/-- Kinetic energy `T = Σ ½ mᵢ |vᵢ|²`. -/
def kinetic (t : ℝ) : ℝ := ∑ i, S.m i / 2 * normSq (S.v t i)

/-- Power of all the forces, `Σ (Σⱼ Fᵢⱼ + Fᵢᵉ) · vᵢ`. -/
def power (t : ℝ) : ℝ := ∑ i, (∑ j, S.F t i j + S.Fe t i) ⬝ᵥ S.v t i

theorem self_force (t : ℝ) (i : ι) : S.F t i i = 0 := by
  have h := S.reaction t i i
  have : (2 : ℝ) • S.F t i i = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- Internal forces cancel in pairs: `Σᵢⱼ Fᵢⱼ = 0`. -/
theorem sum_internal (t : ℝ) : ∑ i, ∑ j, S.F t i j = 0 := by
  have h : ∑ i, ∑ j, S.F t i j = -∑ i, ∑ j, S.F t i j := by
    calc ∑ i, ∑ j, S.F t i j = ∑ j, ∑ i, S.F t i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -S.F t j i :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => S.reaction t j i
      _ = -∑ i, ∑ j, S.F t i j := by simp only [Finset.sum_neg_distrib]
  have : (2 : ℝ) • ∑ i, ∑ j, S.F t i j = 0 := by rw [two_smul]; nth_rewrite 1 [h]; simp
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- `Σ mᵢ aᵢ = Σ Fᵢᵉ`. -/
theorem sum_mass_accel (t : ℝ) : ∑ i, S.m i • S.a t i = S.externalForce t := by
  simp only [S.newton, Finset.sum_add_distrib, S.sum_internal, zero_add, externalForce]

/-- **Momentum theorem**: `Ṗ = Σ Fᵢᵉ`. -/
theorem hasDerivAt_momentum (t : ℝ) : HasDerivAt S.momentum (S.externalForce t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (S.hasDerivAt_v t i).const_smul (S.m i)
  rw [S.sum_mass_accel] at h
  exact h

/-- **Conservation of momentum** for an isolated system. -/
theorem momentum_conserved (h : ∀ t, S.externalForce t = 0) (s t : ℝ) :
    S.momentum s = S.momentum t :=
  eq_of_hasDerivAt_zero (fun t => h t ▸ S.hasDerivAt_momentum t) s t

/-- `d/dt Σ mᵢ xᵢ = P`. -/
theorem hasDerivAt_massMoment (t : ℝ) : HasDerivAt S.massMoment (S.momentum t) t :=
  HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (S.hasDerivAt_x t i).const_smul (S.m i)

/-- **Centre of mass theorem**: `ẋ_G = P / M` and `M ẍ_G = Σ Fᵢᵉ`: the centre of mass moves like a
particle of mass `M` carrying the total external force. -/
theorem hasDerivAt_centerOfMass (t : ℝ) :
    HasDerivAt S.centerOfMass (S.mass⁻¹ • S.momentum t) t ∧
      HasDerivAt (fun s => S.mass⁻¹ • S.momentum s) (S.mass⁻¹ • S.externalForce t) t :=
  ⟨(S.hasDerivAt_massMoment t).const_smul S.mass⁻¹,
    (S.hasDerivAt_momentum t).const_smul S.mass⁻¹⟩

/-- The internal forces are **central**: `Fᵢⱼ` is parallel to `xᵢ - xⱼ` (strong law of action
and reaction). -/
def IsCentral : Prop := ∀ t i j, (S.x t i - S.x t j) ⨯₃ S.F t i j = 0

/-- Central internal forces have zero total torque: `Σᵢⱼ xᵢ × Fᵢⱼ = 0`. -/
theorem internal_torque (hc : S.IsCentral) (t : ℝ) : ∑ i, ∑ j, S.x t i ⨯₃ S.F t i j = 0 := by
  set A := ∑ i, ∑ j, S.x t i ⨯₃ S.F t i j
  set B := ∑ i, ∑ j, S.x t j ⨯₃ S.F t i j
  have hAB : A = -B := by
    calc A = ∑ j, ∑ i, S.x t i ⨯₃ S.F t i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(S.x t i ⨯₃ S.F t j i) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
            rw [S.reaction t j i, map_neg]
      _ = -B := by simp only [B, Finset.sum_neg_distrib]
  have hsub : A - B = 0 := by
    have : ∀ i j, S.x t i ⨯₃ S.F t i j - S.x t j ⨯₃ S.F t i j = 0 := fun i j => by
      rw [← LinearMap.sub_apply, ← map_sub, hc t i j]
    simp only [A, B, ← Finset.sum_sub_distrib, this, Finset.sum_const_zero]
  have : (2 : ℝ) • A = 0 := by
    rw [two_smul]
    calc A + A = A - B := by rw [sub_eq_add_neg, ← hAB]
      _ = 0 := hsub
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- **Angular momentum theorem**: with central internal forces, `L̇ = Σ xᵢ × Fᵢᵉ`. -/
theorem hasDerivAt_angMom (hc : S.IsCentral) (t : ℝ) :
    HasDerivAt S.angMom (S.externalTorque t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_cross (S.hasDerivAt_x t i) (S.hasDerivAt_v t i)).const_smul (S.m i)
  have e : ∀ i, S.m i • (S.v t i ⨯₃ S.v t i + S.x t i ⨯₃ S.a t i) =
      S.x t i ⨯₃ (∑ j, S.F t i j + S.Fe t i) := fun i => by
    rw [cross_self, zero_add, ← S.newton, map_smul]
  have h2 : ∑ i, S.m i • (S.v t i ⨯₃ S.v t i + S.x t i ⨯₃ S.a t i) = S.externalTorque t := by
    rw [Finset.sum_congr rfl fun i _ => e i]
    simp only [map_add, map_sum, Finset.sum_add_distrib, S.internal_torque hc, zero_add,
      externalTorque]
  rw [h2] at h
  exact h

/-- **Conservation of angular momentum** when the external torque vanishes. -/
theorem angMom_conserved (hc : S.IsCentral) (h : ∀ t, S.externalTorque t = 0) (s t : ℝ) :
    S.angMom s = S.angMom t :=
  eq_of_hasDerivAt_zero (fun t => h t ▸ S.hasDerivAt_angMom hc t) s t

/-- **Kinetic energy theorem**: `Ṫ` is the power of all the forces. -/
theorem hasDerivAt_kinetic (t : ℝ) : HasDerivAt S.kinetic (S.power t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_dot (S.hasDerivAt_v t i) (S.hasDerivAt_v t i)).const_mul (S.m i / 2)
  convert h using 1
  · rfl
  unfold power
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← S.newton t i, dotProduct_comm (S.v t i) (S.a t i), smul_dotProduct, smul_eq_mul]
  ring

/-- **Conservation of energy**: if the power of the forces is `-U̇` for a potential energy `U`,
then `T + U` is constant. -/
theorem energy_conserved {U : ℝ → ℝ} (hU : ∀ t, HasDerivAt U (-S.power t) t) (s t : ℝ) :
    S.kinetic s + U s = S.kinetic t + U t := by
  have h : ∀ t, HasDerivAt (fun s => S.kinetic s + U s) 0 t := fun t => by
    have h := (S.hasDerivAt_kinetic t).add (hU t)
    rw [add_neg_cancel] at h
    exact h
  exact eq_of_hasDerivAt_zero h s t

end ParticleSystem

end ClassicalMechanics
