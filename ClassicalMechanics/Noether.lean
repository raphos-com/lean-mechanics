import ClassicalMechanics.Vector
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Lagrangian systems with `n` degrees of freedom and Noether's theorem

A Lagrangian `L(q, v)` on `ℝⁿ × ℝⁿ` with gradients `∂L/∂q = L_q`, `∂L/∂v = L_v`, and a motion `q(t)`
with velocity `v = q̇` and acceleration `a = v̇`. The **Euler–Lagrange equations** read
`d/dt L_v(q, q̇) = L_q(q, q̇)` ([Arnold1989], §§12–20).

* **Energy** (`energy_const`): for a time-independent Lagrangian, `H = q̇ · L_v - L` is conserved.
* **Noether's theorem** (`noether`): if the vector field `ξ(q)` generates a symmetry of `L`
  (infinitesimal invariance `L_q · ξ(q) + L_v · Dξ(q) v = 0`), the **Noether charge**
  `J = L_v · ξ(q)` is conserved along every solution.
* **Translations** (`momentum_const`): if `L` is invariant under translations along `e`, the
  momentum `L_v · e` is conserved.
* **Rotations** (`angular_const`): if `L` is invariant under the infinitesimal linear
  transformations `ξ(q) = A q` (e.g. rotations, `A` skew), the charge `L_v · A q` is conserved;
  for `L = ½ m |v|² - U(|q|)` in the plane this is the angular momentum.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§12–20.
* [Noether1918] E. Noether, *Invariante Variationsprobleme*, Nachr. Ges. Wiss. Göttingen (1918).
-/

open Matrix

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

/-- Product rule for the dot product in `ℝⁿ`. -/
theorem hasDerivAt_dotN {f g : ℝ → Fin n → ℝ} {f' g' : Fin n → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hf' i).mul (hg' i)
  convert this using 1
  · ext s; simp [dotProduct]
  · simp [dotProduct, Finset.sum_add_distrib]

/-- The linear form `w ↦ c · w`. -/
def dotCLM (c : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ c)

@[simp] theorem dotCLM_apply (c w : Fin n → ℝ) : dotCLM c w = c ⬝ᵥ w := by
  simp [dotCLM]

/-- A Lagrangian on `ℝⁿ × ℝⁿ` with its gradients. -/
structure LagrangianN (n : ℕ) where
  L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  Lq : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
  Lv : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
  hasFDerivAt : ∀ q v, HasFDerivAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) => L p.1 p.2)
    ((dotCLM (Lq q v)).comp (ContinuousLinearMap.fst ℝ _ _) +
      (dotCLM (Lv q v)).comp (ContinuousLinearMap.snd ℝ _ _)) (q, v)

/-- A motion in `ℝⁿ`. -/
structure MotionN (n : ℕ) where
  q : ℝ → Fin n → ℝ
  v : ℝ → Fin n → ℝ
  a : ℝ → Fin n → ℝ
  hasDerivAt_q : ∀ t, HasDerivAt q (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t

namespace LagrangianN

variable (𝓛 : LagrangianN n) (γ : MotionN n)

/-- Chain rule: `d/dt L(q, q̇) = L_q · q̇ + L_v · q̈`. -/
theorem hasDerivAt_lagrangian (t : ℝ) :
    HasDerivAt (fun s => 𝓛.L (γ.q s) (γ.v s))
      (𝓛.Lq (γ.q t) (γ.v t) ⬝ᵥ γ.v t + 𝓛.Lv (γ.q t) (γ.v t) ⬝ᵥ γ.a t) t := by
  have h := (𝓛.hasFDerivAt (γ.q t) (γ.v t)).comp_hasDerivAt t
    ((γ.hasDerivAt_q t).prodMk (γ.hasDerivAt_v t))
  convert h using 1
  · rfl
  simp

/-- The **Euler–Lagrange equations** `d/dt L_v(q, q̇) = L_q(q, q̇)`. -/
def EulerLagrange : Prop :=
  ∀ t, HasDerivAt (fun s => 𝓛.Lv (γ.q s) (γ.v s)) (𝓛.Lq (γ.q t) (γ.v t)) t

/-- The energy `H = q̇ · L_v - L`. -/
def energy (t : ℝ) : ℝ := γ.v t ⬝ᵥ 𝓛.Lv (γ.q t) (γ.v t) - 𝓛.L (γ.q t) (γ.v t)

/-- **Conservation of energy** for a time-independent Lagrangian. -/
theorem energy_const (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) : 𝓛.energy γ s = 𝓛.energy γ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := (hasDerivAt_dotN (γ.hasDerivAt_v t) (hEL t)).sub (𝓛.hasDerivAt_lagrangian γ t)
  convert h using 1
  · funext s; rfl
  rw [dotProduct_comm (γ.a t), dotProduct_comm (γ.v t) (𝓛.Lq _ _)]
  ring

/-- An **infinitesimal symmetry** of `L`: a vector field `ξ` with derivative `Dξ` such that
`L_q · ξ(q) + L_v · Dξ(q) v = 0` for all `q, v`. -/
structure Symmetry (𝓛 : LagrangianN n) where
  ξ : (Fin n → ℝ) → Fin n → ℝ
  Dξ : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] Fin n → ℝ
  hasFDerivAt : ∀ q, HasFDerivAt ξ (Dξ q) q
  invariant : ∀ q v, 𝓛.Lq q v ⬝ᵥ ξ q + 𝓛.Lv q v ⬝ᵥ Dξ q v = 0

/-- **Noether's theorem**: the charge `J = L_v · ξ(q)` of an infinitesimal symmetry is conserved
along every solution of the Euler–Lagrange equations. -/
theorem noether (S : Symmetry 𝓛) (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) :
    𝓛.Lv (γ.q s) (γ.v s) ⬝ᵥ S.ξ (γ.q s) = 𝓛.Lv (γ.q t) (γ.v t) ⬝ᵥ S.ξ (γ.q t) := by
  refine eq_of_hasDerivAt_zero (F := fun s => 𝓛.Lv (γ.q s) (γ.v s) ⬝ᵥ S.ξ (γ.q s))
    (fun t => ?_) s t
  have hξ := (S.hasFDerivAt (γ.q t)).comp_hasDerivAt t (γ.hasDerivAt_q t)
  have h := hasDerivAt_dotN (hEL t) hξ
  rw [Function.comp_apply, S.invariant] at h
  exact h

/-- **Translation invariance**: if `L_q · e = 0` everywhere, the momentum `L_v · e` is
conserved. -/
theorem momentum_const (e : Fin n → ℝ) (he : ∀ q v, 𝓛.Lq q v ⬝ᵥ e = 0)
    (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) :
    𝓛.Lv (γ.q s) (γ.v s) ⬝ᵥ e = 𝓛.Lv (γ.q t) (γ.v t) ⬝ᵥ e :=
  𝓛.noether γ ⟨fun _ => e, fun _ => 0, fun _ => hasFDerivAt_const e _,
    fun q v => by simp [he q v]⟩ hEL s t

/-- **Linear symmetries**: if `L_q · A q + L_v · A v = 0` everywhere (e.g. invariance under the
rotations generated by a skew matrix `A`), the charge `L_v · A q` is conserved. -/
theorem angular_const (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ q v, 𝓛.Lq q v ⬝ᵥ A *ᵥ q + 𝓛.Lv q v ⬝ᵥ A *ᵥ v = 0) (hEL : 𝓛.EulerLagrange γ)
    (s t : ℝ) :
    𝓛.Lv (γ.q s) (γ.v s) ⬝ᵥ A *ᵥ γ.q s = 𝓛.Lv (γ.q t) (γ.v t) ⬝ᵥ A *ᵥ γ.q t := by
  let T : (Fin n → ℝ) →L[ℝ] Fin n → ℝ := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  have hT : ∀ v, T v = A *ᵥ v := fun v => by simp [T]
  have hT' : (fun q => A *ᵥ q) = ⇑T := funext fun q => (hT q).symm
  exact 𝓛.noether γ ⟨fun q => A *ᵥ q, fun _ => T, fun q => hT' ▸ T.hasFDerivAt,
    fun q v => by rw [hT]; exact hA q v⟩ hEL s t

end LagrangianN

end ClassicalMechanics
