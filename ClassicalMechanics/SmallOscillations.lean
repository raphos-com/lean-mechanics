import ClassicalMechanics.Noether
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Small oscillations

Linearizing a natural system about a stable equilibrium gives

`M q̈ + K q = 0`

with a symmetric positive definite **mass matrix** `M` and a symmetric **stiffness matrix** `K`
([Arnold1989], §23; [Goldstein2002], §6.2).

* **Energy** (`energy_const`): `½ q̇ · M q̇ + ½ q · K q` is conserved.
* **Normal modes** (`mode_solves`): if `K φ = ω² M φ`, then `q(t) = cos(ωt) φ` (and
  `sin(ωt) φ`) is a motion; solutions superpose (`superpose`).
* **Rayleigh quotient** (`rayleigh`): `ω² = (φ · K φ)/(φ · M φ)`; hence if `K` is positive
  definite every eigenfrequency is real, `ω² > 0` (`omega_sq_pos`): the equilibrium is stable.
* **Orthogonality of modes** (`modes_orthogonal`): modes with distinct frequencies are
  `M`- and `K`-orthogonal.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §23.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §6.2.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

/-- `x · A y = Aᵀ x · y`, so `x · A y = y · A x` for symmetric `A`. -/
theorem dot_mulVec_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

theorem hasDerivAt_mulVec (A : Matrix (Fin n) (Fin n) ℝ) {f : ℝ → Fin n → ℝ} {f' : Fin n → ℝ}
    {t : ℝ} (hf : HasDerivAt f f' t) : HasDerivAt (fun s => A *ᵥ f s) (A *ᵥ f') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 hf j).const_mul (A i j)
  convert h using 1
  · funext s; simp [mulVec, dotProduct]
  · simp [mulVec, dotProduct]

/-- A linear system `M q̈ + K q = 0` with symmetric `M`, `K` and positive definite `M`. -/
structure SmallOscillations (n : ℕ) where
  M : Matrix (Fin n) (Fin n) ℝ
  K : Matrix (Fin n) (Fin n) ℝ
  M_symm : Mᵀ = M
  K_symm : Kᵀ = K
  M_posDef : M.PosDef

namespace SmallOscillations

variable (S : SmallOscillations n)

/-- A motion: `M q̈ + K q = 0`. -/
def IsMotion (γ : MotionN n) : Prop := ∀ t, S.M *ᵥ γ.a t + S.K *ᵥ γ.q t = 0

/-- The energy `½ q̇ · M q̇ + ½ q · K q`. -/
def energy (γ : MotionN n) (t : ℝ) : ℝ :=
  (γ.v t ⬝ᵥ S.M *ᵥ γ.v t) / 2 + (γ.q t ⬝ᵥ S.K *ᵥ γ.q t) / 2

/-- **Conservation of energy**. -/
theorem energy_const {γ : MotionN n} (h : S.IsMotion γ) (s t : ℝ) :
    S.energy γ s = S.energy γ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h1 := hasDerivAt_dotN (γ.hasDerivAt_v t) (hasDerivAt_mulVec S.M (γ.hasDerivAt_v t))
  have h2 := hasDerivAt_dotN (γ.hasDerivAt_q t) (hasDerivAt_mulVec S.K (γ.hasDerivAt_q t))
  convert (h1.div_const 2).add (h2.div_const 2) using 1
  · funext x; rfl
  rw [dot_mulVec_comm S.M_symm (γ.a t), dot_mulVec_comm S.K_symm (γ.q t) (γ.v t)]
  have e : γ.v t ⬝ᵥ (S.M *ᵥ γ.a t + S.K *ᵥ γ.q t) = 0 := by rw [h t, dotProduct_zero]
  rw [dotProduct_add] at e
  linarith

/-- **Superposition**: the equation of motion is linear. -/
theorem superpose {q₁ a₁ q₂ a₂ : Fin n → ℝ} (h₁ : S.M *ᵥ a₁ + S.K *ᵥ q₁ = 0)
    (h₂ : S.M *ᵥ a₂ + S.K *ᵥ q₂ = 0) (c₁ c₂ : ℝ) :
    S.M *ᵥ (c₁ • a₁ + c₂ • a₂) + S.K *ᵥ (c₁ • q₁ + c₂ • q₂) = 0 := by
  rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul]
  calc c₁ • S.M *ᵥ a₁ + c₂ • S.M *ᵥ a₂ + (c₁ • S.K *ᵥ q₁ + c₂ • S.K *ᵥ q₂)
      = c₁ • (S.M *ᵥ a₁ + S.K *ᵥ q₁) + c₂ • (S.M *ᵥ a₂ + S.K *ᵥ q₂) := by
        simp only [smul_add]; abel
    _ = 0 := by rw [h₁, h₂, smul_zero, smul_zero, add_zero]

/-- A **normal mode**: `K φ = ω² M φ`. -/
def IsMode (ω : ℝ) (φ : Fin n → ℝ) : Prop := S.K *ᵥ φ = ω ^ 2 • S.M *ᵥ φ

/-- The motion `q(t) = cos(ωt) φ` of a normal mode. -/
def modeMotion (ω : ℝ) (φ : Fin n → ℝ) : MotionN n where
  q t := cos (ω * t) • φ
  v t := (-(ω * sin (ω * t))) • φ
  a t := (-(ω ^ 2 * cos (ω * t))) • φ
  hasDerivAt_q t := by
    have hs : HasDerivAt (fun s => cos (ω * s)) (-(ω * sin (ω * t))) t := by
      have := ((hasDerivAt_id' t).const_mul ω).cos
      convert this using 1
      ring
    exact hs.smul_const φ
  hasDerivAt_v t := by
    have hs : HasDerivAt (fun s => -(ω * sin (ω * s))) (-(ω ^ 2 * cos (ω * t))) t := by
      have := (((hasDerivAt_id' t).const_mul ω).sin.const_mul ω).neg
      convert this using 1
      ring
    exact hs.smul_const φ

/-- A normal mode oscillates: `q(t) = cos(ωt) φ` is a motion. -/
theorem mode_solves {ω : ℝ} {φ : Fin n → ℝ} (h : S.IsMode ω φ) :
    S.IsMotion (modeMotion ω φ) := by
  intro t
  have h' : S.K *ᵥ φ = ω ^ 2 • S.M *ᵥ φ := h
  simp only [modeMotion, mulVec_smul, h', smul_smul]
  rw [← add_smul]
  convert zero_smul ℝ (S.M *ᵥ φ) using 2
  ring

theorem dot_M_pos {φ : Fin n → ℝ} (hφ : φ ≠ 0) : 0 < φ ⬝ᵥ S.M *ᵥ φ := by
  simpa using S.M_posDef.dotProduct_mulVec_pos hφ

/-- **Rayleigh quotient**: `ω² = (φ · K φ)/(φ · M φ)`. -/
theorem rayleigh {ω : ℝ} {φ : Fin n → ℝ} (h : S.IsMode ω φ) (hφ : φ ≠ 0) :
    ω ^ 2 = (φ ⬝ᵥ S.K *ᵥ φ) / (φ ⬝ᵥ S.M *ᵥ φ) := by
  rw [h, dotProduct_smul, smul_eq_mul, mul_div_assoc, div_self (S.dot_M_pos hφ).ne', mul_one]

/-- **Stability**: if `K` is positive definite, every mode has `ω² > 0`. -/
theorem omega_sq_pos (hK : S.K.PosDef) {ω : ℝ} {φ : Fin n → ℝ} (h : S.IsMode ω φ)
    (hφ : φ ≠ 0) : 0 < ω ^ 2 := by
  rw [S.rayleigh h hφ]
  exact div_pos (by simpa using hK.dotProduct_mulVec_pos hφ) (S.dot_M_pos hφ)

/-- **Orthogonality of normal modes**: modes with different frequencies are `M`-orthogonal and
`K`-orthogonal. -/
theorem modes_orthogonal {ω₁ ω₂ : ℝ} {φ₁ φ₂ : Fin n → ℝ} (h₁ : S.IsMode ω₁ φ₁)
    (h₂ : S.IsMode ω₂ φ₂) (hω : ω₁ ^ 2 ≠ ω₂ ^ 2) :
    φ₁ ⬝ᵥ S.M *ᵥ φ₂ = 0 ∧ φ₁ ⬝ᵥ S.K *ᵥ φ₂ = 0 := by
  have e1 : φ₁ ⬝ᵥ S.K *ᵥ φ₂ = ω₂ ^ 2 * (φ₁ ⬝ᵥ S.M *ᵥ φ₂) := by
    rw [h₂, dotProduct_smul, smul_eq_mul]
  have e2 : φ₁ ⬝ᵥ S.K *ᵥ φ₂ = ω₁ ^ 2 * (φ₁ ⬝ᵥ S.M *ᵥ φ₂) := by
    rw [dot_mulVec_comm S.K_symm, h₁, dotProduct_smul, smul_eq_mul, dot_mulVec_comm S.M_symm]
  have hM : φ₁ ⬝ᵥ S.M *ᵥ φ₂ = 0 := by
    have : (ω₁ ^ 2 - ω₂ ^ 2) * (φ₁ ⬝ᵥ S.M *ᵥ φ₂) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω)
  exact ⟨hM, by rw [e1, hM, mul_zero]⟩

/-- **Existence of a complete set of normal modes** (unit mass matrix): if `M = I` and `K` is
positive semidefinite, there are `n` orthonormal modes `K φⱼ = ωⱼ² φⱼ` (spectral theorem). -/
theorem exists_modes (hM : S.M = 1) (hK : S.K.PosSemidef) :
    ∃ (φ : Fin n → Fin n → ℝ) (ω : Fin n → ℝ),
      (∀ i j, φ i ⬝ᵥ φ j = if i = j then 1 else 0) ∧ ∀ j, S.IsMode (ω j) (φ j) := by
  let b := hK.1.eigenvectorBasis
  refine ⟨fun j => ⇑(b j), fun j => √(hK.1.eigenvalues j), fun i j => ?_, fun j => ?_⟩
  · have h := b.inner_eq_ite i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct_comm] using h
  · change S.K *ᵥ ⇑(b j) = _ • S.M *ᵥ ⇑(b j)
    rw [hK.1.mulVec_eigenvectorBasis j, hM, one_mulVec, Real.sq_sqrt (hK.eigenvalues_nonneg j)]

end SmallOscillations

end ClassicalMechanics
