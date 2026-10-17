import ClassicalMechanics.NormalModes
import ClassicalMechanics.Oscillator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Damped structures and modal superposition

A damped multi-degree-of-freedom structure obeys

`M q̈ + C q̇ + K q = f(t)`

with symmetric mass, damping and stiffness matrices, `M` positive definite and `C`, `K` positive
semidefinite ([Rayleigh1877], §97; [CaugheyOKelly1965]; [Chopra2017], Ch. 10–13).

* **Energy dissipation** (`DampedStructure.hasDerivAt_energy`): the energy
  `E = ½ q̇ᵀMq̇ + ½ qᵀKq` satisfies `Ė = -q̇ᵀCq̇ + q̇ᵀf ≤ q̇ᵀf` (`deriv_energy_le`); free motion
  has non-increasing energy (`energy_antitone`).
* **Modal coordinates** (`ModalBasis`, `exists_modalBasis`): a mode matrix `Φ` with
  `ΦᵀMΦ = I`, `ΦᵀKΦ = diag(ωⱼ²)` (`ModalBasis.stiffness`). Since `Φ⁻¹ = ΦᵀM`, every motion is
  `q = Φη` with `η = ΦᵀMq` (`modal_reconstruct`), and `η` obeys
  `η̈ + ΦᵀCΦ η̇ + diag(ω²) η = Φᵀf` (`modal_eq`); conversely (`of_modal`).
* **Classical damping** (`modal_decoupled`): if `ΦᵀCΦ = diag(2ζⱼωⱼ)`, the equations decouple
  into `n` oscillators `η̈ⱼ + 2ζⱼωⱼη̇ⱼ + ωⱼ²ηⱼ = φⱼᵀf`. Each free modal coordinate is a damped
  oscillator (`modalOscillator`).
* **Rayleigh damping** `C = αM + βK` (`rayleigh_modal`): `ΦᵀCΦ = diag(α + βωⱼ²)`, i.e.
  `ζⱼ = α/(2ωⱼ) + βωⱼ/2` (`rayleigh_zeta`). Two target ratios determine `α, β`
  (`rayleigh_fit`, `rayleigh_fit_unique`); for equal ratios `α = 2ζωᵢωⱼ/(ωᵢ+ωⱼ)`,
  `β = 2ζ/(ωᵢ+ωⱼ)` (`rayleigh_fit_equal`).
* **Caughey criterion**: Rayleigh damping satisfies `CM⁻¹K = KM⁻¹C` (`rayleigh_caughey`); and
  if `CM⁻¹K = KM⁻¹C` and the `ωⱼ²` are distinct, `ΦᵀCΦ` is diagonal (`caughey_diagonal`).
* **Modal superposition** (`free_superposition`, `rayleigh_underdamped_superposition`):
  `q(t) = Σⱼ ηⱼ(t) φⱼ` with each `ηⱼ` a free (e.g. underdamped) modal oscillation solves
  `M q̈ + C q̇ + K q = 0`.

## References

* [Rayleigh1877] J. W. S. Rayleigh, *The Theory of Sound*, Vol. I, §97.
* [CaugheyOKelly1965] T. K. Caughey, M. E. J. O'Kelly, *Classical normal modes in damped linear
  dynamic systems*, J. Appl. Mech. 32 (1965), 583–588.
* [Chopra2017] A. K. Chopra, *Dynamics of Structures*, 5th ed., Ch. 10–13.
-/

open Matrix Real

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

/-- The image `t ↦ A q(t)` of a motion under a constant matrix `A`. -/
def MotionN.mapMatrix (A : Matrix (Fin n) (Fin n) ℝ) (γ : MotionN n) : MotionN n where
  q t := A *ᵥ γ.q t
  v t := A *ᵥ γ.v t
  a t := A *ᵥ γ.a t
  hasDerivAt_q t := hasDerivAt_mulVec A (γ.hasDerivAt_q t)
  hasDerivAt_v t := hasDerivAt_mulVec A (γ.hasDerivAt_v t)

/-- The motion in `ℝⁿ` whose coordinates are the scalar motions `xⱼ` (velocities `vⱼ`,
accelerations `aⱼ`). -/
def MotionN.ofFamily (x v a : Fin n → ℝ → ℝ) (hx : ∀ j t, HasDerivAt (x j) (v j t) t)
    (hv : ∀ j t, HasDerivAt (v j) (a j t) t) : MotionN n where
  q t j := x j t
  v t j := v j t
  a t j := a j t
  hasDerivAt_q t := hasDerivAt_pi.2 fun j => hx j t
  hasDerivAt_v t := hasDerivAt_pi.2 fun j => hv j t

/-- A **damped structure** `M q̈ + C q̇ + K q = f`: symmetric `M`, `C`, `K`, with `M` positive
definite and `C`, `K` positive semidefinite. -/
structure DampedStructure (n : ℕ) extends SmallOscillations n where
  C : Matrix (Fin n) (Fin n) ℝ
  C_symm : Cᵀ = C
  C_posSemidef : C.PosSemidef
  K_posSemidef : K.PosSemidef

namespace DampedStructure

variable (S : DampedStructure n)

/-- A forced motion: `M q̈ + C q̇ + K q = f(t)`. -/
def IsForcedMotion (f : ℝ → Fin n → ℝ) (γ : MotionN n) : Prop :=
  ∀ t, S.M *ᵥ γ.a t + S.C *ᵥ γ.v t + S.K *ᵥ γ.q t = f t

/-- The energy `½ q̇ᵀMq̇ + ½ qᵀKq`. -/
def energy (γ : MotionN n) (t : ℝ) : ℝ := S.toSmallOscillations.energy γ t

/-- The dissipated power `q̇ᵀCq̇` is nonnegative. -/
theorem dissipation_nonneg (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ S.C *ᵥ x := by
  simpa using S.C_posSemidef.dotProduct_mulVec_nonneg x

/-- **Energy balance**: `Ė = -q̇ᵀCq̇ + q̇ᵀf`. -/
theorem hasDerivAt_energy {f : ℝ → Fin n → ℝ} {γ : MotionN n} (h : S.IsForcedMotion f γ)
    (t : ℝ) :
    HasDerivAt (S.energy γ) (-(γ.v t ⬝ᵥ S.C *ᵥ γ.v t) + γ.v t ⬝ᵥ f t) t := by
  have h1 := hasDerivAt_dotN (γ.hasDerivAt_v t) (hasDerivAt_mulVec S.M (γ.hasDerivAt_v t))
  have h2 := hasDerivAt_dotN (γ.hasDerivAt_q t) (hasDerivAt_mulVec S.K (γ.hasDerivAt_q t))
  convert (h1.div_const 2).add (h2.div_const 2) using 1
  · funext x; rfl
  rw [dot_mulVec_comm S.M_symm (γ.a t), dot_mulVec_comm S.K_symm (γ.q t) (γ.v t)]
  have e : γ.v t ⬝ᵥ (S.M *ᵥ γ.a t + S.C *ᵥ γ.v t + S.K *ᵥ γ.q t) = γ.v t ⬝ᵥ f t := by
    rw [h t]
  rw [dotProduct_add, dotProduct_add] at e
  linarith

/-- **Dissipation inequality**: `Ė ≤ q̇ᵀf`, the power of the external force. -/
theorem deriv_energy_le {f : ℝ → Fin n → ℝ} {γ : MotionN n} (h : S.IsForcedMotion f γ)
    (t : ℝ) : deriv (S.energy γ) t ≤ γ.v t ⬝ᵥ f t := by
  rw [(S.hasDerivAt_energy h t).deriv]
  linarith [S.dissipation_nonneg (γ.v t)]

/-- **Free damped motion dissipates energy**: the energy is non-increasing. -/
theorem energy_antitone {γ : MotionN n} (h : S.IsForcedMotion 0 γ) : Antitone (S.energy γ) :=
  antitone_of_deriv_nonpos (fun t => (S.hasDerivAt_energy h t).differentiableAt) fun t => by
    have := S.deriv_energy_le h t
    simpa using this

end DampedStructure

/-- A **modal matrix**: its columns `φⱼ = Φᵀ j` are `M`-orthonormal normal modes,
`ΦᵀMΦ = I` and `K φⱼ = ωⱼ² M φⱼ`. -/
structure ModalBasis (S : SmallOscillations n) where
  Φ : Matrix (Fin n) (Fin n) ℝ
  ω : Fin n → ℝ
  orthonormal : Φᵀ * S.M * Φ = 1
  isMode : ∀ j, S.IsMode (ω j) (Φᵀ j)

/-- **Existence of a modal matrix** for positive semidefinite `K`
(from `SmallOscillations.exists_modes_general`). -/
theorem exists_modalBasis (S : SmallOscillations n) (hK : S.K.PosSemidef) :
    Nonempty (ModalBasis S) := by
  obtain ⟨φ, ω, hon, hmode⟩ := S.exists_modes_general hK
  refine ⟨⟨(Matrix.of φ)ᵀ, ω, ?_, fun j => ?_⟩⟩
  · ext i j
    rw [mul_mul_apply, transpose_transpose, one_apply]
    exact hon i j
  · rw [transpose_transpose]
    exact hmode j

namespace ModalBasis

variable {S : SmallOscillations n} (B : ModalBasis S)

/-- `ΦᵀM` is a left inverse of `Φ`. -/
theorem left_inv : (B.Φᵀ * S.M) * B.Φ = 1 := B.orthonormal

/-- `Φ⁻¹ = ΦᵀM`: also a right inverse. -/
theorem right_inv : B.Φ * (B.Φᵀ * S.M) = 1 := mul_eq_one_comm.mp B.left_inv

/-- `Φᵀ` is invertible, with inverse `MΦ`. -/
theorem transpose_right_inv : (S.M * B.Φ) * B.Φᵀ = 1 := by
  apply mul_eq_one_comm.mp
  rw [← Matrix.mul_assoc]
  exact B.orthonormal

/-- `M⁻¹ = ΦΦᵀ`. -/
theorem M_inv : S.M⁻¹ = B.Φ * B.Φᵀ := by
  apply inv_eq_left_inv
  rw [Matrix.mul_assoc]
  exact B.right_inv

/-- **Reconstruction**: `q = Φ η` with modal coordinates `η = ΦᵀMq`. -/
theorem reconstruct (x : Fin n → ℝ) : B.Φ *ᵥ (B.Φᵀ *ᵥ (S.M *ᵥ x)) = x := by
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, B.right_inv, one_mulVec]

/-- `Φᵀ` is injective. -/
theorem transpose_injective {x y : Fin n → ℝ} (h : B.Φᵀ *ᵥ x = B.Φᵀ *ᵥ y) : x = y := by
  have := congrArg ((S.M * B.Φ) *ᵥ ·) h
  simpa only [mulVec_mulVec, B.transpose_right_inv, one_mulVec] using this

/-- The stiffness in modal coordinates: `ΦᵀKΦ = diag(ωⱼ²)`. -/
theorem stiffness : B.Φᵀ * S.K * B.Φ = diagonal fun j => B.ω j ^ 2 := by
  ext i j
  have hij : B.Φᵀ i ⬝ᵥ S.M *ᵥ B.Φᵀ j = if i = j then 1 else 0 := by
    rw [← mul_mul_apply, B.orthonormal, one_apply]
  rw [mul_mul_apply, B.isMode j, dotProduct_smul, hij, diagonal_apply]
  split_ifs with h
  · subst h; simp
  · simp

/-- `M`-orthonormality of the modes: `φᵢᵀMφⱼ = δᵢⱼ`. -/
theorem mode_orthonormal (i j : Fin n) :
    B.Φᵀ i ⬝ᵥ S.M *ᵥ B.Φᵀ j = if i = j then 1 else 0 := by
  rw [← mul_mul_apply, B.orthonormal, one_apply]

/-- `Φ η = Σⱼ ηⱼ φⱼ`: physical coordinates as a superposition of modes. -/
theorem mulVec_eq_sum (η : Fin n → ℝ) : B.Φ *ᵥ η = ∑ j, η j • B.Φᵀ j := by
  ext i
  simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]

end ModalBasis

namespace DampedStructure

variable (S : DampedStructure n) (B : ModalBasis S.toSmallOscillations)

/-- The **modal coordinates** `η(t) = ΦᵀM q(t)` of a motion. -/
def modal (γ : MotionN n) : MotionN n := γ.mapMatrix (B.Φᵀ * S.M)

/-- The motion is recovered from its modal coordinates: `q = Φ η`. -/
theorem modal_reconstruct (γ : MotionN n) (t : ℝ) : γ.q t = B.Φ *ᵥ (S.modal B γ).q t := by
  simp only [modal, MotionN.mapMatrix, ← mulVec_mulVec, B.reconstruct]

/-- **Modal equations**: if `q` solves `M q̈ + C q̇ + K q = f`, then `η = ΦᵀMq` solves
`η̈ + ΦᵀCΦ η̇ + diag(ω²) η = Φᵀ f`. -/
theorem modal_eq {f : ℝ → Fin n → ℝ} {γ : MotionN n} (h : S.IsForcedMotion f γ) (t : ℝ) :
    (S.modal B γ).a t + (B.Φᵀ * S.C * B.Φ) *ᵥ (S.modal B γ).v t +
      (diagonal fun j => B.ω j ^ 2) *ᵥ (S.modal B γ).q t = B.Φᵀ *ᵥ f t := by
  rw [← B.stiffness, ← h t]
  simp only [modal, MotionN.mapMatrix, ← mulVec_mulVec, B.reconstruct, mulVec_add]

/-- **Converse**: if `η` solves the modal equations, `q = Φη` solves
`M q̈ + C q̇ + K q = f`. -/
theorem of_modal {f : ℝ → Fin n → ℝ} {η : MotionN n}
    (h : ∀ t, η.a t + (B.Φᵀ * S.C * B.Φ) *ᵥ η.v t +
      (diagonal fun j => B.ω j ^ 2) *ᵥ η.q t = B.Φᵀ *ᵥ f t) :
    S.IsForcedMotion f (η.mapMatrix B.Φ) := by
  intro t
  apply B.transpose_injective
  rw [← h t, ← B.stiffness]
  conv_rhs => rw [← one_mulVec (η.a t), ← B.orthonormal]
  simp only [MotionN.mapMatrix, mulVec_add, mulVec_mulVec, Matrix.mul_assoc]

/-- **Decoupling under classical damping**: if `ΦᵀCΦ = diag(2ζⱼωⱼ)`, each modal coordinate
is an independent forced oscillator `η̈ⱼ + 2ζⱼωⱼη̇ⱼ + ωⱼ²ηⱼ = φⱼᵀ f`. -/
theorem modal_decoupled {ζ : Fin n → ℝ}
    (hζ : B.Φᵀ * S.C * B.Φ = diagonal fun j => 2 * ζ j * B.ω j) {f : ℝ → Fin n → ℝ}
    {γ : MotionN n} (h : S.IsForcedMotion f γ) (j : Fin n) (t : ℝ) :
    (S.modal B γ).a t j + 2 * ζ j * B.ω j * (S.modal B γ).v t j +
      B.ω j ^ 2 * (S.modal B γ).q t j = B.Φᵀ j ⬝ᵥ f t := by
  have := congrFun (S.modal_eq B h t) j
  rw [hζ] at this
  simp only [Pi.add_apply, mulVec_diagonal] at this
  exact this

/-- The modal damping coefficients `φⱼᵀCφⱼ` are nonnegative. -/
theorem modal_damping_nonneg (j : Fin n) : 0 ≤ (B.Φᵀ * S.C * B.Φ) j j := by
  rw [mul_mul_apply]
  exact S.dissipation_nonneg _

/-- Under classical damping, each **free** modal coordinate is a damped oscillator
`η̈ⱼ + cⱼ η̇ⱼ + ωⱼ² ηⱼ = 0`, `cⱼ = φⱼᵀCφⱼ` (unit modal mass). -/
def modalOscillator (hdiag : B.Φᵀ * S.C * B.Φ = diagonal fun j => (B.Φᵀ * S.C * B.Φ) j j)
    {γ : MotionN n} (h : S.IsForcedMotion 0 γ) (j : Fin n) (hω : B.ω j ≠ 0) : Damped where
  m := 1
  c := (B.Φᵀ * S.C * B.Φ) j j
  k := B.ω j ^ 2
  m_pos := one_pos
  c_nonneg := S.modal_damping_nonneg B j
  k_pos := by positivity
  x t := (S.modal B γ).q t j
  v t := (S.modal B γ).v t j
  a t := (S.modal B γ).a t j
  hasDerivAt_x t := hasDerivAt_pi.1 ((S.modal B γ).hasDerivAt_q t) j
  hasDerivAt_v t := hasDerivAt_pi.1 ((S.modal B γ).hasDerivAt_v t) j
  eq t := by
    have := congrFun (S.modal_eq B h t) j
    rw [hdiag] at this
    simpa [mulVec_diagonal, add_assoc] using this

/-- Free modal oscillations dissipate their modal energy (`Damped.energy_antitone`). -/
theorem modal_energy_antitone
    (hdiag : B.Φᵀ * S.C * B.Φ = diagonal fun j => (B.Φᵀ * S.C * B.Φ) j j)
    {γ : MotionN n} (h : S.IsForcedMotion 0 γ) (j : Fin n) (hω : B.ω j ≠ 0) :
    Antitone fun t => (S.modal B γ).v t j ^ 2 / 2 + B.ω j ^ 2 / 2 * (S.modal B γ).q t j ^ 2 := by
  have := (S.modalOscillator B hdiag h j hω).energy_antitone
  intro s t hst
  have h' := this hst
  simp only [Damped.energy, modalOscillator] at h'
  simp only
  linarith

/-! ### Rayleigh damping -/

/-- **Rayleigh damping is classical**: `C = αM + βK` gives `ΦᵀCΦ = diag(α + βωⱼ²)`. -/
theorem rayleigh_modal {α β : ℝ} (hC : S.C = α • S.M + β • S.K) :
    B.Φᵀ * S.C * B.Φ = diagonal fun j => α + β * B.ω j ^ 2 := by
  have hK := B.stiffness
  have hM := B.orthonormal
  rw [hC, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, hK, hM]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, one_apply, diagonal_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The **modal damping ratios** of Rayleigh damping: `α + βωⱼ² = 2ζⱼωⱼ` with
`ζⱼ = α/(2ωⱼ) + βωⱼ/2`. -/
theorem rayleigh_zeta {α β : ℝ} (hC : S.C = α • S.M + β • S.K) (hω : ∀ j, B.ω j ≠ 0) :
    B.Φᵀ * S.C * B.Φ =
      diagonal fun j => 2 * (α / (2 * B.ω j) + β * B.ω j / 2) * B.ω j := by
  rw [S.rayleigh_modal B hC]
  congr 1
  funext j
  field_simp [hω j]

/-- **Caughey's condition for Rayleigh damping**: `C M⁻¹ K = K M⁻¹ C`. -/
theorem rayleigh_caughey {α β : ℝ} (hC : S.C = α • S.M + β • S.K) :
    S.C * S.M⁻¹ * S.K = S.K * S.M⁻¹ * S.C := by
  have hdet : IsUnit S.M.det := isUnit_iff_ne_zero.mpr S.M_posDef.det_pos.ne'
  rw [hC]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hdet, nonsing_inv_mul _ hdet,
    Matrix.mul_one]

/-- **Caughey criterion**: if `C M⁻¹ K = K M⁻¹ C` and the squared frequencies are distinct,
then `ΦᵀCΦ` is diagonal, so the damping is classical. -/
theorem caughey_diagonal (hcomm : S.C * S.M⁻¹ * S.K = S.K * S.M⁻¹ * S.C)
    (hω : ∀ i j, i ≠ j → B.ω i ^ 2 ≠ B.ω j ^ 2) :
    B.Φᵀ * S.C * B.Φ = diagonal fun j => (B.Φᵀ * S.C * B.Φ) j j := by
  set Ct := B.Φᵀ * S.C * B.Φ
  have key : Ct * (diagonal fun j => B.ω j ^ 2) = (diagonal fun j => B.ω j ^ 2) * Ct := by
    have e := congrArg (fun X => B.Φᵀ * X * B.Φ) hcomm
    simp only [B.M_inv] at e
    rw [← B.stiffness]
    simp only [Ct, Matrix.mul_assoc] at e ⊢
    exact e
  ext i j
  rw [diagonal_apply]
  split_ifs with h
  · rw [h]
  · have e := congrFun (congrFun key i) j
    rw [mul_diagonal, diagonal_mul] at e
    have : (B.ω j ^ 2 - B.ω i ^ 2) * Ct i j = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (hω i j h).symm)

end DampedStructure

/-! ### Fitting Rayleigh coefficients to two damping ratios -/

/-- The Rayleigh damping ratio `ζ(ω) = α/(2ω) + βω/2`. -/
def rayleighZeta (α β ω : ℝ) : ℝ := α / (2 * ω) + β * ω / 2

/-- The mass-proportional coefficient `α = 2ωᵢωⱼ(ζᵢωⱼ - ζⱼωᵢ)/(ωⱼ² - ωᵢ²)`. -/
def rayleighAlpha (ωi ζi ωj ζj : ℝ) : ℝ := 2 * ωi * ωj * (ζi * ωj - ζj * ωi) / (ωj ^ 2 - ωi ^ 2)

/-- The stiffness-proportional coefficient `β = 2(ζⱼωⱼ - ζᵢωᵢ)/(ωⱼ² - ωᵢ²)`. -/
def rayleighBeta (ωi ζi ωj ζj : ℝ) : ℝ := 2 * (ζj * ωj - ζi * ωi) / (ωj ^ 2 - ωi ^ 2)

/-- **Rayleigh fit**: the coefficients `rayleighAlpha`, `rayleighBeta` produce the damping
ratios `ζᵢ` at `ωᵢ` and `ζⱼ` at `ωⱼ` (`ωᵢ, ωⱼ > 0`, `ωᵢ ≠ ωⱼ`). -/
theorem rayleigh_fit {ωi ζi ωj ζj : ℝ} (hi : 0 < ωi) (hj : 0 < ωj) (hne : ωi ≠ ωj) :
    rayleighZeta (rayleighAlpha ωi ζi ωj ζj) (rayleighBeta ωi ζi ωj ζj) ωi = ζi ∧
      rayleighZeta (rayleighAlpha ωi ζi ωj ζj) (rayleighBeta ωi ζi ωj ζj) ωj = ζj := by
  have hD : ωj ^ 2 - ωi ^ 2 ≠ 0 := by
    intro h
    have : (ωj - ωi) * (ωj + ωi) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hne (by linarith)
    · linarith
  unfold rayleighZeta rayleighAlpha rayleighBeta
  constructor <;> field_simp <;> ring

/-- **Uniqueness of the Rayleigh fit**: any `α, β` with the prescribed damping ratios at two
distinct positive frequencies are the ones of `rayleigh_fit`. -/
theorem rayleigh_fit_unique {α β ωi ζi ωj ζj : ℝ} (hi : 0 < ωi) (hj : 0 < ωj) (hne : ωi ≠ ωj)
    (h1 : rayleighZeta α β ωi = ζi) (h2 : rayleighZeta α β ωj = ζj) :
    α = rayleighAlpha ωi ζi ωj ζj ∧ β = rayleighBeta ωi ζi ωj ζj := by
  have hD : ωj ^ 2 - ωi ^ 2 ≠ 0 := by
    intro h
    have : (ωj - ωi) * (ωj + ωi) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hne (by linarith)
    · linarith
  unfold rayleighZeta at h1 h2
  unfold rayleighAlpha rayleighBeta
  subst h1 h2
  constructor <;> field_simp <;> ring

/-- **Equal damping at two frequencies**: `α = 2ζωᵢωⱼ/(ωᵢ+ωⱼ)`, `β = 2ζ/(ωᵢ+ωⱼ)`. -/
theorem rayleigh_fit_equal {ωi ωj ζ : ℝ} (hi : 0 < ωi) (hj : 0 < ωj) (hne : ωi ≠ ωj) :
    rayleighAlpha ωi ζ ωj ζ = 2 * ζ * ωi * ωj / (ωi + ωj) ∧
      rayleighBeta ωi ζ ωj ζ = 2 * ζ / (ωi + ωj) := by
  have h1 : ωj - ωi ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : ωi + ωj ≠ 0 := by positivity
  have hD : ωj ^ 2 - ωi ^ 2 = (ωj - ωi) * (ωi + ωj) := by ring
  unfold rayleighAlpha rayleighBeta
  rw [hD]
  constructor <;> field_simp

/-! ### Modal superposition of free response -/

namespace DampedStructure

variable (S : DampedStructure n) (B : ModalBasis S.toSmallOscillations)

/-- **Modal superposition**: under classical damping `ΦᵀCΦ = diag(c)`, if each `xⱼ` solves the
free modal oscillator `ẍⱼ + cⱼẋⱼ + ωⱼ²xⱼ = 0`, then `q(t) = Σⱼ xⱼ(t) φⱼ` solves
`M q̈ + C q̇ + K q = 0`. -/
theorem free_superposition {c : Fin n → ℝ} (hc : B.Φᵀ * S.C * B.Φ = diagonal c)
    (x v a : Fin n → ℝ → ℝ) (hx : ∀ j t, HasDerivAt (x j) (v j t) t)
    (hv : ∀ j t, HasDerivAt (v j) (a j t) t)
    (heq : ∀ j t, a j t + c j * v j t + B.ω j ^ 2 * x j t = 0) :
    S.IsForcedMotion 0 ((MotionN.ofFamily x v a hx hv).mapMatrix B.Φ) ∧
      ∀ t, ((MotionN.ofFamily x v a hx hv).mapMatrix B.Φ).q t = ∑ j, x j t • B.Φᵀ j := by
  refine ⟨S.of_modal B fun t => ?_, fun t => B.mulVec_eq_sum _⟩
  rw [hc]
  ext j
  simpa [mulVec_diagonal, MotionN.ofFamily] using heq j t

/-- The underdamped modal oscillation `e^{-ct/2} cos(√(k - c²/4) t)`. -/
def underdampedX (c k t : ℝ) : ℝ := exp (-(c / 2) * t) * cos (√(k - (c / 2) ^ 2) * t)

/-- Its velocity. -/
def underdampedV (c k t : ℝ) : ℝ :=
  exp (-(c / 2) * t) * (-(c / 2) * cos (√(k - (c / 2) ^ 2) * t) -
    √(k - (c / 2) ^ 2) * sin (√(k - (c / 2) ^ 2) * t))

/-- Its acceleration. -/
def underdampedA (c k t : ℝ) : ℝ :=
  exp (-(c / 2) * t) * (((c / 2) ^ 2 - √(k - (c / 2) ^ 2) ^ 2) * cos (√(k - (c / 2) ^ 2) * t) +
    2 * (c / 2) * √(k - (c / 2) ^ 2) * sin (√(k - (c / 2) ^ 2) * t))

/-- The underdamped oscillation solves `ẍ + cẋ + kx = 0` for `c² < 4k`
(from `underdamped_solves` with unit mass). -/
theorem underdamped_spec {c k : ℝ} (hu : c ^ 2 < 4 * k) (t : ℝ) :
    HasDerivAt (underdampedX c k) (underdampedV c k t) t ∧
      HasDerivAt (underdampedV c k) (underdampedA c k t) t ∧
      underdampedA c k t + c * underdampedV c k t + k * underdampedX c k t = 0 := by
  have h := underdamped_solves (m := 1) (c := c) (k := k) one_pos (by linarith) t
  simp only [mul_one, div_one, one_mul] at h
  exact h

/-- **Free response of a Rayleigh-damped structure** with underdamped modes
`(α + βωⱼ²)² < 4ωⱼ²`: for any amplitudes `Aⱼ`,
`q(t) = Σⱼ Aⱼ e^{-γⱼt} cos(ω_{d,j} t) φⱼ` (with `2γⱼ = α + βωⱼ²`) solves
`M q̈ + C q̇ + K q = 0`. -/
theorem rayleigh_underdamped_superposition {α β : ℝ} (hC : S.C = α • S.M + β • S.K)
    (hu : ∀ j, (α + β * B.ω j ^ 2) ^ 2 < 4 * B.ω j ^ 2) (A : Fin n → ℝ) :
    ∃ γ : MotionN n, S.IsForcedMotion 0 γ ∧
      ∀ t, γ.q t = ∑ j, (A j * underdampedX (α + β * B.ω j ^ 2) (B.ω j ^ 2) t) • B.Φᵀ j := by
  let c : Fin n → ℝ := fun j => α + β * B.ω j ^ 2
  have hx : ∀ j t, HasDerivAt (fun s => A j * underdampedX (c j) (B.ω j ^ 2) s)
      (A j * underdampedV (c j) (B.ω j ^ 2) t) t := fun j t =>
    ((underdamped_spec (hu j) t).1).const_mul (A j)
  have hv : ∀ j t, HasDerivAt (fun s => A j * underdampedV (c j) (B.ω j ^ 2) s)
      (A j * underdampedA (c j) (B.ω j ^ 2) t) t := fun j t =>
    ((underdamped_spec (hu j) t).2.1).const_mul (A j)
  obtain ⟨h1, h2⟩ := S.free_superposition B (S.rayleigh_modal B hC) _ _ _ hx hv fun j t => by
    have := (underdamped_spec (hu j) t).2.2
    linear_combination A j * this
  exact ⟨_, h1, h2⟩

end DampedStructure

end ClassicalMechanics
