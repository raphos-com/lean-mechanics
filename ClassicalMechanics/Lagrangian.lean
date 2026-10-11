import ClassicalMechanics.Vector
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Lagrangian mechanics with one degree of freedom

A **Lagrangian** `L(q, v)` with partial derivatives `∂L/∂q = L_q`, `∂L/∂v = L_v`, and a motion
`q(t)` with velocity `v = q̇` and acceleration `a = v̇` ([Arnold1989], §§12–15;
[Goldstein2002], §§2.1–2.7).

* **Chain rule** (`hasDerivAt_lagrangian`): `d/dt L(q, q̇) = L_q q̇ + L_v q̈`.
* **Conservation of energy** (`energy_const`): along a solution of the **Euler–Lagrange
  equation** `d/dt L_v(q, q̇) = L_q(q, q̇)`, the energy (Hamiltonian) `H = q̇ L_v - L` is conserved
  (Beltrami identity).
* **Cyclic coordinates** (`momentum_const`): if `L_q = 0` along the motion, the conjugate momentum
  `p = L_v` is conserved.
* **Hamilton's principle** (`firstVariation_eq`, `stationary_iff`): for variations `h` vanishing
  at the ends, the first variation of the action is
  `δS(h) = ∫ₐᵇ (L_q h + L_v ḣ) = ∫ₐᵇ (L_q - ṗ) h`, and the action is stationary for all smooth
  variations supported in `(a, b)` iff the Euler–Lagrange equation `ṗ = L_q` holds in `(a, b)`.
* **Natural systems** (`natural_EL_iff`, `natural_energy`): for `L = ½ m v² - U(q)` the
  Euler–Lagrange equation is Newton's law `m q̈ = -U'(q)` and `H = ½ m q̇² + U(q)`.

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§12–15.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §§2.1–2.7.
-/

open MeasureTheory Set intervalIntegral
open scoped ContDiff

noncomputable section

namespace ClassicalMechanics

/-- A Lagrangian `L(q, v)` of one degree of freedom with its partial derivatives. -/
structure Lagrangian where
  L : ℝ → ℝ → ℝ
  Lq : ℝ → ℝ → ℝ
  Lv : ℝ → ℝ → ℝ
  hasFDerivAt : ∀ q v, HasFDerivAt (fun p : ℝ × ℝ => L p.1 p.2)
    (Lq q v • ContinuousLinearMap.fst ℝ ℝ ℝ + Lv q v • ContinuousLinearMap.snd ℝ ℝ ℝ) (q, v)

/-- A motion `q(t)` with velocity `v` and acceleration `a`. -/
structure Motion where
  q : ℝ → ℝ
  v : ℝ → ℝ
  a : ℝ → ℝ
  hasDerivAt_q : ∀ t, HasDerivAt q (v t) t
  hasDerivAt_v : ∀ t, HasDerivAt v (a t) t

namespace Lagrangian

variable (𝓛 : Lagrangian) (γ : Motion)

/-- **Chain rule**: `d/dt L(q, q̇) = L_q q̇ + L_v q̈`. -/
theorem hasDerivAt_lagrangian (t : ℝ) :
    HasDerivAt (fun s => 𝓛.L (γ.q s) (γ.v s))
      (𝓛.Lq (γ.q t) (γ.v t) * γ.v t + 𝓛.Lv (γ.q t) (γ.v t) * γ.a t) t := by
  have h := (𝓛.hasFDerivAt (γ.q t) (γ.v t)).comp_hasDerivAt t
    ((γ.hasDerivAt_q t).prodMk (γ.hasDerivAt_v t))
  convert h using 1
  · rfl
  simp

/-- The **Euler–Lagrange equation** `d/dt L_v(q, q̇) = L_q(q, q̇)`. -/
def EulerLagrange : Prop :=
  ∀ t, HasDerivAt (fun s => 𝓛.Lv (γ.q s) (γ.v s)) (𝓛.Lq (γ.q t) (γ.v t)) t

/-- The energy (Hamiltonian) `H = q̇ L_v - L` along the motion. -/
def energy (t : ℝ) : ℝ := γ.v t * 𝓛.Lv (γ.q t) (γ.v t) - 𝓛.L (γ.q t) (γ.v t)

/-- **Conservation of energy** (Beltrami identity): along a solution of the Euler–Lagrange
equation of a time-independent Lagrangian, `H = q̇ L_v - L` is constant. -/
theorem energy_const (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) : 𝓛.energy γ s = 𝓛.energy γ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h := ((γ.hasDerivAt_v t).mul (hEL t)).sub (𝓛.hasDerivAt_lagrangian γ t)
  convert h using 1
  · funext s; rfl
  ring

/-- **Cyclic coordinates**: if `L_q = 0` along the motion, the momentum `p = L_v` is conserved. -/
theorem momentum_const (hEL : 𝓛.EulerLagrange γ) (hc : ∀ t, 𝓛.Lq (γ.q t) (γ.v t) = 0)
    (s t : ℝ) : 𝓛.Lv (γ.q s) (γ.v s) = 𝓛.Lv (γ.q t) (γ.v t) :=
  eq_of_hasDerivAt_zero (fun t => hc t ▸ hEL t) s t

end Lagrangian

/-! ### Hamilton's principle -/

section Hamilton

variable {a b : ℝ} {F p p' : ℝ → ℝ}

/-- **First variation of the action**: for `h` vanishing at `a` and `b`,
`∫ₐᵇ (F h + p ḣ) = ∫ₐᵇ (F - ṗ) h` (with `F = L_q`, `p = L_v` along the motion). -/
theorem firstVariation_eq (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    (hF : Continuous F) {h h' : ℝ → ℝ} (hh : ∀ t, HasDerivAt h (h' t) t) (hh' : Continuous h')
    (ha : h a = 0) (hb : h b = 0) :
    ∫ t in a..b, (F t * h t + p t * h' t) = ∫ t in a..b, (F t - p' t) * h t := by
  have cp : Continuous p := continuous_iff_continuousAt.mpr fun t => (hp t).continuousAt
  have ch : Continuous h := continuous_iff_continuousAt.mpr fun t => (hh t).continuousAt
  have ibp := integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (fun t _ => hp t)
    (fun t _ => hh t) (hp'.intervalIntegrable a b) (hh'.intervalIntegrable a b)
  rw [ha, hb, mul_zero, mul_zero, sub_zero, zero_sub] at ibp
  rw [integral_add (f := fun t => F t * h t) (g := fun t => p t * h' t)
      ((hF.mul ch).intervalIntegrable a b) ((cp.mul hh').intervalIntegrable a b),
    ibp, ← sub_eq_add_neg, ← integral_sub (f := fun t => F t * h t) (g := fun t => p' t * h t)
      ((hF.mul ch).intervalIntegrable a b) ((hp'.mul ch).intervalIntegrable a b)]
  exact integral_congr fun t _ => by ring

/-- **Hamilton's principle**: the action is stationary for every smooth variation `g` compactly
supported in `(a, b)` iff the Euler–Lagrange equation `ṗ = F` holds in `(a, b)`. -/
theorem stationary_iff (hab : a < b) (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    (hF : Continuous F) :
    (∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      ∫ t in a..b, (F t * g t + p t * deriv g t) = 0) ↔ ∀ t ∈ Ioo a b, p' t = F t := by
  have hvar : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → tsupport g ⊆ Ioo a b →
      ∫ t in a..b, (F t * g t + p t * deriv g t) = ∫ t in a..b, (F t - p' t) * g t := by
    intro g hg hgU
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    have h0 : ∀ t ∉ Ioo a b, g t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hgU h)
    exact firstVariation_eq hp hp' hF (fun t => (hg1.differentiable one_ne_zero t).hasDerivAt)
      (hg1.continuous_deriv le_rfl) (h0 a (by simp)) (h0 b (by simp))
  constructor
  · intro h
    have hc : Continuous fun t => F t - p' t := hF.sub hp'
    have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun t => F t - p' t) (μ := volume) (hc.locallyIntegrable.locallyIntegrableOn _)
      fun g hg hgc hgU => by
        have h0 : ∀ t ∉ Ioo a b, g t = 0 := fun t ht =>
          image_eq_zero_of_notMem_tsupport fun h => ht (hgU h)
        have e1 : ∫ t in a..b, (F t - p' t) * g t = 0 := by
          rw [← hvar g hg hgU]; exact h g hg hgc hgU
        rw [intervalIntegral.integral_of_le hab.le] at e1
        calc ∫ x, g x • (F x - p' x) = ∫ x in Ioc a b, g x • (F x - p' x) :=
              (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
                simp [h0 t fun h' => ht (Ioo_subset_Ioc_self h')]).symm
          _ = ∫ x in Ioc a b, (F x - p' x) * g x :=
              setIntegral_congr_fun measurableSet_Ioc fun t _ => by simp [smul_eq_mul, mul_comm]
          _ = 0 := e1
    have hS : IsOpen (Ioo a b ∩ {t | F t - p' t ≠ 0}) :=
      isOpen_Ioo.inter (isOpen_ne_fun hc continuous_const)
    have h0 : volume (Ioo a b ∩ {t | F t - p' t ≠ 0}) = 0 := by
      rw [ae_iff] at hae
      convert hae using 2
      ext t
      simp [and_assoc]
    have he := (hS.measure_eq_zero_iff volume).mp h0
    intro t ht
    by_contra hne
    have : t ∈ Ioo a b ∩ {t | F t - p' t ≠ 0} := ⟨ht, sub_ne_zero.mpr (Ne.symm hne)⟩
    rw [he] at this
    exact this
  · intro hEL g hg _ hgU
    rw [hvar g hg hgU]
    refine (integral_congr fun t ht => ?_).trans integral_zero
    by_cases htU : t ∈ Ioo a b
    · simp [hEL t htU]
    · simp [image_eq_zero_of_notMem_tsupport fun h => htU (hgU h)]

end Hamilton

/-! ### Natural systems -/

/-- The **natural Lagrangian** `L = ½ m v² - U(q)` of a particle in a potential `U`. -/
def natural (m : ℝ) (U U' : ℝ → ℝ) (hU : ∀ q, HasDerivAt U (U' q) q) : Lagrangian where
  L q v := m / 2 * v ^ 2 - U q
  Lq q _ := -U' q
  Lv _ v := m * v
  hasFDerivAt q v := by
    have h1 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := (q, v))).pow 2).const_mul (m / 2)
    have h2 := (hU q).hasFDerivAt.comp (q, v) (hasFDerivAt_fst (𝕜 := ℝ) (p := (q, v)))
    convert h1.sub h2 using 1
    · funext x; rfl
    apply ContinuousLinearMap.ext
    intro x
    simp
    ring

/-- For the natural Lagrangian, the Euler–Lagrange equation is **Newton's law**
`m q̈ = -U'(q)`. -/
theorem natural_EL_iff (m : ℝ) (U U' : ℝ → ℝ) (hU : ∀ q, HasDerivAt U (U' q) q) (γ : Motion) :
    (natural m U U' hU).EulerLagrange γ ↔ ∀ t, m * γ.a t = -U' (γ.q t) := by
  constructor
  · intro h t
    exact ((γ.hasDerivAt_v t).const_mul m).unique (h t)
  · intro h t
    have := (γ.hasDerivAt_v t).const_mul m
    rw [h t] at this
    exact this

/-- For the natural Lagrangian, the energy is `H = ½ m q̇² + U(q)`. -/
theorem natural_energy (m : ℝ) (U U' : ℝ → ℝ) (hU : ∀ q, HasDerivAt U (U' q) q) (γ : Motion)
    (t : ℝ) : (natural m U U' hU).energy γ t = m / 2 * γ.v t ^ 2 + U (γ.q t) := by
  simp only [Lagrangian.energy, natural]
  ring

end ClassicalMechanics
