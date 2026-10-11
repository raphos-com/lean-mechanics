import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import DiscreteMechanics.Winding

/-!
# The one-dimensional Maxwell chain: edge modes and winding number

The simplest Maxwell lattice of [KaneLubensky2014] is a chain of sites `0, …, N` with one degree
of freedom `uₙ` each, linked by `N` bonds whose elongations are

`(C u)ₙ = c₁ uₙ + c₂ uₙ₊₁`,  `c₁, c₂ ≠ 0`

(e.g. their chain of rotors linked by springs). It is isostatic: `N + 1` degrees of freedom,
`N` bonds.

* The finite chain has **exactly one zero mode**, `uₙ = (-c₁/c₂)ⁿ u₀` (`eq_smul_mode`), and **no
  state of self-stress** (`selfStress_eq_zero`), as the Maxwell–Calladine count `1 = (N+1) - N`
  requires.
* The zero mode is **localized at the left edge** (`|uₙ| → 0`) iff `|c₁| < |c₂|`, at the right edge
  otherwise.
* For the infinite chain the Bloch compatibility "matrix" is `C(q) = c₁ + c₂ e^{iq}`. Its
  **winding number** around the Brillouin zone,
  `ν = (2πi)⁻¹ ∮_{|z|=1} c₂ / (c₁ + c₂ z) dz = (2πi)⁻¹ ∮ d log C`,
  is `1` if `|c₁| < |c₂|` and `0` if `|c₁| > |c₂|` (`winding_eq_one`, `winding_eq_zero`).

Hence **the bulk topological invariant `ν` decides on which edge the zero mode lives**
(`winding_eq_one_iff_left`): the one-dimensional instance of the topological boundary modes of
[KaneLubensky2014].

## References

* [KaneLubensky2014] C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
  lattices*, Nature Physics 10, 39–45 (2014).
-/

open Complex Filter Topology Metric

noncomputable section

namespace ContinuumMechanics.KaneLubensky

/-- A one-dimensional Maxwell chain with bond coefficients `c₁, c₂ ≠ 0`. -/
structure Chain where
  c₁ : ℝ
  c₂ : ℝ
  c₁_ne : c₁ ≠ 0
  c₂_ne : c₂ ≠ 0

namespace Chain

variable (K : Chain) {N : ℕ}

/-- Bond elongations of the finite chain with sites `0, …, N`. -/
def compat (u : Fin (N + 1) → ℝ) (n : Fin N) : ℝ := K.c₁ * u n.castSucc + K.c₂ * u n.succ

/-- The zero mode `(-c₁/c₂)ⁿ`. -/
def mode (n : ℕ) : ℝ := (-K.c₁ / K.c₂) ^ n

theorem compat_mode : K.compat (N := N) (fun n => K.mode n) = 0 := by
  funext n
  simp only [compat, mode, Fin.val_castSucc, Fin.val_succ, pow_succ, Pi.zero_apply]
  have := K.c₂_ne
  field_simp
  ring

/-- **The zero modes of the finite chain** are the multiples of `(-c₁/c₂)ⁿ`. -/
theorem eq_smul_mode {u : Fin (N + 1) → ℝ} (hu : K.compat u = 0) :
    ∀ n : Fin (N + 1), u n = u 0 * K.mode n := by
  have h2 := K.c₂_ne
  intro ⟨n, hn⟩
  induction n with
  | zero => simp [mode]
  | succ k ih =>
    have hk : k < N := by omega
    have e := congrFun hu ⟨k, hk⟩
    simp only [compat, Pi.zero_apply] at e
    have ih' := ih (by omega)
    simp only [Fin.castSucc_mk, Fin.succ_mk] at e
    rw [show u ⟨k + 1, hn⟩ = -(K.c₁ / K.c₂) * u ⟨k, by omega⟩ by
      field_simp; linear_combination e, ih', mode, mode, pow_succ]
    ring

/-- **No state of self-stress**: a bond tension doing no work on any displacement vanishes. -/
theorem selfStress_eq_zero {t : Fin N → ℝ} (ht : ∀ u : Fin (N + 1) → ℝ,
    ∑ n, t n * K.compat u n = 0) : t = 0 := by
  have h1 := K.c₁_ne
  -- testing with the unit displacement of site `m` gives `c₁ t_m + c₂ t_{m-1} = 0`
  have key : ∀ m : Fin (N + 1), ∑ n : Fin N, t n *
      (K.c₁ * (if n.castSucc = m then 1 else 0) + K.c₂ * (if n.succ = m then 1 else 0)) = 0 :=
    fun m => ht fun i => if i = m then 1 else 0
  funext ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := key ⟨n, by omega⟩
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero] at e
    have hA : ∑ i : Fin N, (if i.castSucc = (⟨n, by omega⟩ : Fin (N + 1)) then t i * K.c₁ else 0)
        = t ⟨n, hn⟩ * K.c₁ := by
      rw [Finset.sum_eq_single ⟨n, hn⟩]
      · simp
      · intro i _ hi
        rw [ite_eq_right_iff]
        intro h
        exact absurd (Fin.ext (by simpa using congrArg Fin.val h)) hi
      · simp
    have hB : ∑ i : Fin N, (if i.succ = (⟨n, by omega⟩ : Fin (N + 1)) then t i * K.c₂ else 0)
        = if h : 0 < n then t ⟨n - 1, by omega⟩ * K.c₂ else 0 := by
      split_ifs with hpos
      · rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
        · rw [ite_eq_left_iff]
          intro h
          exact absurd (Fin.ext (by simp; omega)) h
        · intro i _ hi
          rw [ite_eq_right_iff]
          intro h
          exfalso
          apply hi
          ext
          have := congrArg Fin.val h
          simp at this ⊢
          omega
        · simp
      · refine Finset.sum_eq_zero fun i _ => ?_
        rw [ite_eq_right_iff]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
    rw [hA, hB] at e
    split_ifs at e with hpos
    · rw [ih (n - 1) (by omega) (by omega), Pi.zero_apply, zero_mul, add_zero] at e
      simpa [h1] using e
    · simpa [h1] using e

/-! ### Localization of the zero mode -/

theorem abs_mode (n : ℕ) : |K.mode n| = (|K.c₁| / |K.c₂|) ^ n := by
  simp [mode, abs_div, abs_neg, abs_pow]

/-- The zero mode decays away from the left edge iff `|c₁| < |c₂|`. -/
theorem tendsto_mode_iff :
    Tendsto K.mode atTop (𝓝 0) ↔ |K.c₁| < |K.c₂| := by
  have h2 : 0 < |K.c₂| := abs_pos.2 K.c₂_ne
  have h1 : 0 < |K.c₁| := abs_pos.2 K.c₁_ne
  rw [← div_lt_one h2]
  change Tendsto (fun n : ℕ => (-K.c₁ / K.c₂) ^ n) atTop (𝓝 0) ↔ _
  constructor
  · intro h
    have h' := h.abs
    simp only [abs_zero, abs_pow, abs_div, abs_neg] at h'
    by_contra hge
    push Not at hge
    have : ∀ n : ℕ, 1 ≤ (|K.c₁| / |K.c₂|) ^ n := fun n => one_le_pow₀ hge
    have := ge_of_tendsto' h' this
    norm_num at this
  · intro h
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
      rw [abs_div, abs_neg]; exact h)

/-! ### Winding number of the Bloch compatibility -/

/-- The winding number `(2πi)⁻¹ ∮_{|z|=1} c₂ / (c₁ + c₂ z) dz` of `q ↦ c₁ + c₂ e^{iq}`. -/
def winding : ℂ := (2 * Real.pi * I)⁻¹ * ∮ z in C(0, 1), (K.c₂ : ℂ) / (K.c₁ + K.c₂ * z)

theorem integrand_eq (z : ℂ) :
    (K.c₂ : ℂ) / (K.c₁ + K.c₂ * z) = (z - (-(K.c₁ / K.c₂) : ℂ))⁻¹ := by
  have h2 : (K.c₂ : ℂ) ≠ 0 := by exact_mod_cast K.c₂_ne
  rcases eq_or_ne ((K.c₁ : ℂ) + K.c₂ * z) 0 with h | h
  · have hz : z - (-(K.c₁ / K.c₂) : ℂ) = 0 := by
      field_simp; linear_combination h
    rw [h, hz]; simp
  · have hz : z - (-(K.c₁ / K.c₂) : ℂ) ≠ 0 := by
      intro hz; apply h; field_simp at hz; linear_combination hz
    field_simp
    rw [show (K.c₂ : ℂ) * z - -K.c₁ = K.c₁ + K.c₂ * z by ring, div_self h]

theorem norm_root : ‖(-(K.c₁ / K.c₂) : ℂ)‖ = |K.c₁| / |K.c₂| := by
  rw [norm_neg, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- `ν = 1` when `|c₁| < |c₂|`. -/
theorem winding_eq_one (h : |K.c₁| < |K.c₂|) : K.winding = 1 := by
  have h2 : 0 < |K.c₂| := abs_pos.2 K.c₂_ne
  have hw : (-(K.c₁ / K.c₂) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, norm_root, div_lt_one h2]; exact h
  rw [winding, funext K.integrand_eq, circleIntegral.integral_sub_inv_of_mem_ball hw]
  have : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  field_simp

/-- `ν = 0` when `|c₁| > |c₂|`. -/
theorem winding_eq_zero (h : |K.c₂| < |K.c₁|) : K.winding = 0 := by
  have h2 : 0 < |K.c₂| := abs_pos.2 K.c₂_ne
  have hw : 1 < ‖(-(K.c₁ / K.c₂) : ℂ)‖ := by rw [norm_root, one_lt_div h2]; exact h
  rw [winding, funext K.integrand_eq]
  have hne : ∀ z ∈ closedBall (0 : ℂ) 1, z - (-(K.c₁ / K.c₂) : ℂ) ≠ 0 := fun z hz h0 => by
    rw [sub_eq_zero] at h0
    rw [mem_closedBall, dist_zero_right, h0] at hz
    linarith
  have hd : DiffContOnCl ℂ (fun z : ℂ => (z - (-(K.c₁ / K.c₂) : ℂ))⁻¹) (ball 0 1) := by
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.inv
      · fun_prop
      · exact hne z (ball_subset_closedBall hz)
    · rw [closure_ball _ one_ne_zero] at hz
      exact ((continuousAt_id.sub continuousAt_const).inv₀ (hne z hz)).continuousWithinAt
  rw [hd.circleIntegral_eq_zero zero_le_one, mul_zero]

/-- **Bulk–edge correspondence in one dimension**: the winding number of the Bloch compatibility
is `1` exactly when the zero mode is localized at the left edge. -/
theorem winding_eq_one_iff_left (h : |K.c₁| ≠ |K.c₂|) :
    K.winding = 1 ↔ Tendsto K.mode atTop (𝓝 0) := by
  rw [tendsto_mode_iff]
  constructor
  · intro hw
    by_contra hlt
    have : |K.c₂| < |K.c₁| := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h)
    rw [K.winding_eq_zero this] at hw
    exact zero_ne_one hw
  · exact K.winding_eq_one

/-- The Bloch compatibility of the chain as a polynomial in `z = e^{iq}`: `c₁ + c₂ z`. -/
noncomputable def blochPoly : Polynomial ℂ :=
  Polynomial.C (K.c₁ : ℂ) + Polynomial.C (K.c₂ : ℂ) * Polynomial.X

/-- The chain's winding number is the general winding number
(`DiscreteMechanics.winding`) of its Bloch polynomial, which counts its roots in the unit disk
(`DiscreteMechanics.winding_eq_card_roots`). -/
theorem winding_eq_blochPoly : K.winding = DiscreteMechanics.winding K.blochPoly := by
  simp [winding, DiscreteMechanics.winding, blochPoly]

end Chain

end ContinuumMechanics.KaneLubensky
