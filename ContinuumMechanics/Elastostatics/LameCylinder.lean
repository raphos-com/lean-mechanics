import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Lamé's problem: the thick-walled cylinder and sphere under pressure

A thick-walled tube `a < r < b` of an isotropic linear elastic material (Lamé moduli `λ`, `μ`)
is loaded by an inner pressure `p_a` and an outer pressure `p_b`. In the axisymmetric
plane-strain state the only displacement is radial, `u = u(r)`, with strains `ε_r = u'`,
`ε_θ = u/r` and stresses

`σ_r = (λ + 2μ) u' + λ u/r`,   `σ_θ = λ u' + (λ + 2μ) u/r`   (`sigR`, `sigT`).

We work throughout in this one-dimensional radial formulation on `r > 0` (one-variable
`HasDerivAt`), which avoids the coordinate singularity at the axis.

## Main results

* `hasDerivAt_sigR`, `equilibrium_iff_ode`: the radial equilibrium equation
  `σ_r' + (σ_r - σ_θ)/r = 0` equals `(λ + 2μ)(u'' + u'/r - u/r²)`, hence (for `λ + 2μ ≠ 0`)
  is equivalent to the Euler equation `u'' + u'/r - u/r² = 0`.
* `general_solves`, `eq_general_of_ode`: `u = A r + B/r` solves the Euler equation, and every
  twice-differentiable solution on an interval `(a, b)` with `a ≥ 0` is of this form
  (via `(1/r (r u)')' = 0`).
* `sigR_general`, `sigT_general`: the stresses of `A r + B/r` are
  `2(λ + μ)A ∓ 2μB/r²`; `lame_displacement_stress` recovers Lamé's stresses with
  `A = A'/(2(λ + μ))`, `B = B'/(2μ)`.
* **Lamé's solution** (`lameR`, `lameT`): `σ_r = A' - B'/r²`, `σ_θ = A' + B'/r²` with
  `A' = (p_a a² - p_b b²)/(b² - a²)`, `B' = (p_a - p_b) a² b²/(b² - a²)`: equilibrium
  (`lame_equilibrium`), boundary conditions (`lameR_inner`, `lameR_outer`), constant
  `σ_r + σ_θ = 2A'` (`lame_sum`) and constant plane-strain axial stress (`lame_axial`).
* Internal pressure only: the hoop stress is maximal at the bore,
  `σ_θ(a) = p_a (b² + a²)/(b² - a²)` (`hoop_inner`, `hoop_le_inner`), `-p_a ≤ σ_r ≤ 0`
  (`radial_bounds`), and the **thin-wall (Barlow) limit** `σ_θ(a) t/a → p_a` for `b = a + t`,
  `t → 0⁺` (`barlow_error`, `tendsto_barlow`).
* The thick **spherical shell** (`sphR`, `sphT`, `sphere_*`): `u = A r + B/r²`,
  `σ_r = A' - 2B'/r³`, `σ_θ = A' + B'/r³`, with equilibrium `σ_r' + 2(σ_r - σ_θ)/r = 0` and
  the pressure boundary conditions.

## References

* [TimoshenkoGoodier1970] S. P. Timoshenko, J. N. Goodier, *Theory of Elasticity*, 3rd ed.,
  §§28, 136.
* [Barber2010] J. R. Barber, *Elasticity*, 3rd ed., §8.3.1.
* [Lame1852] G. Lamé, *Leçons sur la théorie mathématique de l'élasticité des corps solides*.
-/

open Set Filter Topology

noncomputable section

namespace ContinuumMechanics.LameCylinder

variable (lam μ : ℝ)

/-! ### Plane-strain cylinder: stresses and equilibrium -/

/-- Radial stress `σ_r = (λ + 2μ) ε_r + λ ε_θ` for `ε_r = u'`, `ε_θ = u/r`. -/
def sigR (du u r : ℝ) : ℝ := (lam + 2 * μ) * du + lam * u / r

/-- Hoop stress `σ_θ = λ ε_r + (λ + 2μ) ε_θ` for `ε_r = u'`, `ε_θ = u/r`. -/
def sigT (du u r : ℝ) : ℝ := lam * du + (lam + 2 * μ) * u / r

/-- Plane-strain axial stress `σ_z = λ (ε_r + ε_θ)`. -/
def sigZ (du u r : ℝ) : ℝ := lam * (du + u / r)

/-- The Euler-type residual `u'' + u'/r - u/r²` of the radial displacement equation. -/
def odeRes (ddu du u r : ℝ) : ℝ := ddu + du / r - u / r ^ 2

/-- `σ_r - σ_θ = 2μ (u' - u/r)`. -/
theorem sigR_sub_sigT (du u r : ℝ) :
    sigR lam μ du u r - sigT lam μ du u r = 2 * μ * (du - u / r) := by
  unfold sigR sigT; ring

/-- The derivative of the radial stress along a twice-differentiable displacement:
`σ_r' = (λ + 2μ) u'' + λ (u' r - u)/r²`. -/
theorem hasDerivAt_sigR {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) :
    HasDerivAt (fun s => sigR lam μ (du s) (u s) s)
      ((lam + 2 * μ) * ddu r + lam * ((du r * r - u r) / r ^ 2)) r := by
  unfold sigR
  have := (hdu.const_mul (lam + 2 * μ)).add ((hu.const_mul lam).div (hasDerivAt_id' r) hr)
  convert this using 1
  field_simp

/-- Radial equilibrium residual: `σ_r' + (σ_r - σ_θ)/r = (λ + 2μ)(u'' + u'/r - u/r²)`. -/
theorem equilibrium_eq {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) :
    deriv (fun s => sigR lam μ (du s) (u s) s) r +
        (sigR lam μ (du r) (u r) r - sigT lam μ (du r) (u r) r) / r =
      (lam + 2 * μ) * odeRes (ddu r) (du r) (u r) r := by
  rw [(hasDerivAt_sigR lam μ hu hdu hr).deriv, sigR_sub_sigT, odeRes]
  field_simp
  ring

/-- For `λ + 2μ ≠ 0`, radial equilibrium `σ_r' + (σ_r - σ_θ)/r = 0` is equivalent to the
Euler equation `u'' + u'/r - u/r² = 0`. -/
theorem equilibrium_iff_ode {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) (hlm : lam + 2 * μ ≠ 0) :
    deriv (fun s => sigR lam μ (du s) (u s) s) r +
        (sigR lam μ (du r) (u r) r - sigT lam μ (du r) (u r) r) / r = 0 ↔
      odeRes (ddu r) (du r) (u r) r = 0 := by
  rw [equilibrium_eq lam μ hu hdu hr, mul_eq_zero, or_iff_right hlm]

/-! ### General solution of the Euler equation -/

/-- The general radial displacement `u = A r + B/r`. -/
def gen (A B r : ℝ) : ℝ := A * r + B / r

/-- Its derivative `u' = A - B/r²`. -/
def genD (A B r : ℝ) : ℝ := A - B / r ^ 2

/-- Its second derivative `u'' = 2B/r³`. -/
def genDD (B r : ℝ) : ℝ := 2 * B / r ^ 3

/-- `(A r + B/r)' = A - B/r²` for `r ≠ 0`. -/
theorem hasDerivAt_gen (A B : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (gen A B) (genD A B r) r := by
  have := ((hasDerivAt_id' r).const_mul A).add ((hasDerivAt_inv hr).const_mul B)
  convert this using 1
  · funext s; simp [gen, div_eq_mul_inv]
  · simp only [genD]; ring

/-- `(A - B/r²)' = 2B/r³` for `r ≠ 0`. -/
theorem hasDerivAt_genD (A B : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (genD A B) (genDD B r) r := by
  have := (hasDerivAt_const r A).sub ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)
    |>.const_mul B)
  convert this using 1
  · funext s; simp [genD, div_eq_mul_inv]
  · simp only [genDD]
    field_simp
    ring

/-- `u = A r + B/r` solves `u'' + u'/r - u/r² = 0` on `r ≠ 0`. -/
theorem general_solves (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    odeRes (genDD B r) (genD A B r) (gen A B r) r = 0 := by
  unfold odeRes genDD genD gen
  field_simp
  ring

/-- A function with zero derivative on an open interval is constant there. -/
theorem exists_const_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ r ∈ Ioo a b, HasDerivAt f 0 r) :
    ∃ c, ∀ r ∈ Ioo a b, f r = c :=
  isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hf r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hf r hr).deriv)

/-- **Uniqueness**: every twice-differentiable solution of `u'' + u'/r - u/r² = 0` on an
interval `(a, b)` with `a ≥ 0` is of the form `u = A r + B/r`. The proof integrates
`(1/r (r u)')' = 0` twice: `w = u' + u/r` is constant `= 2A`, and then `r u - A r²` is
constant `= B`. -/
theorem eq_general_of_ode {u du ddu : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hu : ∀ r ∈ Ioo a b, HasDerivAt u (du r) r) (hdu : ∀ r ∈ Ioo a b, HasDerivAt du (ddu r) r)
    (hode : ∀ r ∈ Ioo a b, odeRes (ddu r) (du r) (u r) r = 0) :
    ∃ A B : ℝ, ∀ r ∈ Ioo a b, u r = gen A B r := by
  have hr0 : ∀ r ∈ Ioo a b, r ≠ 0 := fun r hr => (ha.trans_lt hr.1).ne'
  obtain ⟨c, hc⟩ := exists_const_Ioo (f := fun r => du r + u r / r) (a := a) (b := b)
    (fun r hr => by
      have := (hdu r hr).add ((hu r hr).div (hasDerivAt_id' r) (hr0 r hr))
      convert this using 1
      rw [← hode r hr]
      unfold odeRes
      field_simp [hr0 r hr]
      ring)
  obtain ⟨B, hB⟩ := exists_const_Ioo (f := fun r => r * u r - c / 2 * r ^ 2) (a := a) (b := b)
    (fun r hr => by
      have := ((hasDerivAt_id' r).mul (hu r hr)).sub ((hasDerivAt_pow 2 r).const_mul (c / 2))
      convert this using 1
      have h' : du r = c - u r / r := by linarith [hc r hr]
      rw [h']
      norm_num
      field_simp [hr0 r hr]
      ring)
  refine ⟨c / 2, B, fun r hr => ?_⟩
  have h := hB r hr
  simp only [gen]
  field_simp [hr0 r hr]
  linarith

/-- Stresses of the general solution: `σ_r = 2(λ + μ)A - 2μB/r²`. -/
theorem sigR_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sigR lam μ (genD A B r) (gen A B r) r = 2 * (lam + μ) * A - 2 * μ * B / r ^ 2 := by
  unfold sigR genD gen; field_simp; ring

/-- Stresses of the general solution: `σ_θ = 2(λ + μ)A + 2μB/r²`. -/
theorem sigT_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sigT lam μ (genD A B r) (gen A B r) r = 2 * (lam + μ) * A + 2 * μ * B / r ^ 2 := by
  unfold sigT genD gen; field_simp; ring

/-! ### Lamé's solution -/

/-- `A' = (p_a a² - p_b b²)/(b² - a²)`. -/
def lameA (a b pa pb : ℝ) : ℝ := (pa * a ^ 2 - pb * b ^ 2) / (b ^ 2 - a ^ 2)

/-- `B' = (p_a - p_b) a² b²/(b² - a²)`. -/
def lameB (a b pa pb : ℝ) : ℝ := (pa - pb) * a ^ 2 * b ^ 2 / (b ^ 2 - a ^ 2)

/-- Lamé's radial stress `σ_r = A' - B'/r²`. -/
def lameR (a b pa pb r : ℝ) : ℝ := lameA a b pa pb - lameB a b pa pb / r ^ 2

/-- Lamé's hoop stress `σ_θ = A' + B'/r²`. -/
def lameT (a b pa pb r : ℝ) : ℝ := lameA a b pa pb + lameB a b pa pb / r ^ 2

/-- `σ_r' = 2B'/r³`. -/
theorem hasDerivAt_lameR (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (lameR a b pa pb) (2 * lameB a b pa pb / r ^ 3) r := by
  have := (hasDerivAt_const r (lameA a b pa pb)).sub
    (((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_mul (lameB a b pa pb))
  convert this using 1
  · funext s; simp [lameR, div_eq_mul_inv]
  · field_simp; ring

/-- **Equilibrium** of Lamé's stresses: `σ_r' + (σ_r - σ_θ)/r = 0` on `r ≠ 0`. -/
theorem lame_equilibrium (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (lameR a b pa pb) r + (lameR a b pa pb r - lameT a b pa pb r) / r = 0 := by
  rw [(hasDerivAt_lameR a b pa pb hr).deriv]
  unfold lameR lameT
  field_simp
  ring

/-- Inner boundary condition `σ_r(a) = -p_a`. -/
theorem lameR_inner (a b pa pb : ℝ) (ha : a ≠ 0) (hab : b ^ 2 - a ^ 2 ≠ 0) :
    lameR a b pa pb a = -pa := by
  unfold lameR lameA lameB
  field_simp
  ring

/-- Outer boundary condition `σ_r(b) = -p_b`. -/
theorem lameR_outer (a b pa pb : ℝ) (hb : b ≠ 0) (hab : b ^ 2 - a ^ 2 ≠ 0) :
    lameR a b pa pb b = -pb := by
  unfold lameR lameA lameB
  field_simp
  ring

/-- `σ_r + σ_θ = 2A'` is constant through the wall. -/
theorem lame_sum (a b pa pb r : ℝ) :
    lameR a b pa pb r + lameT a b pa pb r = 2 * lameA a b pa pb := by
  unfold lameR lameT; ring

/-- The displacement `u = A r + B/r` with `A = A'/(2(λ + μ))`, `B = B'/(2μ)` produces exactly
Lamé's stresses (for `λ + μ ≠ 0`, `μ ≠ 0`). -/
theorem lame_displacement_stress (a b pa pb : ℝ) (h1 : lam + μ ≠ 0) (h2 : μ ≠ 0) {r : ℝ}
    (hr : r ≠ 0) :
    let A := lameA a b pa pb / (2 * (lam + μ))
    let B := lameB a b pa pb / (2 * μ)
    sigR lam μ (genD A B r) (gen A B r) r = lameR a b pa pb r ∧
      sigT lam μ (genD A B r) (gen A B r) r = lameT a b pa pb r := by
  intro A B
  rw [sigR_general lam μ A B hr, sigT_general lam μ A B hr]
  simp only [A, B, lameR, lameT]
  constructor <;> field_simp

/-- The plane-strain axial stress `σ_z = λ (u' + u/r)` of Lamé's displacement is the constant
`λ A'/(λ + μ)`. -/
theorem lame_axial (a b pa pb : ℝ) (h1 : lam + μ ≠ 0) (h2 : μ ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    let A := lameA a b pa pb / (2 * (lam + μ))
    let B := lameB a b pa pb / (2 * μ)
    sigZ lam (genD A B r) (gen A B r) r = lam * lameA a b pa pb / (lam + μ) := by
  intro A B
  simp only [sigZ, genD, gen, A, B]
  field_simp
  ring

/-! ### Internal pressure only: maximal hoop stress and the thin-wall limit -/

/-- With `p_b = 0`, the hoop stress at the bore is `σ_θ(a) = p_a (b² + a²)/(b² - a²)`. -/
theorem hoop_inner (a b pa : ℝ) (ha : a ≠ 0) (hab : b ^ 2 - a ^ 2 ≠ 0) :
    lameT a b pa 0 a = pa * (b ^ 2 + a ^ 2) / (b ^ 2 - a ^ 2) := by
  unfold lameT lameA lameB
  field_simp
  ring

/-- With `p_b = 0` and `p_a ≥ 0`, the hoop stress is maximal at the bore:
`σ_θ(r) ≤ σ_θ(a)` for `0 < a ≤ r`, `a < b`. -/
theorem hoop_le_inner (a b pa r : ℝ) (ha : 0 < a) (hab : a < b) (hpa : 0 ≤ pa) (har : a ≤ r) :
    lameT a b pa 0 r ≤ lameT a b pa 0 a := by
  unfold lameT
  gcongr
  unfold lameB
  have : 0 < b ^ 2 - a ^ 2 := by nlinarith
  positivity

/-- With `p_b = 0` and `p_a ≥ 0`, the radial stress is compressive and bounded by the
pressure: `-p_a ≤ σ_r(r) ≤ 0` for `0 < a ≤ r ≤ b`. -/
theorem radial_bounds (a b pa r : ℝ) (ha : 0 < a) (hab : a < b) (hpa : 0 ≤ pa) (har : a ≤ r)
    (hrb : r ≤ b) : -pa ≤ lameR a b pa 0 r ∧ lameR a b pa 0 r ≤ 0 := by
  have hd : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hr : 0 < r := ha.trans_le har
  have hr2 : a ^ 2 ≤ r ^ 2 := by gcongr
  have hr2' : r ^ 2 ≤ b ^ 2 := by gcongr
  have key : lameR a b pa 0 r = pa * a ^ 2 * (r ^ 2 - b ^ 2) / ((b ^ 2 - a ^ 2) * r ^ 2) := by
    unfold lameR lameA lameB
    field_simp
    ring
  rw [key]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hpa (sq_nonneg b)) (sub_nonneg.2 hr2)]
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (by positivity)

/-- Thin-wall error: for `b = a + t` with `a, t > 0`,
`σ_θ(a) t/a - p_a = p_a t (a + t)/((2a + t) a)`, which is `O(t/a)`. -/
theorem barlow_error (a t pa : ℝ) (ha : 0 < a) (ht : 0 < t) :
    lameT a (a + t) pa 0 a * t / a - pa = pa * t * (a + t) / ((2 * a + t) * a) := by
  rw [hoop_inner a (a + t) pa ha.ne' (by nlinarith), show (a + t) ^ 2 - a ^ 2 = t * (2 * a + t) by
    ring]
  have : 2 * a + t ≠ 0 := by positivity
  field_simp
  ring

/-- **Barlow's thin-wall formula** as a limit: for `b = a + t`, `σ_θ(a) · t/a → p_a`
as `t → 0⁺`. -/
theorem tendsto_barlow (a pa : ℝ) (ha : 0 < a) :
    Tendsto (fun t => lameT a (a + t) pa 0 a * t / a) (𝓝[>] 0) (𝓝 pa) := by
  have hc : Tendsto (fun t : ℝ => pa + pa * t * (a + t) / ((2 * a + t) * a)) (𝓝 0)
      (𝓝 (pa + pa * 0 * (a + 0) / ((2 * a + 0) * a))) := by
    apply Tendsto.add tendsto_const_nhds
    apply Tendsto.div _ _ (by positivity)
    · exact ((tendsto_const_nhds.mul tendsto_id).mul (tendsto_const_nhds.add tendsto_id))
    · exact (tendsto_const_nhds.add tendsto_id).mul tendsto_const_nhds
  simp only [mul_zero, zero_mul, add_zero, zero_div] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← barlow_error a t pa ha ht]
  ring

/-! ### The thick spherical shell -/

/-- Spherical radial stress for `u = A r + B/r²`: `σ_r = (λ + 2μ) u' + 2λ u/r`. -/
def sphSigR (du u r : ℝ) : ℝ := (lam + 2 * μ) * du + 2 * lam * u / r

/-- Spherical hoop stress: `σ_θ = λ u' + 2(λ + μ) u/r`. -/
def sphSigT (du u r : ℝ) : ℝ := lam * du + 2 * (lam + μ) * u / r

/-- Stresses of the spherical general solution `u = A r + B/r²`, `u' = A - 2B/r³`:
`σ_r = (3λ + 2μ)A - 4μB/r³` and `σ_θ = (3λ + 2μ)A + 2μB/r³`. -/
theorem sphere_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphSigR lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r =
        (3 * lam + 2 * μ) * A - 4 * μ * B / r ^ 3 ∧
      sphSigT lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r =
        (3 * lam + 2 * μ) * A + 2 * μ * B / r ^ 3 := by
  unfold sphSigR sphSigT
  constructor <;> field_simp <;> ring

/-- Lamé constant `A' = (p_a a³ - p_b b³)/(b³ - a³)` for the sphere. -/
def sphA (a b pa pb : ℝ) : ℝ := (pa * a ^ 3 - pb * b ^ 3) / (b ^ 3 - a ^ 3)

/-- Lamé constant `B' = (p_a - p_b) a³ b³/(2(b³ - a³))` for the sphere. -/
def sphB (a b pa pb : ℝ) : ℝ := (pa - pb) * a ^ 3 * b ^ 3 / (2 * (b ^ 3 - a ^ 3))

/-- Sphere radial stress `σ_r = A' - 2B'/r³`. -/
def sphR (a b pa pb r : ℝ) : ℝ := sphA a b pa pb - 2 * sphB a b pa pb / r ^ 3

/-- Sphere hoop stress `σ_θ = A' + B'/r³`. -/
def sphT (a b pa pb r : ℝ) : ℝ := sphA a b pa pb + sphB a b pa pb / r ^ 3

/-- `σ_r' = 6B'/r⁴` for the sphere. -/
theorem hasDerivAt_sphR (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sphR a b pa pb) (6 * sphB a b pa pb / r ^ 4) r := by
  have := (hasDerivAt_const r (sphA a b pa pb)).sub
    (((hasDerivAt_pow 3 r).inv (pow_ne_zero 3 hr)).const_mul (2 * sphB a b pa pb))
  convert this using 1
  · funext s; simp [sphR, div_eq_mul_inv]
  · field_simp; ring

/-- Spherical **equilibrium** `σ_r' + 2(σ_r - σ_θ)/r = 0` on `r ≠ 0`. -/
theorem sphere_equilibrium (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (sphR a b pa pb) r + 2 * (sphR a b pa pb r - sphT a b pa pb r) / r = 0 := by
  rw [(hasDerivAt_sphR a b pa pb hr).deriv]
  unfold sphR sphT
  field_simp
  ring

/-- Sphere boundary conditions `σ_r(a) = -p_a`, `σ_r(b) = -p_b`. -/
theorem sphere_bc (a b pa pb : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ^ 3 - a ^ 3 ≠ 0) :
    sphR a b pa pb a = -pa ∧ sphR a b pa pb b = -pb := by
  unfold sphR sphA sphB
  constructor <;> field_simp <;> ring

/-- The displacement `u = A r + B/r²` with `A = A'/(3λ + 2μ)`, `B = B'/(2μ)` produces the
spherical Lamé stresses. -/
theorem sphere_displacement_stress (a b pa pb : ℝ) (h1 : 3 * lam + 2 * μ ≠ 0) (h2 : μ ≠ 0)
    {r : ℝ} (hr : r ≠ 0) :
    let A := sphA a b pa pb / (3 * lam + 2 * μ)
    let B := sphB a b pa pb / (2 * μ)
    sphSigR lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r = sphR a b pa pb r ∧
      sphSigT lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r = sphT a b pa pb r := by
  intro A B
  rw [(sphere_general lam μ A B hr).1, (sphere_general lam μ A B hr).2]
  simp only [A, B, sphR, sphT]
  constructor
  · field_simp; ring
  · field_simp

end ContinuumMechanics.LameCylinder
