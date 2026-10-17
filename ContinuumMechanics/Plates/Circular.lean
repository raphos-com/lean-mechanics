import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Axisymmetric bending of circular Kirchhoff plates

A circular Kirchhoff–Love plate of radius `a`, flexural rigidity `D` and Poisson ratio `ν`
carries a uniform transverse load `q`. For an axisymmetric deflection `w = w(r)` the plate
equation `D Δ²w = q` becomes the ordinary differential equation

`Δ_r² w = q / D`,   `Δ_r f = f'' + f'/r = (1/r) (r f')'`,

and the radial and tangential bending moments are
`M_r = -D (w'' + ν w'/r)`, `M_θ = -D (w'/r + ν w'')` ([TimoshenkoWoinowsky1959], §§15–16).
We work in this one-dimensional radial formulation on `r > 0` (one-variable derivatives), which
avoids the coordinate singularity at the centre; `lapR` and `biharmR` use `deriv`, and the
derivatives are identified on the open half-line `Ioi 0`.

## Main results

* `biharmR_gen`: the general axisymmetric solution
  `w = q r⁴/(64 D) + C₁ + C₂ r² + C₃ log r + C₄ r² log r` satisfies `Δ_r² w = q/D` on `r > 0`.
* **Clamped plate** (`clamped`): `w = q (a² - r²)²/(64 D)` solves the equation
  (`clamped_solves`), satisfies `w(a) = w'(a) = 0` (`clamped_edge`, `deriv_clamped_edge`) and
  has central deflection `q a⁴/(64 D)` (`clamped_center`).
* Moments of the clamped plate: `M_r = q((1 + ν)a² - (3 + ν)r²)/16` (`momentR_clamped`),
  `M_θ = q((1 + ν)a² - (1 + 3ν)r²)/16` (`momentT_clamped`), edge values `-q a²/8`,
  `-ν q a²/8` (`momentR_clamped_edge`, `momentT_clamped_edge`), and the bound
  `|M_r|, |M_θ| ≤ q a²/8 = |M_r(a)|` on `0 < r ≤ a` for `-1 ≤ ν ≤ 1`
  (`abs_momentR_clamped_le`, `abs_momentT_clamped_le`).
* **Simply supported plate** (`simply`): `w = q (a² - r²)((5 + ν)/(1 + ν) a² - r²)/(64 D)`
  solves the equation (`simply_solves`), satisfies `w(a) = 0` and `M_r(a) = 0`
  (`simply_edge`, `momentR_simply_edge`), with central deflection
  `(5 + ν) q a⁴/(64 (1 + ν) D)` (`simply_center`).
* `center_ratio`, `one_lt_center_ratio`, `center_ratio_ge`: the ratio of central deflections
  simply supported / clamped is `(5 + ν)/(1 + ν)`, which exceeds `1` for `ν > -1` and is at
  least `11/3` for `-1 < ν ≤ 1/2`.

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, 2nd ed., §§15–16.
* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, 2nd ed., §5.2.
-/

open Set Filter Topology Real

noncomputable section

namespace ContinuumMechanics.Plates.Circular

/-! ### The axisymmetric Laplacian -/

/-- The **axisymmetric Laplacian** `Δ_r f = f'' + f'/r`. -/
def lapR (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv (deriv f) r + deriv f r / r

/-- The **axisymmetric biharmonic operator** `Δ_r² f = Δ_r (Δ_r f)`. -/
def biharmR (f : ℝ → ℝ) : ℝ → ℝ := lapR (lapR f)

/-- `Δ_r` only depends on the values of `f` near `r`. -/
theorem lapR_congr {f g : ℝ → ℝ} {r : ℝ} (h : f =ᶠ[𝓝 r] g) : lapR f r = lapR g r := by
  unfold lapR
  rw [h.deriv.deriv_eq, h.deriv_eq]

/-- `Δ_r` along explicitly known first and second derivatives on `r > 0`. -/
theorem lapR_eq {f f₁ f₂ : ℝ → ℝ} (h₁ : ∀ r > 0, HasDerivAt f (f₁ r) r)
    (h₂ : ∀ r > 0, HasDerivAt f₁ (f₂ r) r) {r : ℝ} (hr : 0 < r) :
    lapR f r = f₂ r + f₁ r / r := by
  have e : deriv f =ᶠ[𝓝 r] f₁ :=
    eventually_of_mem (Ioi_mem_nhds hr) fun s hs => (h₁ s hs).deriv
  unfold lapR
  rw [e.deriv_eq, (h₂ r hr).deriv, (h₁ r hr).deriv]

/-- If `Δ_r f = L` on `r > 0`, then `Δ_r² f = Δ_r L` there. -/
theorem biharmR_eq {f L : ℝ → ℝ} (h : ∀ s > 0, lapR f s = L s) {r : ℝ} (hr : 0 < r) :
    biharmR f r = lapR L r :=
  lapR_congr (eventually_of_mem (Ioi_mem_nhds hr) h)

/-! ### The general axisymmetric solution -/

section General

variable (q D C₁ C₂ C₃ C₄ : ℝ)

/-- The general axisymmetric solution
`w = q r⁴/(64 D) + C₁ + C₂ r² + C₃ log r + C₄ r² log r` of `Δ_r² w = q/D`. -/
def gen (r : ℝ) : ℝ :=
  q * r ^ 4 / (64 * D) + C₁ + C₂ * r ^ 2 + C₃ * log r + C₄ * (r ^ 2 * log r)

/-- Its derivative `w' = q r³/(16 D) + 2 C₂ r + C₃/r + C₄ (2 r log r + r)`. -/
def genD (r : ℝ) : ℝ :=
  q * r ^ 3 / (16 * D) + 2 * C₂ * r + C₃ / r + C₄ * (2 * r * log r + r)

/-- Its second derivative `w'' = 3 q r²/(16 D) + 2 C₂ - C₃/r² + C₄ (2 log r + 3)`. -/
def genDD (r : ℝ) : ℝ :=
  3 * q * r ^ 2 / (16 * D) + 2 * C₂ - C₃ / r ^ 2 + C₄ * (2 * log r + 3)

/-- Its Laplacian `Δ_r w = q r²/(4 D) + 4 C₂ + 4 C₄ (log r + 1)`. -/
def genL (r : ℝ) : ℝ := q * r ^ 2 / (4 * D) + 4 * C₂ + 4 * C₄ * (log r + 1)

/-- `(Δ_r w)' = q r/(2 D) + 4 C₄/r`. -/
def genLD (r : ℝ) : ℝ := q * r / (2 * D) + 4 * C₄ / r

/-- `(Δ_r w)'' = q/(2 D) - 4 C₄/r²`. -/
def genLDD (r : ℝ) : ℝ := q / (2 * D) - 4 * C₄ / r ^ 2

/-- `w' = genD` on `r > 0`. -/
theorem hasDerivAt_gen {r : ℝ} (hr : 0 < r) :
    HasDerivAt (gen q D C₁ C₂ C₃ C₄) (genD q D C₂ C₃ C₄ r) r := by
  have hl := hasDerivAt_log hr.ne'
  have h := (((((hasDerivAt_pow 4 r).const_mul q).div_const (64 * D)).const_add C₁).add
    ((hasDerivAt_pow 2 r).const_mul C₂)).add (hl.const_mul C₃) |>.add
    (((hasDerivAt_pow 2 r).mul hl).const_mul C₄)
  convert h using 1
  · funext s; simp only [gen, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [genD]; field_simp; ring

/-- `w'' = genDD` on `r > 0`. -/
theorem hasDerivAt_genD {r : ℝ} (hr : 0 < r) :
    HasDerivAt (genD q D C₂ C₃ C₄) (genDD q D C₂ C₃ C₄ r) r := by
  have hl := hasDerivAt_log hr.ne'
  have h := (((((hasDerivAt_pow 3 r).const_mul q).div_const (16 * D)).add
    ((hasDerivAt_id' r).const_mul (2 * C₂))).add ((hasDerivAt_inv hr.ne').const_mul C₃)).add
    (((((hasDerivAt_id' r).mul hl).const_mul 2).add (hasDerivAt_id' r)).const_mul C₄)
  convert h using 1
  · funext s; simp only [genD, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [genDD]; field_simp; ring

/-- `(Δ_r w)' = genLD` on `r > 0`. -/
theorem hasDerivAt_genL {r : ℝ} (hr : 0 < r) :
    HasDerivAt (genL q D C₂ C₄) (genLD q D C₄ r) r := by
  have h := ((((hasDerivAt_pow 2 r).const_mul q).div_const (4 * D)).const_add (4 * C₂)).add
    (((hasDerivAt_log hr.ne').add_const 1).const_mul (4 * C₄))
  convert h using 1
  · funext s; simp only [genL, Pi.add_apply]; ring
  · simp only [genLD]; field_simp; ring

/-- `(Δ_r w)'' = genLDD` on `r > 0`. -/
theorem hasDerivAt_genLD {r : ℝ} (hr : 0 < r) :
    HasDerivAt (genLD q D C₄) (genLDD q D C₄ r) r := by
  have h := (((hasDerivAt_id' r).const_mul q).div_const (2 * D)).add
    ((hasDerivAt_inv hr.ne').const_mul (4 * C₄))
  convert h using 1
  · funext s; simp only [genLD, Pi.add_apply]; ring
  · simp only [genLDD]; field_simp; ring

/-- `Δ_r w = genL` on `r > 0`. -/
theorem lapR_gen {r : ℝ} (hr : 0 < r) : lapR (gen q D C₁ C₂ C₃ C₄) r = genL q D C₂ C₄ r := by
  rw [lapR_eq (fun s hs => hasDerivAt_gen q D C₁ C₂ C₃ C₄ hs)
    (fun s hs => hasDerivAt_genD q D C₂ C₃ C₄ hs) hr]
  simp only [genDD, genD, genL]
  field_simp
  ring

/-- **General axisymmetric solution**: on `r > 0`,
`Δ_r² (q r⁴/(64 D) + C₁ + C₂ r² + C₃ log r + C₄ r² log r) = q/D`. -/
theorem biharmR_gen {r : ℝ} (hr : 0 < r) : biharmR (gen q D C₁ C₂ C₃ C₄) r = q / D := by
  rw [biharmR_eq (fun s hs => lapR_gen q D C₁ C₂ C₃ C₄ hs) hr,
    lapR_eq (fun s hs => hasDerivAt_genL q D C₂ C₄ hs) (fun s hs => hasDerivAt_genLD q D C₄ hs)
      hr]
  simp only [genLDD, genLD]
  field_simp
  ring

/-- Equivalently, the general solution satisfies the plate equation `D Δ_r² w = q` for
`D ≠ 0`. -/
theorem plate_gen (hD : D ≠ 0) {r : ℝ} (hr : 0 < r) :
    D * biharmR (gen q D C₁ C₂ C₃ C₄) r = q := by
  rw [biharmR_gen q D C₁ C₂ C₃ C₄ hr]
  field_simp

end General

/-! ### Bending moments -/

/-- Radial bending moment `M_r = -D (w'' + ν w'/r)`. -/
def momentR (D ν : ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ := -D * (deriv (deriv w) r + ν * deriv w r / r)

/-- Tangential bending moment `M_θ = -D (w'/r + ν w'')`. -/
def momentT (D ν : ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ := -D * (deriv w r / r + ν * deriv (deriv w) r)

/-- Moments along explicitly known derivatives on `r > 0`. -/
theorem moments_eq {D ν : ℝ} {f f₁ f₂ : ℝ → ℝ} (h₁ : ∀ r > 0, HasDerivAt f (f₁ r) r)
    (h₂ : ∀ r > 0, HasDerivAt f₁ (f₂ r) r) {r : ℝ} (hr : 0 < r) :
    momentR D ν f r = -D * (f₂ r + ν * f₁ r / r) ∧
      momentT D ν f r = -D * (f₁ r / r + ν * f₂ r) := by
  have e : deriv f =ᶠ[𝓝 r] f₁ :=
    eventually_of_mem (Ioi_mem_nhds hr) fun s hs => (h₁ s hs).deriv
  unfold momentR momentT
  rw [e.deriv_eq, (h₂ r hr).deriv, (h₁ r hr).deriv]
  exact ⟨rfl, rfl⟩

/-! ### The clamped plate -/

section Clamped

variable (q D a : ℝ)

/-- Deflection of a **clamped** circular plate under uniform load:
`w = q (a² - r²)²/(64 D)`. -/
def clamped (r : ℝ) : ℝ := q * (a ^ 2 - r ^ 2) ^ 2 / (64 * D)

/-- The clamped deflection is the general solution with `C₁ = q a⁴/(64 D)`,
`C₂ = -q a²/(32 D)` and `C₃ = C₄ = 0` (regularity at the centre). -/
theorem clamped_eq_gen :
    clamped q D a = gen q D (q * a ^ 4 / (64 * D)) (-(q * a ^ 2) / (32 * D)) 0 0 := by
  funext r
  simp only [clamped, gen]
  ring

/-- `w'` of the clamped plate: `w' = -q r (a² - r²)/(16 D)`. -/
theorem deriv_clamped (r : ℝ) :
    deriv (clamped q D a) r = -(q * r * (a ^ 2 - r ^ 2)) / (16 * D) := by
  have h := ((((hasDerivAt_pow 2 r).const_sub (a ^ 2)).pow 2).const_mul q).div_const (64 * D)
  rw [show deriv (clamped q D a) r = _ from h.deriv]
  field_simp
  ring

/-- The clamped deflection solves the plate equation `Δ_r² w = q/D` on `r > 0`. -/
theorem clamped_solves {r : ℝ} (hr : 0 < r) : biharmR (clamped q D a) r = q / D := by
  rw [clamped_eq_gen]
  exact biharmR_gen q D _ _ _ _ hr

/-- Clamped edge: `w(a) = 0`. -/
theorem clamped_edge : clamped q D a a = 0 := by simp [clamped]

/-- Clamped edge: zero slope `w'(a) = 0`. -/
theorem deriv_clamped_edge : deriv (clamped q D a) a = 0 := by
  rw [deriv_clamped]
  ring

/-- Regularity at the centre: zero slope `w'(0) = 0`. -/
theorem deriv_clamped_center : deriv (clamped q D a) 0 = 0 := by
  rw [deriv_clamped]
  ring

/-- **Central deflection of the clamped plate**: `w(0) = q a⁴/(64 D)`. -/
theorem clamped_center : clamped q D a 0 = q * a ^ 4 / (64 * D) := by
  simp only [clamped]
  ring

/-- The centre is the point of maximal deflection: `0 ≤ w(r) ≤ w(0)` for `0 ≤ r ≤ a`,
`q ≥ 0`, `D > 0`. -/
theorem clamped_le_center (hq : 0 ≤ q) (hD : 0 < D) {r : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) :
    0 ≤ clamped q D a r ∧ clamped q D a r ≤ clamped q D a 0 := by
  simp only [clamped]
  have h1 : 0 ≤ a ^ 2 - r ^ 2 := by nlinarith
  have h2 : (a ^ 2 - r ^ 2) ^ 2 ≤ (a ^ 2 - 0 ^ 2) ^ 2 := by nlinarith
  exact ⟨by positivity, div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hq)
    (by positivity)⟩

variable (ν : ℝ)

/-- Radial moment of the clamped plate: `M_r = q ((1 + ν) a² - (3 + ν) r²)/16`. -/
theorem momentR_clamped (hD : D ≠ 0) {r : ℝ} (hr : 0 < r) :
    momentR D ν (clamped q D a) r = q * ((1 + ν) * a ^ 2 - (3 + ν) * r ^ 2) / 16 := by
  rw [clamped_eq_gen, (moments_eq (fun s hs => hasDerivAt_gen q D _ _ 0 0 hs)
    (fun s hs => hasDerivAt_genD q D _ 0 0 hs) hr).1]
  simp only [genD, genDD]
  field_simp
  ring

/-- Tangential moment of the clamped plate: `M_θ = q ((1 + ν) a² - (1 + 3ν) r²)/16`. -/
theorem momentT_clamped (hD : D ≠ 0) {r : ℝ} (hr : 0 < r) :
    momentT D ν (clamped q D a) r = q * ((1 + ν) * a ^ 2 - (1 + 3 * ν) * r ^ 2) / 16 := by
  rw [clamped_eq_gen, (moments_eq (fun s hs => hasDerivAt_gen q D _ _ 0 0 hs)
    (fun s hs => hasDerivAt_genD q D _ 0 0 hs) hr).2]
  simp only [genD, genDD]
  field_simp
  ring

/-- Radial moment at the clamped edge: `M_r(a) = -q a²/8`. -/
theorem momentR_clamped_edge (hD : D ≠ 0) (ha : 0 < a) :
    momentR D ν (clamped q D a) a = -(q * a ^ 2 / 8) := by
  rw [momentR_clamped q D a ν hD ha]
  ring

/-- Tangential moment at the clamped edge: `M_θ(a) = -ν q a²/8`. -/
theorem momentT_clamped_edge (hD : D ≠ 0) (ha : 0 < a) :
    momentT D ν (clamped q D a) a = -(ν * q * a ^ 2 / 8) := by
  rw [momentT_clamped q D a ν hD ha]
  ring

/-- **The largest radial moment is at the edge**: `|M_r(r)| ≤ q a²/8` on `0 < r ≤ a` for
`q ≥ 0` and `-1 ≤ ν ≤ 1`. -/
theorem abs_momentR_clamped_le (hD : D ≠ 0) (hq : 0 ≤ q) (hν₁ : -1 ≤ ν) (hν₂ : ν ≤ 1)
    {r : ℝ} (hr : 0 < r) (hra : r ≤ a) :
    |momentR D ν (clamped q D a) r| ≤ q * a ^ 2 / 8 := by
  rw [momentR_clamped q D a ν hD hr, abs_le]
  have hs : r ^ 2 ≤ a ^ 2 := by nlinarith
  have h1 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + ν) (sub_nonneg.2 hs))
  have h2 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ν) (sq_nonneg a))
  have h3 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + ν) (sq_nonneg r))
  constructor <;> nlinarith

/-- **The largest tangential moment is bounded by the edge radial moment**:
`|M_θ(r)| ≤ q a²/8` on `0 < r ≤ a` for `q ≥ 0` and `-1 ≤ ν ≤ 1`. -/
theorem abs_momentT_clamped_le (hD : D ≠ 0) (hq : 0 ≤ q) (hν₁ : -1 ≤ ν) (hν₂ : ν ≤ 1)
    {r : ℝ} (hr : 0 < r) (hra : r ≤ a) :
    |momentT D ν (clamped q D a) r| ≤ q * a ^ 2 / 8 := by
  rw [momentT_clamped q D a ν hD hr, abs_le]
  have hs : r ^ 2 ≤ a ^ 2 := by nlinarith
  have hs' := sub_nonneg.2 hs
  have h1 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ν) hs')
  have h2 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ν) hs')
  have h3 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ν) (sq_nonneg r))
  have h4 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ν) (sq_nonneg r))
  have h5 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ν) (sq_nonneg a))
  have h6 := mul_nonneg hq (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ν) (sq_nonneg a))
  constructor <;> nlinarith

end Clamped

/-! ### The simply supported plate -/

section Simply

variable (q D a ν : ℝ)

/-- Deflection of a **simply supported** circular plate under uniform load:
`w = q (a² - r²)((5 + ν)/(1 + ν) a² - r²)/(64 D)`. -/
def simply (r : ℝ) : ℝ := q * (a ^ 2 - r ^ 2) * ((5 + ν) / (1 + ν) * a ^ 2 - r ^ 2) / (64 * D)

/-- The simply supported deflection is the general solution with `C₃ = C₄ = 0`. -/
theorem simply_eq_gen :
    simply q D a ν = gen q D (q * ((5 + ν) / (1 + ν)) * a ^ 4 / (64 * D))
      (-(q * a ^ 2 * (1 + (5 + ν) / (1 + ν))) / (64 * D)) 0 0 := by
  funext r
  simp only [simply, gen]
  ring

/-- The simply supported deflection solves `Δ_r² w = q/D` on `r > 0`. -/
theorem simply_solves {r : ℝ} (hr : 0 < r) : biharmR (simply q D a ν) r = q / D := by
  rw [simply_eq_gen]
  exact biharmR_gen q D _ _ _ _ hr

/-- Simply supported edge: `w(a) = 0`. -/
theorem simply_edge : simply q D a ν a = 0 := by simp [simply]

/-- Simply supported edge: zero radial moment `M_r(a) = -D (w'' + ν w'/r) = 0`
(for `ν ≠ -1`, `D ≠ 0`, `a > 0`). -/
theorem momentR_simply_edge (hD : D ≠ 0) (hν : 1 + ν ≠ 0) (ha : 0 < a) :
    momentR D ν (simply q D a ν) a = 0 := by
  rw [simply_eq_gen, (moments_eq (fun s hs => hasDerivAt_gen q D _ _ 0 0 hs)
    (fun s hs => hasDerivAt_genD q D _ 0 0 hs) ha).1]
  simp only [genD, genDD]
  field_simp
  ring

/-- **Central deflection of the simply supported plate**:
`w(0) = (5 + ν) q a⁴/(64 (1 + ν) D) = ((5 + ν)/(1 + ν)) · q a⁴/(64 D)`. -/
theorem simply_center : simply q D a ν 0 = (5 + ν) / (1 + ν) * (q * a ^ 4 / (64 * D)) := by
  simp only [simply]
  ring

/-- **Ratio of central deflections**: simply supported / clamped `= (5 + ν)/(1 + ν)`. -/
theorem center_ratio (hq : q ≠ 0) (hD : D ≠ 0) (ha : a ≠ 0) :
    simply q D a ν 0 / clamped q D a 0 = (5 + ν) / (1 + ν) := by
  rw [simply_center, clamped_center]
  field_simp

/-- The simply supported plate is more flexible: `(5 + ν)/(1 + ν) > 1` for `ν > -1`. -/
theorem one_lt_center_ratio (hν : -1 < ν) : 1 < (5 + ν) / (1 + ν) := by
  rw [one_lt_div (by linarith)]
  linarith

/-- For physical Poisson ratios `-1 < ν ≤ 1/2`, the simply supported plate deflects at least
`11/3` times as much at the centre as the clamped plate. -/
theorem center_ratio_ge (hν₁ : -1 < ν) (hν₂ : ν ≤ 1 / 2) : 11 / 3 ≤ (5 + ν) / (1 + ν) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- Central deflections compared directly: `w_clamped(0) < w_simply(0)` for `q, D, a > 0`
and `ν > -1`. -/
theorem clamped_center_lt_simply (hq : 0 < q) (hD : 0 < D) (ha : 0 < a) (hν : -1 < ν) :
    clamped q D a 0 < simply q D a ν 0 := by
  have hc : 0 < clamped q D a 0 := by rw [clamped_center]; positivity
  have h := center_ratio q D a ν hq.ne' hD.ne' ha.ne'
  rw [div_eq_iff hc.ne'] at h
  rw [h]
  exact lt_mul_of_one_lt_left hc (one_lt_center_ratio ν hν)

end Simply

end ContinuumMechanics.Plates.Circular
