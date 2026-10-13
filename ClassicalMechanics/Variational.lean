import ClassicalMechanics.Lagrangian
import ClassicalMechanics.Oscillator

/-!
# Classical problems of the calculus of variations

We treat a variational problem `∫ L(y, y') dx` whose integrand does not depend explicitly on the
independent variable `x` as a one-degree-of-freedom Lagrangian system (`Lagrangian`), with `x`
playing the role of time ([GelfandFomin1963], §§1–4; [Arnold1989], §§12–13).

* **Beltrami identity** (`beltrami`): along any extremal, `y' ∂L/∂y' - L` is constant; this is the
  conservation of energy `Lagrangian.energy_const`.
* **Geodesics in the plane** (`geodesic_accel_eq_zero`, `geodesic_affine`): for the arc-length
  integrand `L = √(1 + y'²)` the extremals have `y'' = 0`, i.e. are straight lines.
* **Catenary** (`catenary`, `catenaryCurve_EL`, `catenaryCurve_energy`): for the integrand
  `L = y √(1 + y'²)` of the hanging chain / minimal surface of revolution, `y = a cosh((x - b)/a)`
  is an extremal with Beltrami constant `-a`; conversely along every extremal
  `y / √(1 + y'²)` is constant (`catenary_beltrami`), and `y / √(1 + y'²) = a` forces
  `y'² = y²/a² - 1` (`catenary_slope_sq`).
* **Brachistochrone** (`brachL`, `brach_energy`, `brach_beltrami`): for the time integrand
  `L = √((1 + y'²)/y)` (`y` measured downward), the Beltrami identity reads `y (1 + y'²) = 2R`.
  The **cycloid** `x = R(θ - sin θ)`, `y = R(1 - cos θ)` has slope `dy/dx = sin θ/(1 - cos θ)`
  (`cycloid_slope`), satisfies `y (1 + y'²) = 2R` (`cycloid_beltrami`) and the Euler–Lagrange
  equation in parametric form `d/dθ L_{y'} = L_y · dx/dθ` (`cycloid_EL`).
* **Tautochrone** (`cycloid_speed`, `cycloid_height`, `tautochrone`): the arc length from the
  lowest point is `s = -4R cos(θ/2)` with `ds/dθ = 2R sin(θ/2)`, the depth is
  `y = 2R - s²/(8R)`, so motion under gravity along the cycloid is the harmonic oscillator
  `s̈ = -(g/(4R)) s`, whose period `2π/√(g/(4R))` does not depend on the amplitude.

## References

* [GelfandFomin1963] I. M. Gelfand, S. V. Fomin, *Calculus of Variations*, §§1–4.
* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§12–13.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §2.2.
-/

open Real Filter Set
open scoped Real Topology

noncomputable section

namespace ClassicalMechanics

/-! ### Beltrami identity -/

/-- **Beltrami identity**: for an integrand `L(y, y')` not depending on `x`, any extremal (a
solution of the Euler–Lagrange equation) satisfies `y' ∂L/∂y' - L = const`. -/
theorem beltrami (𝓛 : Lagrangian) (γ : Motion) (hEL : 𝓛.EulerLagrange γ) (s t : ℝ) :
    γ.v s * 𝓛.Lv (γ.q s) (γ.v s) - 𝓛.L (γ.q s) (γ.v s) =
      γ.v t * 𝓛.Lv (γ.q t) (γ.v t) - 𝓛.L (γ.q t) (γ.v t) :=
  𝓛.energy_const γ hEL s t

/-- `1 + v² > 0`. -/
theorem one_add_sq_pos (v : ℝ) : 0 < 1 + v ^ 2 := by positivity

/-- The derivative of `v ↦ √(1 + v²)` is `v / √(1 + v²)`. -/
theorem hasDerivAt_sqrt_one_add_sq (v : ℝ) :
    HasDerivAt (fun w => √(1 + w ^ 2)) (v / √(1 + v ^ 2)) v := by
  have h := ((hasDerivAt_pow 2 v).const_add 1).sqrt (one_add_sq_pos v).ne'
  convert h using 1
  field_simp
  ring

/-! ### Geodesics in the plane -/

/-- The **arc-length** integrand `L = √(1 + y'²)`, whose extremals are the geodesics of the
Euclidean plane. -/
def arcLength : Lagrangian where
  L _ v := √(1 + v ^ 2)
  Lq _ _ := 0
  Lv _ v := v / √(1 + v ^ 2)
  hasFDerivAt q v := by
    have h := (hasDerivAt_sqrt_one_add_sq v).hasFDerivAt.comp (q, v)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (q, v)))
    convert h using 1
    · funext p; rfl
    apply ContinuousLinearMap.ext
    intro x
    simp
    ring

/-- The map `v ↦ v / √(1 + v²)` is injective. -/
theorem div_sqrt_one_add_sq_injective {v w : ℝ}
    (h : v / √(1 + v ^ 2) = w / √(1 + w ^ 2)) : v = w := by
  have hv := sqrt_pos.mpr (one_add_sq_pos v)
  have hw := sqrt_pos.mpr (one_add_sq_pos w)
  have hv2 := sq_sqrt (one_add_sq_pos v).le
  have hw2 := sq_sqrt (one_add_sq_pos w).le
  have h1 : v * √(1 + w ^ 2) = w * √(1 + v ^ 2) := by
    field_simp at h; linarith
  have h2 : v ^ 2 = w ^ 2 := by
    have := congrArg (· ^ 2) h1
    simp only [mul_pow, hv2, hw2] at this
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · exact h3
  · subst h3
    have : w * (√(1 + w ^ 2) + √(1 + (-w) ^ 2)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h4 | h4
    · simp [h4]
    · nlinarith

/-- **Geodesics are straight lines (I)**: along an extremal of the arc-length integrand the
slope is constant and `y'' = 0`. -/
theorem geodesic_accel_eq_zero (γ : Motion) (hEL : arcLength.EulerLagrange γ) (t : ℝ) :
    γ.a t = 0 := by
  have hc : ∀ s, γ.v s = γ.v 0 := fun s =>
    div_sqrt_one_add_sq_injective (arcLength.momentum_const γ hEL (fun _ => rfl) s 0)
  have h : HasDerivAt γ.v 0 t := by
    have : γ.v = fun _ => γ.v 0 := funext hc
    rw [this]; exact hasDerivAt_const t _
  exact (γ.hasDerivAt_v t).unique h

/-- **Geodesics are straight lines (II)**: every extremal of the arc-length integrand is an
affine function `y(x) = y(0) + y'(0) x`. -/
theorem geodesic_affine (γ : Motion) (hEL : arcLength.EulerLagrange γ) (x : ℝ) :
    γ.q x = γ.q 0 + γ.v 0 * x := by
  have hc : ∀ s, γ.v s = γ.v 0 := fun s =>
    div_sqrt_one_add_sq_injective (arcLength.momentum_const γ hEL (fun _ => rfl) s 0)
  have h : ∀ s, HasDerivAt (fun s => γ.q s - γ.v 0 * s) 0 s := fun s => by
    have := (γ.hasDerivAt_q s).sub ((hasDerivAt_id s).const_mul (γ.v 0))
    convert this using 1
    · funext y; rfl
    · rw [hc s]; ring
  have := eq_of_hasDerivAt_zero h x 0
  simp at this
  linarith

/-! ### The catenary -/

/-- The integrand `L = y √(1 + y'²)` of the **hanging chain** (potential energy of a chain of
uniform density) and of the **minimal surface of revolution** (area `2π ∫ y ds`). -/
def catenary : Lagrangian where
  L y v := y * √(1 + v ^ 2)
  Lq _ v := √(1 + v ^ 2)
  Lv y v := y * v / √(1 + v ^ 2)
  hasFDerivAt y v := by
    have hs := (hasDerivAt_sqrt_one_add_sq v).hasFDerivAt.comp (y, v)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, v)))
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y, v))).mul hs
    convert h using 1
    · funext p; rfl
    apply ContinuousLinearMap.ext
    intro x
    simp
    ring

/-- The Beltrami function of the catenary: `y' ∂L/∂y' - L = -y / √(1 + y'²)`. -/
theorem catenary_energy (γ : Motion) (t : ℝ) :
    catenary.energy γ t = -(γ.q t / √(1 + γ.v t ^ 2)) := by
  have hs := sqrt_pos.mpr (one_add_sq_pos (γ.v t))
  have hs2 := sq_sqrt (one_add_sq_pos (γ.v t)).le
  simp only [Lagrangian.energy, catenary]
  field_simp
  rw [hs2]
  ring

/-- **Beltrami identity for the catenary**: along any extremal, `y / √(1 + y'²)` is constant. -/
theorem catenary_beltrami (γ : Motion) (hEL : catenary.EulerLagrange γ) (s t : ℝ) :
    γ.q s / √(1 + γ.v s ^ 2) = γ.q t / √(1 + γ.v t ^ 2) := by
  have := catenary.energy_const γ hEL s t
  rw [catenary_energy, catenary_energy] at this
  linarith

/-- If `y / √(1 + y'²) = a` with `a > 0`, then `y'² = y²/a² - 1`: the first-order equation
integrated by `y = a cosh((x - b)/a)`. -/
theorem catenary_slope_sq {a y v : ℝ} (ha : 0 < a) (h : y / √(1 + v ^ 2) = a) :
    v ^ 2 = y ^ 2 / a ^ 2 - 1 := by
  have hs := sqrt_pos.mpr (one_add_sq_pos v)
  have hs2 := sq_sqrt (one_add_sq_pos v).le
  have hy : y = a * √(1 + v ^ 2) := by field_simp at h; linarith
  rw [hy, mul_pow, hs2]
  field_simp
  ring

/-- `√(1 + sinh² u) = cosh u`. -/
theorem sqrt_one_add_sinh_sq (u : ℝ) : √(1 + sinh u ^ 2) = cosh u := by
  rw [← cosh_sq', sqrt_sq (cosh_pos u).le]

/-- `d/du cosh u = sinh u` (via `cosh u = (eᵘ + e⁻ᵘ)/2`). -/
theorem hasDerivAt_cosh' (u : ℝ) : HasDerivAt cosh (sinh u) u := by
  have h := ((hasDerivAt_exp u).add ((hasDerivAt_neg u).exp)).div_const 2
  have e : cosh = fun x => (exp x + exp (-x)) / 2 := funext cosh_eq
  rw [e, sinh_eq]
  convert h using 1
  ring

/-- `d/du sinh u = cosh u` (via `sinh u = (eᵘ - e⁻ᵘ)/2`). -/
theorem hasDerivAt_sinh' (u : ℝ) : HasDerivAt sinh (cosh u) u := by
  have h := ((hasDerivAt_exp u).sub ((hasDerivAt_neg u).exp)).div_const 2
  have e : sinh = fun x => (exp x - exp (-x)) / 2 := funext sinh_eq
  rw [e, cosh_eq]
  convert h using 1
  ring

/-- The **catenary** `y = a cosh((x - b)/a)` as a motion, with slope `sinh((x - b)/a)` and
second derivative `cosh((x - b)/a)/a`. -/
def catenaryCurve (a b : ℝ) (ha : a ≠ 0) : Motion where
  q x := a * cosh ((x - b) / a)
  v x := sinh ((x - b) / a)
  a x := cosh ((x - b) / a) / a
  hasDerivAt_q x := by
    have h0 : HasDerivAt (fun x => (x - b) / a) (1 / a) x :=
      ((hasDerivAt_id x).sub_const b).div_const a
    have h := ((hasDerivAt_cosh' _).comp x h0).const_mul a
    convert h using 1
    · rfl
    field_simp
  hasDerivAt_v x := by
    have h0 : HasDerivAt (fun x => (x - b) / a) (1 / a) x :=
      ((hasDerivAt_id x).sub_const b).div_const a
    have h := (hasDerivAt_sinh' _).comp x h0
    convert h using 1
    · rfl
    field_simp

/-- **The catenary is an extremal**: `y = a cosh((x - b)/a)` satisfies the Euler–Lagrange
equation `d/dx (y y'/√(1 + y'²)) = √(1 + y'²)`. -/
theorem catenaryCurve_EL (a b : ℝ) (ha : a ≠ 0) :
    catenary.EulerLagrange (catenaryCurve a b ha) := by
  intro x
  have e : (fun s => catenary.Lv ((catenaryCurve a b ha).q s) ((catenaryCurve a b ha).v s)) =
      fun s => a * sinh ((s - b) / a) := by
    funext s
    simp only [catenary, catenaryCurve, sqrt_one_add_sinh_sq]
    field_simp [(cosh_pos ((s - b) / a)).ne']
  rw [e]
  have h0 : HasDerivAt (fun x => (x - b) / a) (1 / a) x :=
    ((hasDerivAt_id x).sub_const b).div_const a
  have h := ((hasDerivAt_sinh' _).comp x h0).const_mul a
  convert h using 1
  · rfl
  simp only [catenary, catenaryCurve, sqrt_one_add_sinh_sq]
  field_simp

/-- **Beltrami constant of the catenary**: along `y = a cosh((x - b)/a)`,
`y' ∂L/∂y' - L = -a`. -/
theorem catenaryCurve_energy (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    catenary.energy (catenaryCurve a b ha.ne') x = -a := by
  rw [catenary_energy]
  simp only [catenaryCurve, sqrt_one_add_sinh_sq]
  field_simp [(cosh_pos ((x - b) / a)).ne']

/-! ### The brachistochrone -/

/-- The **brachistochrone** integrand `L(y, y') = √(1 + y'²) / √y` (the descent time is
`∫ L dx / √(2g)`, with `y > 0` measured downward from the starting point). -/
def brachL (y v : ℝ) : ℝ := √(1 + v ^ 2) / √y

/-- `∂L/∂y' = y' / √(y (1 + y'²))`. -/
def brachLv (y v : ℝ) : ℝ := v / √(y * (1 + v ^ 2))

/-- `∂L/∂y = -√(1 + y'²) / (2 y √y)`. -/
def brachLy (y v : ℝ) : ℝ := -(√(1 + v ^ 2) / (2 * y * √y))

/-- `brachLv` is the partial derivative of `brachL` in `y'` (for `y > 0`). -/
theorem hasDerivAt_brachL_v {y : ℝ} (hy : 0 < y) (v : ℝ) :
    HasDerivAt (fun w => brachL y w) (brachLv y v) v := by
  have h := (hasDerivAt_sqrt_one_add_sq v).div_const √y
  convert h using 1
  · rfl
  simp only [brachLv]
  rw [sqrt_mul hy.le]
  field_simp

/-- `brachLy` is the partial derivative of `brachL` in `y` (for `y > 0`). -/
theorem hasDerivAt_brachL_y {y : ℝ} (hy : 0 < y) (v : ℝ) :
    HasDerivAt (fun z => brachL z v) (brachLy y v) y := by
  have hs := sqrt_pos.mpr hy
  have h := ((hasDerivAt_id y).sqrt hy.ne').inv hs.ne'
  have h' := h.const_mul √(1 + v ^ 2)
  convert h' using 1
  · funext z; simp [brachL, div_eq_mul_inv]
  simp only [brachLy, id]
  rw [sq_sqrt hy.le]
  field_simp

/-- The Beltrami function of the brachistochrone:
`y' ∂L/∂y' - L = -1/√(y (1 + y'²))`. -/
theorem brach_energy {y : ℝ} (hy : 0 < y) (v : ℝ) :
    v * brachLv y v - brachL y v = -(1 / √(y * (1 + v ^ 2))) := by
  have hs := sqrt_pos.mpr hy
  have hv := sqrt_pos.mpr (one_add_sq_pos v)
  have hv2 := sq_sqrt (one_add_sq_pos v).le
  simp only [brachLv, brachL]
  rw [sqrt_mul hy.le]
  field_simp
  rw [hv2]
  ring

/-- **Beltrami identity for the brachistochrone**: if `y' ∂L/∂y' - L = -1/√(2R)`, then
`y (1 + y'²) = 2R`. -/
theorem brach_beltrami {y v R : ℝ} (hy : 0 < y) (hR : 0 < R)
    (h : v * brachLv y v - brachL y v = -(1 / √(2 * R))) : y * (1 + v ^ 2) = 2 * R := by
  rw [brach_energy hy] at h
  have h1 : √(y * (1 + v ^ 2)) = √(2 * R) := by
    have hp := sqrt_pos.mpr (mul_pos hy (one_add_sq_pos v))
    have hq := sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * R)
    field_simp at h
    linarith
  rwa [sqrt_inj (mul_pos hy (one_add_sq_pos v)).le (by positivity)] at h1

/-- The abscissa `x(θ) = R(θ - sin θ)` of the **cycloid**. -/
def cycloidX (R θ : ℝ) : ℝ := R * (θ - sin θ)

/-- The depth `y(θ) = R(1 - cos θ)` of the **cycloid**. -/
def cycloidY (R θ : ℝ) : ℝ := R * (1 - cos θ)

/-- The slope `dy/dx = sin θ/(1 - cos θ)` of the cycloid. -/
def cycloidSlope (θ : ℝ) : ℝ := sin θ / (1 - cos θ)

/-- `dx/dθ = R(1 - cos θ)`. -/
theorem hasDerivAt_cycloidX (R θ : ℝ) : HasDerivAt (cycloidX R) (R * (1 - cos θ)) θ :=
  ((hasDerivAt_id θ).sub (hasDerivAt_sin θ)).const_mul R

/-- `dy/dθ = R sin θ`. -/
theorem hasDerivAt_cycloidY (R θ : ℝ) : HasDerivAt (cycloidY R) (R * sin θ) θ := by
  have h := ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cos θ)).const_mul R
  convert h using 1
  · funext φ; rfl
  · ring

/-- On `(0, 2π)`, `1 - cos θ > 0`. -/
theorem one_sub_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π)) : 0 < 1 - cos θ := by
  have h1 : cos θ ≤ 1 := cos_le_one θ
  have h2 : cos θ ≠ 1 := fun h =>
    hθ.1.ne' ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos, hθ.1]) hθ.2).mp h)
  exact sub_pos.mpr (lt_of_le_of_ne h1 h2)

/-- **Slope of the cycloid** (ratio of derivatives): if the arch is the graph of a function
`Y` (i.e. `Y(x(φ)) = y(φ)` near `θ`) differentiable at `x(θ)`, then
`Y'(x(θ)) = sin θ/(1 - cos θ)`. -/
theorem cycloid_slope {R θ Y' : ℝ} {Y : ℝ → ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 (2 * π))
    (hY : HasDerivAt Y Y' (cycloidX R θ)) (hgraph : ∀ᶠ φ in 𝓝 θ, Y (cycloidX R φ) = cycloidY R φ) :
    Y' = cycloidSlope θ := by
  have hc := one_sub_cos_pos hθ
  have h1 := (hY.comp θ (hasDerivAt_cycloidX R θ)).congr_of_eventuallyEq
    (hgraph.mono fun φ h => h.symm)
  have h2 := h1.unique (hasDerivAt_cycloidY R θ)
  have h3 : Y' * (1 - cos θ) = sin θ :=
    mul_left_cancel₀ hR.ne' (by rw [← h2]; ring)
  simp only [cycloidSlope]
  rw [eq_div_iff hc.ne']
  exact h3

/-- **The cycloid satisfies the Beltrami relation** `y (1 + y'²) = 2R` of the brachistochrone
on each arch `θ ∈ (0, 2π)`. -/
theorem cycloid_beltrami {R θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π)) :
    cycloidY R θ * (1 + cycloidSlope θ ^ 2) = 2 * R := by
  have hc := one_sub_cos_pos hθ
  simp only [cycloidY, cycloidSlope]
  field_simp
  linear_combination R * sin_sq_add_cos_sq θ

/-- Along the cycloid, the Beltrami function of the brachistochrone is `-1/√(2R)`. -/
theorem cycloid_energy {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 (2 * π)) :
    cycloidSlope θ * brachLv (cycloidY R θ) (cycloidSlope θ) -
      brachL (cycloidY R θ) (cycloidSlope θ) = -(1 / √(2 * R)) := by
  have hy : 0 < cycloidY R θ := mul_pos hR (one_sub_cos_pos hθ)
  rw [brach_energy hy, cycloid_beltrami hθ]

/-- `d/dθ (sin θ/(1 - cos θ)) = -1/(1 - cos θ)` on `(0, 2π)`. -/
theorem hasDerivAt_cycloidSlope {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π)) :
    HasDerivAt cycloidSlope (-(1 / (1 - cos θ))) θ := by
  have hc := one_sub_cos_pos hθ
  have h := (hasDerivAt_sin θ).div ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cos θ)) hc.ne'
  convert h using 1
  · funext φ; rfl
  simp only [Pi.sub_apply]
  field_simp
  linear_combination sin_sq_add_cos_sq θ

/-- **The cycloid is an extremal of the brachistochrone problem**: the Euler–Lagrange equation
in parametric form, `d/dθ L_{y'}(y, y') = L_y(y, y') · dx/dθ`, holds on `(0, 2π)`. -/
theorem cycloid_EL {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 (2 * π)) :
    HasDerivAt (fun φ => brachLv (cycloidY R φ) (cycloidSlope φ))
      (brachLy (cycloidY R θ) (cycloidSlope θ) * (R * (1 - cos θ))) θ := by
  have hc := one_sub_cos_pos hθ
  have hq := sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * R)
  have hq2 := sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * R)
  have e : (fun φ => brachLv (cycloidY R φ) (cycloidSlope φ)) =ᶠ[𝓝 θ]
      fun φ => cycloidSlope φ / √(2 * R) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    simp only [brachLv, cycloid_beltrami hφ]
  refine ((hasDerivAt_cycloidSlope hθ).div_const _).congr_of_eventuallyEq e |>.congr_deriv ?_
  -- simplify `L_y` using `1 + y'² = 2/(1 - cos θ)`
  have hy : 0 < cycloidY R θ := mul_pos hR hc
  have hb := cycloid_beltrami (R := R) hθ
  have h1 : 1 + cycloidSlope θ ^ 2 = 2 * R / cycloidY R θ := by
    field_simp; linarith
  have hsy := sqrt_pos.mpr hy
  have hsy2 := sq_sqrt hy.le
  have h2 : √(1 + cycloidSlope θ ^ 2) = √(2 * R) / √(cycloidY R θ) := by
    rw [h1, sqrt_div' _ hy.le]
  simp only [brachLy, h2]
  simp only [cycloidY] at hsy hsy2 ⊢
  field_simp
  rw [mul_comm (1 - cos θ) R, hsy2, hq2]
  ring

/-! ### The tautochrone -/

/-- `ds/dθ = 2R sin(θ/2)`: the speed `√(x'(θ)² + y'(θ)²)` of the cycloid parametrization. -/
theorem cycloid_speed {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 (2 * π)) :
    √((R * (1 - cos θ)) ^ 2 + (R * sin θ) ^ 2) = 2 * R * sin (θ / 2) := by
  have hs : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hcos : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, cos_two_mul, cos_sq']; ring_nf
  have e : (R * (1 - cos θ)) ^ 2 + (R * sin θ) ^ 2 = (2 * R * sin (θ / 2)) ^ 2 := by
    have := sin_sq_add_cos_sq θ
    have : (R * (1 - cos θ)) ^ 2 + (R * sin θ) ^ 2 = R ^ 2 * (2 - 2 * cos θ) := by
      linear_combination R ^ 2 * this
    rw [this, hcos]; ring
  rw [e, sqrt_sq (by positivity)]

/-- The **arc length** `s(θ) = -4R cos(θ/2)` along the cycloid, measured from the lowest point
`θ = π`. -/
def cycloidArc (R θ : ℝ) : ℝ := -(4 * R * cos (θ / 2))

/-- `ds/dθ = 2R sin(θ/2)`, which is the speed of the parametrization (`cycloid_speed`). -/
theorem hasDerivAt_cycloidArc (R θ : ℝ) :
    HasDerivAt (cycloidArc R) (2 * R * sin (θ / 2)) θ := by
  have h0 : HasDerivAt (fun φ : ℝ => φ / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
  have h := (h0.cos.const_mul (4 * R)).neg
  convert h using 1
  · funext φ; rfl
  ring

/-- **Depth as a function of arc length**: `y = 2R - s²/(8R)`; the potential energy
`-m g y` along the cycloid is therefore quadratic in `s`. -/
theorem cycloid_height {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    cycloidY R θ = 2 * R - cycloidArc R θ ^ 2 / (8 * R) := by
  have hcos : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
    rw [show θ = 2 * (θ / 2) by ring, cos_two_mul]; ring_nf
  simp only [cycloidY, cycloidArc]
  rw [hcos]
  field_simp
  ring

/-- **Tautochrone**: a bead of mass `m` sliding under gravity `g` on the cycloid, described by
its arc length `s` with the natural Lagrangian `½ m ṡ² - U(s)`, `U(s) = m g s²/(8R)` (the
potential `-m g y` up to a constant, by `cycloid_height`), oscillates with period
`2π/√(g/(4R))`, independently of the amplitude. -/
theorem tautochrone {m g R : ℝ} (hm : 0 < m) (hg : 0 < g) (hR : 0 < R) (γ : Motion)
    (hEL : (natural m (fun s => m * g * s ^ 2 / (8 * R)) (fun s => m * g * s / (4 * R))
      (fun s => by
        have h := ((hasDerivAt_pow 2 s).const_mul (m * g)).div_const (8 * R)
        convert h using 1
        field_simp
        ring)).EulerLagrange γ) (t : ℝ) :
    γ.q (t + 2 * π / √(g / (4 * R))) = γ.q t := by
  have hN := (natural_EL_iff _ _ _ _ γ).mp hEL
  let H : Harmonic :=
    { m := m, c := 0, k := m * g / (4 * R), m_pos := hm, c_nonneg := le_rfl,
      k_pos := by positivity, x := γ.q, v := γ.v, a := γ.a, hasDerivAt_x := γ.hasDerivAt_q,
      hasDerivAt_v := γ.hasDerivAt_v,
      eq := fun t => by
        show m * γ.a t + 0 * γ.v t + m * g / (4 * R) * γ.q t = 0
        linear_combination hN t,
      c_eq := rfl }
  have hω : H.ω = √(g / (4 * R)) := by
    simp only [Harmonic.ω, H]
    congr 1
    field_simp
  have := H.periodic t
  rwa [hω] at this

end ClassicalMechanics
