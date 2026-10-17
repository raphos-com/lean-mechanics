import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cables and arches

A perfectly flexible cable carries no bending moment; its equilibrium under vertical loads is
governed by a constant horizontal tension component `H`. We measure the cable ordinate `y(x)`
**downward** from the chord joining the supports (so the sag is positive). Under a vertical load
`q(x)` per unit horizontal length, vertical equilibrium of a cable element reads
`H y'' = -q` ([Irvine1981], §1.2; [TimoshenkoYoung1965], §2.1).

## Main results

**(a) Parabolic cable** (uniform load `q` per horizontal length, span `L`, sag `f`):
* `parabolicCable_equilibrium_iff`: the parabola `y = 4 f x (L - x) / L²` satisfies `H y'' = -q`
  iff `H = q L² / (8 f)`.
* `parabolicCable_tension_support`: the tension at the supports is
  `T_max = H √(1 + y'(0)²) = √(H² + (q L / 2)²)`.
* `parabolicCable_tension_le_support`: the tension `H √(1 + y'²)` on `[0, L]` is maximal at the
  supports.
* `parabolicCable_length_bounds`: the arc length `∫₀ᴸ √(1 + y'²)` satisfies
  `L ≤ ℓ ≤ L (1 + 8 f² / (3 L²))`.

**(b) Catenary** (self-weight `w` per unit arc length, `a = H / w`, ordinate measured upward
from the directrix):
* `catenary_equilibrium`: `y = a cosh (x / a)` satisfies `H y'' = w √(1 + y'²)`.
* `catenary_tension`: the tension `T = H √(1 + y'²) = H cosh (x / a) = w y`.
* `catenary_arcLength_hasDerivAt`: `s = a sinh (x / a)` has `ds/dx = √(1 + y'²)`.
* `catenary_ge_parabola`: the catenary lies above the osculating parabola at the vertex,
  `a cosh (x / a) ≥ a + x² / (2 a)` (from `cosh u ≥ 1 + u² / 2`, `one_add_sq_div_two_le_cosh`).

**(c) Arches** (ordinate measured upward, simply supported beam moment `M₀`):
* `archMoment`: `M(x) = M₀(x) - H y(x)`.
* `parabolicArch_funicular`: the parabolic arch under uniform load with `H = q L² / (8 f)` has
  `M ≡ 0`.
* `threeHinged_thrust`: for any arch with crown rise `y(L/2) = f`, the crown hinge condition
  `M(L/2) = 0` forces `H = M₀(L/2) / f`; for uniform load `threeHinged_thrust_uniform` gives
  `H = q L² / (8 f)`.

## References

* [Irvine1981] H. M. Irvine, *Cable Structures*, MIT Press, 1981, Ch. 1.
* [TimoshenkoYoung1965] S. P. Timoshenko, D. H. Young, *Theory of Structures*, 2nd ed., Ch. 2, 3.
-/

open Real Set intervalIntegral

namespace ContinuumMechanics.Structures

/-! ### (a) The parabolic cable -/

/-- The **parabolic cable profile** `y(x) = 4 f x (L - x) / L²` (measured downward), with
`y(0) = y(L) = 0` and sag `y(L/2) = f`. -/
noncomputable def parabolicCable (f L : ℝ) (x : ℝ) : ℝ := 4 * f * x * (L - x) / L ^ 2

/-- The parabolic cable vanishes at the supports and has sag `f` at mid-span. -/
theorem parabolicCable_values (f L : ℝ) (hL : L ≠ 0) :
    parabolicCable f L 0 = 0 ∧ parabolicCable f L L = 0 ∧ parabolicCable f L (L / 2) = f := by
  refine ⟨by simp [parabolicCable], by simp [parabolicCable], ?_⟩
  simp only [parabolicCable]
  field_simp
  ring

/-- The slope of the parabolic cable, `y'(x) = 4 f (L - 2 x) / L²`. -/
noncomputable def parabolicCableSlope (f L : ℝ) (x : ℝ) : ℝ := 4 * f * (L - 2 * x) / L ^ 2

/-- `y'(x) = 4 f (L - 2 x) / L²`. -/
theorem parabolicCable_hasDerivAt (f L x : ℝ) :
    HasDerivAt (parabolicCable f L) (parabolicCableSlope f L x) x := by
  have h := (((hasDerivAt_id' x).const_mul (4 * f)).mul
    ((hasDerivAt_const x L).sub (hasDerivAt_id' x))).div_const (L ^ 2)
  convert h using 1
  · funext y; simp [parabolicCable]
  · simp only [parabolicCableSlope, Pi.sub_apply]; ring

/-- The slope is affine with derivative `-8 f / L²`. -/
theorem parabolicCableSlope_hasDerivAt (f L x : ℝ) :
    HasDerivAt (parabolicCableSlope f L) (-(8 * f / L ^ 2)) x := by
  have h := (((hasDerivAt_const x L).sub ((hasDerivAt_id' x).const_mul 2)).const_mul
    (4 * f)).div_const (L ^ 2)
  convert h using 1
  · funext y; simp [parabolicCableSlope]
  · ring

/-- `y'' = -8 f / L²` for the parabolic cable. -/
theorem parabolicCable_deriv_deriv (f L x : ℝ) :
    deriv (deriv (parabolicCable f L)) x = -(8 * f / L ^ 2) := by
  have e : deriv (parabolicCable f L) = parabolicCableSlope f L :=
    funext fun y => (parabolicCable_hasDerivAt f L y).deriv
  rw [e, (parabolicCableSlope_hasDerivAt f L x).deriv]

/-- **Cable equilibrium** under a vertical load `q` per horizontal length with horizontal tension
`H` (ordinate measured downward): `H y'' = -q` on `[0, L]`. [Irvine1981], §1.2. -/
def CableEquilibrium (H L : ℝ) (q y : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc 0 L, H * deriv (deriv y) x = -q x

/-- **Parabolic cable**: under a uniform load `q`, the parabola `y = 4 f x (L - x) / L²` is in
equilibrium iff the horizontal tension is `H = q L² / (8 f)`. -/
theorem parabolicCable_equilibrium_iff {f L : ℝ} (hf : f ≠ 0) (hL : 0 < L) (H q : ℝ) :
    CableEquilibrium H L (fun _ => q) (parabolicCable f L) ↔ H = q * L ^ 2 / (8 * f) := by
  have hL0 : L ≠ 0 := hL.ne'
  have key : H * -(8 * f / L ^ 2) = -q ↔ H = q * L ^ 2 / (8 * f) := by
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; subst h; field_simp
  constructor
  · intro h
    have := h 0 ⟨le_rfl, hL.le⟩
    rw [parabolicCable_deriv_deriv] at this
    exact key.1 this
  · intro h x _
    rw [parabolicCable_deriv_deriv]
    exact key.2 h

/-- The cable tension `T = H √(1 + y'²)` (the horizontal component `H` is constant along the
cable, the vertical component is `H y'`). -/
noncomputable def cableTension (H slope : ℝ) : ℝ := H * √(1 + slope ^ 2)

/-- `T = √(H² + (H y')²)` for `H ≥ 0`. -/
theorem cableTension_eq_sqrt {H : ℝ} (hH : 0 ≤ H) (s : ℝ) :
    cableTension H s = √(H ^ 2 + (H * s) ^ 2) := by
  rw [cableTension, show H ^ 2 + (H * s) ^ 2 = H ^ 2 * (1 + s ^ 2) by ring, sqrt_mul (sq_nonneg _),
    sqrt_sq hH]

/-- **Tension at the supports** of the parabolic cable with `H = q L² / (8 f)`:
`T_max = √(H² + (q L / 2)²)` (the vertical reaction is half the total load `q L`). -/
theorem parabolicCable_tension_support {f L q : ℝ} (hf : 0 < f) (hL : 0 < L) (hq : 0 ≤ q) :
    let H := q * L ^ 2 / (8 * f)
    cableTension H (parabolicCableSlope f L 0) = √(H ^ 2 + (q * L / 2) ^ 2) ∧
      cableTension H (parabolicCableSlope f L L) = √(H ^ 2 + (q * L / 2) ^ 2) := by
  intro H
  have hH : 0 ≤ H := by positivity
  have h0 : H * parabolicCableSlope f L 0 = q * L / 2 := by
    simp only [H, parabolicCableSlope]; field_simp; ring
  have h1 : (H * parabolicCableSlope f L L) ^ 2 = (q * L / 2) ^ 2 := by
    simp only [H, parabolicCableSlope]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [cableTension_eq_sqrt hH, h0]
  · rw [cableTension_eq_sqrt hH, h1]

/-- **The tension is maximal at the supports**: on `[0, L]`, `|y'(x)| ≤ |y'(0)|`, so
`T(x) ≤ T(0)`. -/
theorem parabolicCable_tension_le_support {f L H : ℝ} (hL : 0 < L) (hH : 0 ≤ H) {x : ℝ}
    (hx : x ∈ Icc 0 L) :
    cableTension H (parabolicCableSlope f L x) ≤ cableTension H (parabolicCableSlope f L 0) := by
  unfold cableTension
  apply mul_le_mul_of_nonneg_left _ hH
  apply sqrt_le_sqrt
  have hsq : (L - 2 * x) ^ 2 ≤ L ^ 2 := by nlinarith [hx.1, hx.2]
  have e : ∀ y, parabolicCableSlope f L y ^ 2 = 16 * f ^ 2 / L ^ 4 * (L - 2 * y) ^ 2 := by
    intro y; simp only [parabolicCableSlope]; field_simp; ring
  rw [e, e]
  have : 0 ≤ 16 * f ^ 2 / L ^ 4 := by positivity
  nlinarith

/-- The **arc length** `ℓ = ∫₀ᴸ √(1 + y'²) dx` of the parabolic cable. -/
noncomputable def parabolicCableLength (f L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, √(1 + parabolicCableSlope f L x ^ 2)

/-- `∫₀ᴸ (1 + y'²/2) dx = L + 8 f² / (3 L)` for the parabolic cable. -/
theorem integral_one_add_slope_sq_half {f L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, (1 + parabolicCableSlope f L x ^ 2 / 2) =
      L * (1 + 8 * f ^ 2 / (3 * L ^ 2)) := by
  have hL0 : L ≠ 0 := hL.ne'
  let F : ℝ → ℝ := fun x => x - 4 * f ^ 2 * (L - 2 * x) ^ 3 / (3 * L ^ 4)
  have hF : ∀ x ∈ uIcc 0 L, HasDerivAt F (1 + parabolicCableSlope f L x ^ 2 / 2) x := by
    intro x _
    have h := (hasDerivAt_id' x).sub ((((hasDerivAt_const x L).sub
      ((hasDerivAt_id' x).const_mul 2)).pow 3).const_mul (4 * f ^ 2) |>.div_const (3 * L ^ 4))
    convert h using 1
    simp only [parabolicCableSlope, Pi.sub_apply]
    field_simp
    ring
  have hcont : Continuous fun x => 1 + parabolicCableSlope f L x ^ 2 / 2 := by
    unfold parabolicCableSlope; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]
  simp only [F]
  field_simp
  ring

/-- **Length of the parabolic cable**: `L ≤ ℓ ≤ L (1 + 8 f² / (3 L²))`, the upper bound being the
classical second-order approximation (from `√(1 + t) ≤ 1 + t/2`). -/
theorem parabolicCable_length_bounds {f L : ℝ} (hL : 0 < L) :
    L ≤ parabolicCableLength f L ∧
      parabolicCableLength f L ≤ L * (1 + 8 * f ^ 2 / (3 * L ^ 2)) := by
  have hc : Continuous fun x => √(1 + parabolicCableSlope f L x ^ 2) := by
    unfold parabolicCableSlope; fun_prop
  have hc2 : Continuous fun x => 1 + parabolicCableSlope f L x ^ 2 / 2 := by
    unfold parabolicCableSlope; fun_prop
  constructor
  · have h := integral_mono_on hL.le (intervalIntegrable_const (μ := MeasureTheory.volume)
      (c := (1 : ℝ))) (hc.intervalIntegrable 0 L) (fun x _ => by
        rw [one_le_sqrt]; nlinarith [sq_nonneg (parabolicCableSlope f L x)])
    simpa [parabolicCableLength] using h
  · rw [← integral_one_add_slope_sq_half (f := f) hL]
    refine integral_mono_on hL.le (hc.intervalIntegrable 0 L) (hc2.intervalIntegrable 0 L)
      fun x _ => ?_
    exact sqrt_one_add_le (by nlinarith [sq_nonneg (parabolicCableSlope f L x)])

/-! ### (b) The catenary -/

/-- The **catenary** `y(x) = a cosh (x / a)`, ordinate measured upward from the directrix. -/
noncomputable def catenary (a : ℝ) (x : ℝ) : ℝ := a * cosh (x / a)

/-- `y' = sinh (x / a)`. -/
theorem catenary_hasDerivAt {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (catenary a) (sinh (x / a)) x := by
  have h := ((hasDerivAt_id' x).div_const a).cosh.const_mul a
  convert h using 1
  · funext y; simp [catenary]
  · field_simp

/-- `y'' = cosh (x / a) / a`. -/
theorem catenary_deriv_deriv {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    deriv (deriv (catenary a)) x = cosh (x / a) / a := by
  have e : deriv (catenary a) = fun y => sinh (y / a) :=
    funext fun y => (catenary_hasDerivAt ha y).deriv
  rw [e]
  have h := ((hasDerivAt_id' x).div_const a).sinh
  rw [h.deriv]
  simp [div_eq_mul_inv, mul_comm]

/-- `√(1 + y'²) = cosh (x / a)` along the catenary. -/
theorem catenary_sqrt_one_add_slope_sq {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    √(1 + deriv (catenary a) x ^ 2) = cosh (x / a) := by
  rw [(catenary_hasDerivAt ha x).deriv, ← cosh_sq', sqrt_sq (cosh_pos _).le]

/-- **Catenary equilibrium**: with self-weight `w > 0` per unit arc length and horizontal tension
`H`, `a = H / w`, the curve `y = a cosh (x / a)` satisfies `H y'' = w √(1 + y'²)`.
[Irvine1981], §1.3. -/
theorem catenary_equilibrium {H w : ℝ} (hH : H ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    H * deriv (deriv (catenary (H / w))) x = w * √(1 + deriv (catenary (H / w)) x ^ 2) := by
  have ha : H / w ≠ 0 := div_ne_zero hH hw
  rw [catenary_deriv_deriv ha, catenary_sqrt_one_add_slope_sq ha]
  field_simp

/-- **Tension in the catenary**: `T = H √(1 + y'²) = H cosh (x / a) = w y`. -/
theorem catenary_tension {H w : ℝ} (hH : H ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    cableTension H (deriv (catenary (H / w)) x) = H * cosh (x / (H / w)) ∧
      H * cosh (x / (H / w)) = w * catenary (H / w) x := by
  have ha : H / w ≠ 0 := div_ne_zero hH hw
  refine ⟨by rw [cableTension, catenary_sqrt_one_add_slope_sq ha], ?_⟩
  simp only [catenary]
  field_simp

/-- **Arc length of the catenary** from the vertex: `s(x) = a sinh (x / a)` satisfies
`ds/dx = √(1 + y'²)`, and `s(0) = 0`. -/
theorem catenary_arcLength_hasDerivAt {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => a * sinh (y / a)) (√(1 + deriv (catenary a) x ^ 2)) x := by
  rw [catenary_sqrt_one_add_slope_sq ha]
  have h := ((hasDerivAt_id' x).div_const a).sinh.const_mul a
  convert h using 1
  field_simp

/-- The arc length of the catenary from the vertex to `x` is `a sinh (x / a)`. -/
theorem catenary_arcLength {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, √(1 + deriv (catenary a) t ^ 2) = a * sinh (x / a) := by
  have hc : Continuous fun t => √(1 + deriv (catenary a) t ^ 2) := by
    have e : (fun t => √(1 + deriv (catenary a) t ^ 2)) = fun t => cosh (t / a) :=
      funext (catenary_sqrt_one_add_slope_sq ha)
    rw [e]; fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => catenary_arcLength_hasDerivAt ha t)
    (hc.intervalIntegrable _ _)]
  simp

/-- `u² ≤ sinh² u`. -/
theorem sq_le_sinh_sq (u : ℝ) : u ^ 2 ≤ sinh u ^ 2 := by
  have h : |u| ≤ |sinh u| := by rw [abs_sinh]; exact self_le_sinh_iff.2 (abs_nonneg u)
  rw [← sq_abs u, ← sq_abs (sinh u)]
  exact pow_le_pow_left₀ (abs_nonneg u) h 2

/-- `cosh u ≥ 1 + u² / 2` (via `cosh u = 1 + 2 sinh² (u/2)` and `|sinh v| ≥ |v|`). -/
theorem one_add_sq_div_two_le_cosh (u : ℝ) : 1 + u ^ 2 / 2 ≤ cosh u := by
  have e : cosh u = 1 + 2 * sinh (u / 2) ^ 2 := by
    have h := cosh_two_mul (u / 2)
    rw [show 2 * (u / 2) = u by ring, cosh_sq] at h
    linarith
  have := sq_le_sinh_sq (u / 2)
  rw [e]
  nlinarith

/-- **Catenary versus parabola**: the catenary `a cosh (x / a)` lies above the parabola
`a + x² / (2 a)` with the same vertex and the same vertex curvature `1 / a`. -/
theorem catenary_ge_parabola {a : ℝ} (ha : 0 < a) (x : ℝ) :
    a + x ^ 2 / (2 * a) ≤ catenary a x := by
  have h := one_add_sq_div_two_le_cosh (x / a)
  have e : a + x ^ 2 / (2 * a) = a * (1 + (x / a) ^ 2 / 2) := by field_simp
  rw [e, catenary]
  exact mul_le_mul_of_nonneg_left h ha.le

/-- The comparison parabola `a + x² / (2 a)` has curvature `y'' = 1 / a`, equal to the vertex
curvature `cosh 0 / a` of the catenary. -/
theorem catenary_vertex_curvature {a : ℝ} (ha : a ≠ 0) :
    deriv (deriv (catenary a)) 0 = 1 / a := by
  rw [catenary_deriv_deriv ha]; simp

/-! ### (c) Arches -/

/-- The **simply supported beam moment** under a uniform load `q` on span `L`:
`M₀(x) = q x (L - x) / 2`. -/
noncomputable def beamMomentUniform (q L : ℝ) (x : ℝ) : ℝ := q * x * (L - x) / 2

/-- The **arch bending moment** `M(x) = M₀(x) - H y(x)`: the simply supported beam moment `M₀`
reduced by the moment of the horizontal thrust `H` about a point of the axis `y` (ordinate
measured upward from the springing line). [TimoshenkoYoung1965], §3.1. -/
def archMoment (M₀ y : ℝ → ℝ) (H : ℝ) (x : ℝ) : ℝ := M₀ x - H * y x

/-- **The parabolic arch is funicular for a uniform load**: with `y = 4 f x (L - x) / L²` and
`H = q L² / (8 f)`, the bending moment vanishes identically. -/
theorem parabolicArch_funicular {f L : ℝ} (hf : f ≠ 0) (hL : L ≠ 0) (q x : ℝ) :
    archMoment (beamMomentUniform q L) (parabolicCable f L) (q * L ^ 2 / (8 * f)) x = 0 := by
  simp only [archMoment, beamMomentUniform, parabolicCable]
  field_simp
  ring

/-- **Three-hinged arch**: if the crown hinge is at `x = L/2` with rise `y(L/2) = f ≠ 0`, the
condition `M(L/2) = 0` determines the thrust `H = M₀(L/2) / f`. -/
theorem threeHinged_thrust {M₀ y : ℝ → ℝ} {H f L : ℝ} (hf : f ≠ 0) (hy : y (L / 2) = f)
    (hM : archMoment M₀ y H (L / 2) = 0) : H = M₀ (L / 2) / f := by
  simp only [archMoment, hy] at hM
  field_simp
  linarith

/-- **Three-hinged arch under uniform load**: the thrust is `H = q L² / (8 f)`, for any arch
axis with rise `f` at the crown hinge. -/
theorem threeHinged_thrust_uniform {y : ℝ → ℝ} {H f L q : ℝ} (hf : f ≠ 0) (hy : y (L / 2) = f)
    (hM : archMoment (beamMomentUniform q L) y H (L / 2) = 0) : H = q * L ^ 2 / (8 * f) := by
  rw [threeHinged_thrust hf hy hM, beamMomentUniform]
  field_simp
  ring

/-- **Three-hinged parabolic arch**: the crown-hinge thrust makes the parabolic three-hinged arch
moment-free along its whole span under uniform load. -/
theorem threeHinged_parabolic_moment_zero {f L q H : ℝ} (hf : f ≠ 0) (hL : L ≠ 0)
    (hM : archMoment (beamMomentUniform q L) (parabolicCable f L) H (L / 2) = 0) (x : ℝ) :
    archMoment (beamMomentUniform q L) (parabolicCable f L) H x = 0 := by
  rw [threeHinged_thrust_uniform hf (parabolicCable_values f L hL).2.2 hM]
  exact parabolicArch_funicular hf hL q x

end ContinuumMechanics.Structures
