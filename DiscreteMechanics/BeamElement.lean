import ContinuumMechanics.Beams.EulerBernoulli.Solutions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Euler–Bernoulli beam element

The classical two-node beam finite element of matrix structural analysis. An element of length
`L` and bending stiffness `EI` has four degrees of freedom, the **nodal values**
`d = (w(0), w'(0), w(L), w'(L))` (`nodalValues`). The deflection inside the element is
interpolated by the cubic **Hermite shape functions** (`ξ = x / L`)

* `N₁ = 1 - 3ξ² + 2ξ³`, `N₂ = L (ξ - 2ξ² + ξ³)`, `N₃ = 3ξ² - 2ξ³`, `N₄ = L (-ξ² + ξ³)`,

and the **element stiffness matrix** is `k_ij = ∫₀ᴸ EI Nᵢ'' Nⱼ'' dx`, i.e.

`k = (EI / L³) [[12, 6L, -12, 6L], [6L, 4L², -6L, 2L²], [-12, -6L, 12, -6L], [6L, 2L², -6L, 4L²]]`.

Shape functions are polynomials (`x ↦ p.eval x`), so all derivatives are formal derivatives
(`ContinuumMechanics.Beams.iteratedDeriv_eval`) and all integrals are integrals of monomials.

Sign convention: `k d = f` with `f = (F₁, M₁, F₂, M₂)` the nodal forces and moments, positive in
the direction of the corresponding degree of freedom. For a cubic `w` (no distributed load)
`f = (EI w'''(0), -EI w''(0), -EI w'''(L), EI w''(L))`.

## Main results

* `hermite_apply`: the shape functions in the variable `ξ = x / L`.
* `nodalValues_hermite`: the **Kronecker property** `dⱼ(Nᵢ) = δᵢⱼ`.
* `cubic_eq_sum_hermite`: every cubic is reproduced exactly, `p = Σᵢ dᵢ(p) Nᵢ`.
* `nodalValues_interp`: the interpolant `Σᵢ vᵢ Nᵢ` has nodal values `v`.
* `beamStiffness_eq_integral`: `k_ij = ∫₀ᴸ EI Nᵢ'' Nⱼ'' dx`.
* `beamStiffness_isSymm`, `beamStiffness_isHermitian`: `k` is symmetric.
* `dotProduct_beamStiffness_mulVec`: the strain energy `vᵀ k v = ∫₀ᴸ EI (w'')² dx` of the
  interpolated deflection `w = Σᵢ vᵢ Nᵢ`.
* `beamStiffness_posSemidef`: `k` is positive semidefinite.
* `beamStiffness_mulVec_eq_zero_iff`: `ker k` is spanned by the rigid-body modes, the
  translation `(1, 0, 1, 0)` and the rotation `(0, 1, L, 1)`.
* `beamStiffness_mulVec_nodalValues_cubic`: **exactness** for cubic deflections: `k d` is the
  vector of exact end shear forces and bending moments.
* `consistentLoad_eq_integral`: the consistent load vector of a uniform load `q`,
  `∫₀ᴸ q Nᵢ dx = qL (1/2, L/12, 1/2, -L/12)`.
* `fixedEnd_moments`, `fixedEnd_reactions_eq_exact`: with all four degrees of freedom fixed the
  reactions are `-f`, giving the classical fixed-end moments `∓ qL²/12`; they coincide with the
  end forces of the exact clamped–clamped solution (`clampedUniform_solves`).
* `cantilever_solve`, `cantilever_oneElement`: a cantilever modelled by one element, clamped at
  node 1 with tip load `P`: the reduced `2 × 2` system gives tip deflection `PL³/(3EI)` and tip
  rotation `PL²/(2EI)`; `cantilever_oneElement_exact`: these are the nodal values of the exact
  solution `EBBeam.cantileverTip`.

## References

* [Przemieniecki1968] J. S. Przemieniecki, *Theory of Matrix Structural Analysis*,
  McGraw–Hill (1968), Ch. 5.
* [Hughes2000] T. J. R. Hughes, *The Finite Element Method*, Dover (2000), §1.16.
* [Reddy2006] J. N. Reddy, *An Introduction to the Finite Element Method*, 3rd ed.,
  McGraw–Hill (2006), §5.2.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, App. G.
-/

open Polynomial intervalIntegral Matrix
open ContinuumMechanics.Beams (EBBeam)

namespace DiscreteMechanics.BeamElement

/-- The integral of a cubic over `[0, L]`. -/
theorem integral_cubic (L c₀ c₁ c₂ c₃ : ℝ) :
    ∫ x in (0 : ℝ)..L, (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) =
      c₀ * L + c₁ * L ^ 2 / 2 + c₂ * L ^ 3 / 3 + c₃ * L ^ 4 / 4 := by
  have hc : ∀ (c : ℝ) (n : ℕ),
      IntervalIntegrable (fun x : ℝ => c * x ^ n) MeasureTheory.volume 0 L :=
    fun c n => (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
  have h₁ : IntervalIntegrable (fun x : ℝ => c₁ * x) MeasureTheory.volume 0 L := by
    simpa using hc c₁ 1
  rw [integral_add ((intervalIntegrable_const.add h₁).add (hc c₂ 2)) (hc c₃ 3),
    integral_add (intervalIntegrable_const.add h₁) (hc c₂ 2),
    integral_add intervalIntegrable_const h₁]
  have h1 : ∫ x in (0 : ℝ)..L, c₁ * x = c₁ * (L ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  simp [integral_const_mul, integral_pow, h1]
  ring

/-- The integral of a product of two affine functions over `[0, L]`. -/
theorem integral_linear_mul_linear (L a b c d : ℝ) :
    ∫ x in (0 : ℝ)..L, (a + b * x) * (c + d * x) =
      a * c * L + (a * d + b * c) * L ^ 2 / 2 + b * d * L ^ 3 / 3 := by
  have := integral_cubic L (a * c) (a * d + b * c) (b * d) 0
  simp only [zero_mul, add_zero, zero_div] at this
  rw [← this]
  congr 1; ext x; ring

/-- The four cubic **Hermite shape functions** of an element of length `L`, as polynomials in
`x ∈ [0, L]`: `N₁ = 1 - 3ξ² + 2ξ³`, `N₂ = L (ξ - 2ξ² + ξ³)`, `N₃ = 3ξ² - 2ξ³`,
`N₄ = L (-ξ² + ξ³)` with `ξ = x / L`. [Przemieniecki1968], §5.3. -/
noncomputable def hermitePoly (L : ℝ) : Fin 4 → ℝ[X] :=
  ![1 - C (3 / L ^ 2) * X ^ 2 + C (2 / L ^ 3) * X ^ 3,
    X - C (2 / L) * X ^ 2 + C (1 / L ^ 2) * X ^ 3,
    C (3 / L ^ 2) * X ^ 2 - C (2 / L ^ 3) * X ^ 3,
    - C (1 / L) * X ^ 2 + C (1 / L ^ 2) * X ^ 3]

/-- The Hermite shape function `Nᵢ` as a function `ℝ → ℝ`. -/
noncomputable def hermite (L : ℝ) (i : Fin 4) : ℝ → ℝ := fun x => (hermitePoly L i).eval x

/-- Constant term of the curvature `Nᵢ'' = curvA L i + curvB L i * x`. -/
noncomputable def curvA (L : ℝ) : Fin 4 → ℝ := ![-6 / L ^ 2, -4 / L, 6 / L ^ 2, -2 / L]
/-- Linear coefficient of the curvature `Nᵢ'' = curvA L i + curvB L i * x`. -/
noncomputable def curvB (L : ℝ) : Fin 4 → ℝ :=
  ![12 / L ^ 3, 6 / L ^ 2, -12 / L ^ 3, 6 / L ^ 2]

/-- The shape functions written in the dimensionless coordinate `ξ = x / L`. -/
theorem hermite_apply (L : ℝ) (hL : L ≠ 0) (x : ℝ) :
    hermite L 0 x = 1 - 3 * (x / L) ^ 2 + 2 * (x / L) ^ 3 ∧
    hermite L 1 x = L * (x / L - 2 * (x / L) ^ 2 + (x / L) ^ 3) ∧
    hermite L 2 x = 3 * (x / L) ^ 2 - 2 * (x / L) ^ 3 ∧
    hermite L 3 x = L * (-(x / L) ^ 2 + (x / L) ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hermite, hermitePoly] <;> field_simp

/-- The curvatures `Nᵢ''` of the shape functions are affine in `x`. -/
theorem iteratedDeriv_two_hermite (L : ℝ) (hL : L ≠ 0) (i : Fin 4) (x : ℝ) :
    iteratedDeriv 2 (hermite L i) x = curvA L i + curvB L i * x := by
  unfold hermite
  rw [ContinuumMechanics.Beams.iteratedDeriv_eval]
  fin_cases i <;> simp [hermitePoly, curvA, curvB, derivative_mul, derivative_pow,
    Function.iterate_succ] <;> field_simp <;> ring

/-- The four **nodal degrees of freedom** of a deflection `w` on `[0, L]`: end deflections and
end slopes, `(w(0), w'(0), w(L), w'(L))`. -/
noncomputable def nodalValues (L : ℝ) (w : ℝ → ℝ) : Fin 4 → ℝ :=
  ![w 0, deriv w 0, w L, deriv w L]

/-- **Kronecker property** of the Hermite shape functions: the `j`-th nodal value of `Nᵢ` is
`δᵢⱼ` (e.g. `N₁(0) = 1`, `N₁'(0) = N₁(L) = N₁'(L) = 0`). -/
theorem nodalValues_hermite (L : ℝ) (hL : L ≠ 0) (i j : Fin 4) :
    nodalValues L (hermite L i) j = if i = j then 1 else 0 := by
  unfold hermite
  simp only [nodalValues, ContinuumMechanics.Beams.deriv_eval]
  fin_cases i <;> fin_cases j <;> simp [hermitePoly, derivative_mul, derivative_pow] <;>
    field_simp <;> ring

/-- A polynomial of degree at most three is `a + b X + c X² + d X³`. -/
theorem exists_cubic {p : ℝ[X]} (hp : p.natDegree ≤ 3) :
    ∃ a b c d : ℝ, p = C a + C b * X + C c * X ^ 2 + C d * X ^ 3 := by
  refine ⟨p.coeff 0, p.coeff 1, p.coeff 2, p.coeff 3, ?_⟩
  conv_lhs => rw [p.as_sum_range' 4 (by omega)]
  simp [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]

/-- **Cubics are reproduced exactly**: every polynomial `p` of degree `≤ 3` equals the
Hermite interpolant of its end values and end slopes, `p = Σᵢ dᵢ(p) Nᵢ`. -/
theorem cubic_eq_sum_hermite (L : ℝ) (hL : L ≠ 0) {p : ℝ[X]} (hp : p.natDegree ≤ 3)
    (x : ℝ) :
    p.eval x = ∑ i, nodalValues L (fun y => p.eval y) i * hermite L i x := by
  simp only [Fin.sum_univ_four, nodalValues, ContinuumMechanics.Beams.deriv_eval]
  obtain ⟨a, b, c, d, rfl⟩ := exists_cubic hp
  simp [hermite, hermitePoly, derivative_mul, derivative_pow]
  field_simp
  ring

/-- The Hermite interpolant `Σᵢ vᵢ Nᵢ` of nodal values `v`, as a polynomial. -/
noncomputable def interpPoly (L : ℝ) (v : Fin 4 → ℝ) : ℝ[X] :=
  ∑ i, C (v i) * hermitePoly L i
/-- The Hermite interpolant `w = Σᵢ vᵢ Nᵢ` of nodal values `v`. -/
noncomputable def interp (L : ℝ) (v : Fin 4 → ℝ) : ℝ → ℝ :=
  fun x => (interpPoly L v).eval x

/-- The interpolant is the combination `Σᵢ vᵢ Nᵢ(x)` of the shape functions. -/
theorem interp_apply (L : ℝ) (v : Fin 4 → ℝ) (x : ℝ) :
    interp L v x = ∑ i, v i * hermite L i x := by
  simp [interp, interpPoly, eval_finsetSum, hermite]

/-- The interpolant of nodal values `v` has nodal values `v`. -/
theorem nodalValues_interp (L : ℝ) (hL : L ≠ 0) (v : Fin 4 → ℝ) :
    nodalValues L (interp L v) = v := by
  ext j
  rw [show interp L v = fun x => (interpPoly L v).eval x from rfl]
  simp only [nodalValues, ContinuumMechanics.Beams.deriv_eval]
  fin_cases j <;>
    simp [interpPoly, Fin.sum_univ_four, hermitePoly, derivative_mul, derivative_pow] <;>
    field_simp <;> ring

/-- Curvature of the interpolant: `w'' = Σᵢ vᵢ Nᵢ''`. -/
theorem iteratedDeriv_two_interp (L : ℝ) (hL : L ≠ 0) (v : Fin 4 → ℝ) (x : ℝ) :
    iteratedDeriv 2 (interp L v) x = ∑ i, v i * (curvA L i + curvB L i * x) := by
  unfold interp interpPoly
  rw [ContinuumMechanics.Beams.iteratedDeriv_eval]
  simp [Fin.sum_univ_four, hermitePoly, curvA, curvB, derivative_mul, derivative_pow,
    Function.iterate_succ]
  field_simp
  ring

/-- The **element stiffness matrix** of an Euler–Bernoulli beam element with bending stiffness
`EI` and length `L`, for the degrees of freedom `(w(0), w'(0), w(L), w'(L))`.
[Przemieniecki1968], Ch. 5. -/
noncomputable def beamStiffness (EI L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (EI / L ^ 3) • !![12, 6 * L, -12, 6 * L; 6 * L, 4 * L ^ 2, -6 * L, 2 * L ^ 2;
    -12, -6 * L, 12, -6 * L; 6 * L, 2 * L ^ 2, -6 * L, 4 * L ^ 2]

/-- The stiffness matrix is the Galerkin matrix of the bending energy:
`k_ij = ∫₀ᴸ EI Nᵢ'' Nⱼ'' dx`. -/
theorem beamStiffness_eq_integral (EI L : ℝ) (hL : L ≠ 0) (i j : Fin 4) :
    beamStiffness EI L i j =
      ∫ x in (0 : ℝ)..L,
        EI * iteratedDeriv 2 (hermite L i) x * iteratedDeriv 2 (hermite L j) x := by
  simp_rw [iteratedDeriv_two_hermite L hL, mul_assoc, intervalIntegral.integral_const_mul,
    integral_linear_mul_linear]
  fin_cases i <;> fin_cases j <;> simp [beamStiffness, curvA, curvB] <;> field_simp <;> ring

/-- The element stiffness matrix is **symmetric**. -/
theorem beamStiffness_isSymm (EI L : ℝ) : (beamStiffness EI L).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beamStiffness]

/-- **Strain energy**: `vᵀ k v = ∫₀ᴸ EI (w'')² dx` for the interpolated deflection
`w = Σᵢ vᵢ Nᵢ`. -/
theorem dotProduct_beamStiffness_mulVec (EI L : ℝ) (hL : L ≠ 0) (v : Fin 4 → ℝ) :
    v ⬝ᵥ (beamStiffness EI L *ᵥ v) =
      ∫ x in (0 : ℝ)..L, EI * iteratedDeriv 2 (interp L v) x ^ 2 := by
  have h : ∀ x, iteratedDeriv 2 (interp L v) x =
      (∑ i, v i * curvA L i) + (∑ i, v i * curvB L i) * x := by
    intro x
    rw [iteratedDeriv_two_interp L hL, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h, sq, intervalIntegral.integral_const_mul, integral_linear_mul_linear]
  simp [dotProduct, mulVec, Fin.sum_univ_four, beamStiffness, curvA, curvB]
  field_simp
  ring

/-- The element stiffness matrix is Hermitian (symmetric, over `ℝ`). -/
theorem beamStiffness_isHermitian (EI L : ℝ) : (beamStiffness EI L).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact beamStiffness_isSymm EI L

/-- The element stiffness matrix is **positive semidefinite** for `EI ≥ 0`, `L > 0`, since
`vᵀ k v = ∫₀ᴸ EI (w'')² dx ≥ 0`. -/
theorem beamStiffness_posSemidef {EI L : ℝ} (hEI : 0 ≤ EI) (hL : 0 < L) :
    (beamStiffness EI L).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (beamStiffness_isHermitian EI L) fun v => ?_
  rw [star_trivial, dotProduct_beamStiffness_mulVec EI L hL.ne']
  exact intervalIntegral.integral_nonneg hL.le fun x _ => mul_nonneg hEI (sq_nonneg _)

/-- The nodal forces `k v` written out componentwise. -/
theorem beamStiffness_mulVec (EI L : ℝ) (v : Fin 4 → ℝ) :
    beamStiffness EI L *ᵥ v =
      ![EI / L ^ 3 * (12 * v 0 + 6 * L * v 1 - 12 * v 2 + 6 * L * v 3),
        EI / L ^ 3 * (6 * L * v 0 + 4 * L ^ 2 * v 1 - 6 * L * v 2 + 2 * L ^ 2 * v 3),
        EI / L ^ 3 * (-12 * v 0 - 6 * L * v 1 + 12 * v 2 - 6 * L * v 3),
        EI / L ^ 3 * (6 * L * v 0 + 2 * L ^ 2 * v 1 - 6 * L * v 2 + 4 * L ^ 2 * v 3)] := by
  ext i
  fin_cases i <;> simp [beamStiffness, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The rigid-body **translation** `w = 1`: nodal values `(1, 0, 1, 0)`. -/
def translationMode : Fin 4 → ℝ := ![1, 0, 1, 0]
/-- The rigid-body **rotation** `w = x`: nodal values `(0, 1, L, 1)`. -/
def rotationMode (L : ℝ) : Fin 4 → ℝ := ![0, 1, L, 1]

/-- A rigid translation produces no nodal forces. -/
theorem beamStiffness_mulVec_translationMode (EI L : ℝ) :
    beamStiffness EI L *ᵥ translationMode = 0 := by
  ext i
  fin_cases i <;> simp [beamStiffness, translationMode, mulVec, dotProduct, Fin.sum_univ_four]

/-- A rigid rotation produces no nodal forces. -/
theorem beamStiffness_mulVec_rotationMode (EI L : ℝ) :
    beamStiffness EI L *ᵥ rotationMode L = 0 := by
  ext i
  fin_cases i <;> simp [beamStiffness, rotationMode, mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring

/-- **Kernel of the element stiffness matrix**: `k v = 0` iff `v` is a rigid-body motion, a
combination of the translation `(1, 0, 1, 0)` and the rotation `(0, 1, L, 1)`. -/
theorem beamStiffness_mulVec_eq_zero_iff {EI L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0)
    (v : Fin 4 → ℝ) :
    beamStiffness EI L *ᵥ v = 0 ↔ ∃ a θ : ℝ, v = a • translationMode + θ • rotationMode L := by
  constructor
  · intro h
    rw [beamStiffness_mulVec] at h
    have h0 : EI / L ^ 3 * (12 * v 0 + 6 * L * v 1 - 12 * v 2 + 6 * L * v 3) = 0 :=
      congrFun h 0
    have h1 : EI / L ^ 3 * (6 * L * v 0 + 4 * L ^ 2 * v 1 - 6 * L * v 2 + 2 * L ^ 2 * v 3) = 0 :=
      congrFun h 1
    have hc : EI / L ^ 3 ≠ 0 := div_ne_zero hEI (pow_ne_zero 3 hL)
    have h0' : 12 * v 0 + 6 * L * v 1 - 12 * v 2 + 6 * L * v 3 = 0 :=
      (mul_eq_zero.1 (by linear_combination h0)).resolve_left hc
    have h1' : 6 * L * v 0 + 4 * L ^ 2 * v 1 - 6 * L * v 2 + 2 * L ^ 2 * v 3 = 0 :=
      (mul_eq_zero.1 (by linear_combination h1)).resolve_left hc
    have e2 : v 2 = v 0 + L * v 1 := by
      have := (mul_eq_zero.1 (show L * (v 0 + L * v 1 - v 2) = 0 by
        linear_combination h1' / 2 - L * h0' / 6)).resolve_left hL
      linarith
    have e3 : v 3 = v 1 := by
      have := (mul_eq_zero.1 (show L * (v 3 - v 1) = 0 by
        linear_combination h0' / 6 + 2 * e2)).resolve_left hL
      linarith
    refine ⟨v 0, v 1, ?_⟩
    ext i
    fin_cases i <;> simp [translationMode, rotationMode, e2, e3]
    ring
  · rintro ⟨a, θ, rfl⟩
    rw [mulVec_add, mulVec_smul, mulVec_smul, beamStiffness_mulVec_translationMode,
      beamStiffness_mulVec_rotationMode, smul_zero, smul_zero, add_zero]

/-- **Exactness for cubic deflections**: if `w` is a cubic (the exact solution of `EI w'''' = 0`,
no distributed load), the element equations `k d = f` with `d` the nodal values of `w` give the
exact end forces and moments `f = (EI w'''(0), -EI w''(0), -EI w'''(L), EI w''(L))`. -/
theorem beamStiffness_mulVec_nodalValues_cubic (EI L : ℝ) (hL : L ≠ 0) {p : ℝ[X]}
    (hp : p.natDegree ≤ 3) :
    beamStiffness EI L *ᵥ nodalValues L (fun x => p.eval x) =
      ![EI * iteratedDeriv 3 (fun x => p.eval x) 0,
        -(EI * iteratedDeriv 2 (fun x => p.eval x) 0),
        -(EI * iteratedDeriv 3 (fun x => p.eval x) L),
        EI * iteratedDeriv 2 (fun x => p.eval x) L] := by
  rw [beamStiffness_mulVec]
  simp only [nodalValues, ContinuumMechanics.Beams.deriv_eval,
    ContinuumMechanics.Beams.iteratedDeriv_eval]
  obtain ⟨a, b, c, d, rfl⟩ := exists_cubic hp
  ext i
  fin_cases i <;> simp [derivative_mul, Function.iterate_succ] <;> field_simp <;> ring

/-- The integral of a function that agrees with a cubic everywhere. -/
theorem integral_cubic_of_eq {f : ℝ → ℝ} (L c₀ c₁ c₂ c₃ : ℝ)
    (hf : ∀ x, f x = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) :
    ∫ x in (0 : ℝ)..L, f x =
      c₀ * L + c₁ * L ^ 2 / 2 + c₂ * L ^ 3 / 3 + c₃ * L ^ 4 / 4 := by
  rw [show f = fun x => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 from funext hf]
  exact integral_cubic L c₀ c₁ c₂ c₃

/-- The **consistent load vector** of a uniform load `q`: `qL (1/2, L/12, 1/2, -L/12)`. -/
noncomputable def consistentLoad (q L : ℝ) : Fin 4 → ℝ :=
  ![q * L / 2, q * L ^ 2 / 12, q * L / 2, -(q * L ^ 2 / 12)]

/-- The consistent load vector is `fᵢ = ∫₀ᴸ q Nᵢ dx`. -/
theorem consistentLoad_eq_integral (q L : ℝ) (hL : L ≠ 0) (i : Fin 4) :
    consistentLoad q L i = ∫ x in (0 : ℝ)..L, q * hermite L i x := by
  fin_cases i
  · rw [integral_cubic_of_eq L q 0 (-3 * q / L ^ 2) (2 * q / L ^ 3)
      fun x => by simp [hermite, hermitePoly]; field_simp; ring]
    simp [consistentLoad]; field_simp; ring
  · rw [integral_cubic_of_eq L 0 q (-2 * q / L) (q / L ^ 2)
      fun x => by simp [hermite, hermitePoly]; field_simp; ring]
    simp [consistentLoad]; field_simp; ring
  · rw [integral_cubic_of_eq L 0 0 (3 * q / L ^ 2) (-2 * q / L ^ 3)
      fun x => by simp [hermite, hermitePoly]; field_simp; ring]
    simp [consistentLoad]; field_simp; ring
  · rw [integral_cubic_of_eq L 0 0 (-q / L) (q / L ^ 2)
      fun x => by simp [hermite, hermitePoly]; field_simp]
    simp [consistentLoad]; field_simp; ring

/-- **Fully fixed element**: if all four degrees of freedom are fixed (`d = 0`), the element
equations `k d = f + r` force the reactions to be `r = -f`. -/
theorem fixedEnd_reactions (EI q L : ℝ) {r : Fin 4 → ℝ}
    (h : beamStiffness EI L *ᵥ 0 = consistentLoad q L + r) : r = -consistentLoad q L := by
  rw [mulVec_zero] at h
  funext i
  have := congrFun h i
  simp only [Pi.zero_apply, Pi.add_apply] at this
  simp only [Pi.neg_apply]
  linarith

/-- **Fixed-end forces and moments** of a clamped–clamped element under a uniform load `q`:
end reactions `-qL/2` and end moments `-qL²/12`, `+qL²/12`. -/
theorem fixedEnd_moments (EI q L : ℝ) {r : Fin 4 → ℝ}
    (h : beamStiffness EI L *ᵥ 0 = consistentLoad q L + r) :
    r 0 = -(q * L / 2) ∧ r 1 = -(q * L ^ 2 / 12) ∧ r 2 = -(q * L / 2) ∧
      r 3 = q * L ^ 2 / 12 := by
  rw [fixedEnd_reactions EI q L h]
  simp [consistentLoad]

/-- Clamping node 1 (`w(0) = w'(0) = 0`) leaves the reduced `2 × 2` stiffness matrix of the
degrees of freedom `(w(L), w'(L))`. -/
theorem reducedStiffness_cantilever (EI L : ℝ) :
    (beamStiffness EI L).submatrix ![2, 3] ![2, 3] =
      (EI / L ^ 3) • !![12, -6 * L; -6 * L, 4 * L ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Solution of the two scalar equations of the reduced cantilever system. -/
theorem cantilever_eqs_iff {EI L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0) (P δ θ : ℝ) :
    EI / L ^ 3 * (12 * δ - 6 * L * θ) = P ∧ EI / L ^ 3 * (-6 * L * δ + 4 * L ^ 2 * θ) = 0 ↔
      δ = P * L ^ 3 / (3 * EI) ∧ θ = P * L ^ 2 / (2 * EI) := by
  constructor
  · rintro ⟨h0, h1⟩
    have hc : EI / L ^ 3 * L ≠ 0 := mul_ne_zero (div_ne_zero hEI (pow_ne_zero 3 hL)) hL
    have e1 : 2 * L * θ = 3 * δ := by
      have := (mul_eq_zero.1 (show EI / L ^ 3 * L * (4 * L * θ - 6 * δ) = 0 by
        linear_combination h1)).resolve_left hc
      linarith
    have e0 : EI * (12 * δ - 6 * L * θ) = P * L ^ 3 := by
      field_simp at h0; linear_combination h0
    have hδ : δ = P * L ^ 3 / (3 * EI) := by
      rw [eq_div_iff (mul_ne_zero three_ne_zero hEI)]
      linear_combination e0 + 3 * EI * e1
    refine ⟨hδ, ?_⟩
    rw [eq_div_iff (mul_ne_zero two_ne_zero hEI)]
    rw [hδ] at e1; field_simp at e1; linear_combination e1
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- **Cantilever, one element**: the reduced system `K_ff (δ, θ) = (P, 0)` has the unique
solution `δ = PL³/(3EI)`, `θ = PL²/(2EI)`. -/
theorem cantilever_solve {EI L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0) (P δ θ : ℝ) :
    ((EI / L ^ 3) • !![12, -6 * L; -6 * L, 4 * L ^ 2]) *ᵥ ![δ, θ] = ![P, 0] ↔
      δ = P * L ^ 3 / (3 * EI) ∧ θ = P * L ^ 2 / (2 * EI) := by
  have hmv : ((EI / L ^ 3) • !![12, -6 * L; -6 * L, 4 * L ^ 2]) *ᵥ ![δ, θ] =
      ![EI / L ^ 3 * (12 * δ - 6 * L * θ), EI / L ^ 3 * (-6 * L * δ + 4 * L ^ 2 * θ)] := by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, -mul_eq_mul_left_iff] <;> ring
  rw [hmv, ← cantilever_eqs_iff hEI hL]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]

/-- **Cantilever, one element**, in terms of the full element equations: with node 1 clamped
and a tip load `P` at node 2, the tip deflection is `PL³/(3EI)` and the tip rotation
`PL²/(2EI)`. -/
theorem cantilever_oneElement {EI L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0) (P δ θ : ℝ) :
    (beamStiffness EI L *ᵥ ![0, 0, δ, θ]) 2 = P ∧
        (beamStiffness EI L *ᵥ ![0, 0, δ, θ]) 3 = 0 ↔
      δ = P * L ^ 3 / (3 * EI) ∧ θ = P * L ^ 2 / (2 * EI) := by
  rw [← cantilever_eqs_iff hEI hL, beamStiffness_mulVec]
  have e2 : EI / L ^ 3 * (-12 * (0 : ℝ) - 6 * L * 0 + 12 * δ - 6 * L * θ) =
      EI / L ^ 3 * (12 * δ - 6 * L * θ) := by ring
  have e3 : EI / L ^ 3 * (6 * L * (0 : ℝ) + 2 * L ^ 2 * 0 - 6 * L * δ + 4 * L ^ 2 * θ) =
      EI / L ^ 3 * (-6 * L * δ + 4 * L ^ 2 * θ) := by ring
  exact Iff.of_eq (congrArg₂ _ (congrArg (· = P) e2) (congrArg (· = 0) e3))

/-- Support reactions of the one-element cantilever: force `-P` and moment `-PL` at the
clamp. -/
theorem cantilever_reactions {EI L : ℝ} (hEI : EI ≠ 0) (hL : L ≠ 0) (P : ℝ) :
    (beamStiffness EI L *ᵥ ![0, 0, P * L ^ 3 / (3 * EI), P * L ^ 2 / (2 * EI)]) 0 = -P ∧
      (beamStiffness EI L *ᵥ ![0, 0, P * L ^ 3 / (3 * EI), P * L ^ 2 / (2 * EI)]) 1 =
        -(P * L) := by
  rw [beamStiffness_mulVec]
  constructor
  · change EI / L ^ 3 * (12 * 0 + 6 * L * 0 - 12 * (P * L ^ 3 / (3 * EI)) +
      6 * L * (P * L ^ 2 / (2 * EI))) = -P
    field_simp; ring
  · change EI / L ^ 3 * (6 * L * 0 + 4 * L ^ 2 * 0 - 6 * L * (P * L ^ 3 / (3 * EI)) +
      2 * L ^ 2 * (P * L ^ 2 / (2 * EI))) = -(P * L)
    field_simp; ring

/-- Nodal values of the exact cantilever solution `P x² (3L - x) / (6EI)`. -/
theorem nodalValues_cantileverTip (b : EBBeam) (P : ℝ) :
    nodalValues b.L (b.cantileverTip P) =
      ![0, 0, P * b.L ^ 3 / (3 * b.EI), P * b.L ^ 2 / (2 * b.EI)] := by
  have hEI := b.EI_pos.ne'
  unfold EBBeam.cantileverTip EBBeam.cantileverTipPoly
  simp only [nodalValues, ContinuumMechanics.Beams.deriv_eval]
  ext i
  fin_cases i <;> simp [derivative_mul] <;> field_simp <;> ring

/-- **The one-element solution is exact**: the finite element tip deflection and rotation are
those of the exact solution `EBBeam.cantileverTip` (a cubic). -/
theorem cantilever_oneElement_exact (b : EBBeam) (P δ θ : ℝ) :
    (beamStiffness b.EI b.L *ᵥ ![0, 0, δ, θ]) 2 = P ∧
        (beamStiffness b.EI b.L *ᵥ ![0, 0, δ, θ]) 3 = 0 ↔
      ![0, 0, δ, θ] = nodalValues b.L (b.cantileverTip P) := by
  rw [cantilever_oneElement b.EI_pos.ne' b.L_pos.ne', nodalValues_cantileverTip]
  constructor
  · rintro ⟨rfl, rfl⟩
    rfl
  · intro h
    exact ⟨congrFun h 2, congrFun h 3⟩

/-- Exact deflection of a clamped–clamped beam under a uniform load `q`:
`w = q x² (L - x)² / (24 EI)`. [TimoshenkoGere1997], App. G. -/
noncomputable def clampedUniform (b : EBBeam) (q : ℝ) : ℝ → ℝ :=
  fun x => (C (q / (24 * b.EI)) * (X ^ 2 * (C b.L - X) ^ 2)).eval x

/-- `clampedUniform` solves `EI w'''' = q` with both ends clamped. -/
theorem clampedUniform_solves (b : EBBeam) (q : ℝ) :
    b.Equation (fun _ => q) (clampedUniform b q) ∧ b.ClampedClamped (clampedUniform b q) := by
  have hEI := b.EI_pos.ne'
  refine ⟨fun x _ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold clampedUniform
  all_goals beam_poly

/-- The reactions of the fully fixed element equal the exact end shear forces and bending
moments `(EI w'''(0), -EI w''(0), -EI w'''(L), EI w''(L))` of the exact clamped–clamped
solution. -/
theorem fixedEnd_reactions_eq_exact (b : EBBeam) (q : ℝ) {r : Fin 4 → ℝ}
    (h : beamStiffness b.EI b.L *ᵥ 0 = consistentLoad q b.L + r) :
    r = ![b.EI * iteratedDeriv 3 (clampedUniform b q) 0,
      -(b.EI * iteratedDeriv 2 (clampedUniform b q) 0),
      -(b.EI * iteratedDeriv 3 (clampedUniform b q) b.L),
      b.EI * iteratedDeriv 2 (clampedUniform b q) b.L] := by
  have hEI := b.EI_pos.ne'
  rw [fixedEnd_reactions _ _ _ h]
  unfold clampedUniform
  simp only [ContinuumMechanics.Beams.iteratedDeriv_eval]
  ext i
  fin_cases i <;>
    simp [consistentLoad, derivative_mul, derivative_pow, Function.iterate_succ] <;>
    field_simp <;> ring

/-- The classical fixed-end moments: the bending moment `M = -EI w''` of the exact
clamped–clamped solution is `-qL²/12` at both ends. -/
theorem clampedUniform_endMoments (b : EBBeam) (q : ℝ) :
    -(b.EI * iteratedDeriv 2 (clampedUniform b q) 0) = -(q * b.L ^ 2 / 12) ∧
      -(b.EI * iteratedDeriv 2 (clampedUniform b q) b.L) = -(q * b.L ^ 2 / 12) := by
  have hEI := b.EI_pos.ne'
  constructor <;> unfold clampedUniform <;> beam_poly

end DiscreteMechanics.BeamElement
