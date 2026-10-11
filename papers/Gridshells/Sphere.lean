import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Gridshells.Chebyshev

/-!
# Chebyshev nets on the unit sphere

A **Chebyshev net on the unit sphere** is a map `r(u, v)` into `S² ⊂ ℝ³` whose coordinate curves are
parametrized by arc length: `|r| = 1`, `|r_u| = |r_v| = 1`. Its angle `ω` is given by
`cos ω = r_u · r_v` (`SphericalNet`). We prove from these geometric data that the angle satisfies
the **Chebyshev-net equation with `K = 1`**:

`ω_uv = -sin ω`   (`SphericalNet.sine_gordon`),

so that the Hazzidakis formula and the area bound of `Gridshells.Chebyshev` hold for actual
spherical nets (`SphericalNet.area_lt_two_pi`): **a Chebyshev quadrilateral on the unit sphere has
area less than `2π`**.

## Proof

All the identities below come from differentiating the constraints. With the orthonormal frame
`(r, r_u, n)`, `n = r × r_u`, and Parseval's identity in it (`dot_eq_parseval`):

* `r_uv = -cos ω r` (`ruv_eq`): `r_uv` is orthogonal to `r_u` and `r_v`, and `r · r_uv = -cos ω`;
* hence `r_uuv · r_v = -cos²ω`, and `r_uu · r_vv = 1 - cos ω ω_u ω_v`;
* differentiating `-sin ω ω_u = r_uu · r_v` in `v` gives `-cos ω ω_u ω_v - sin ω ω_uv
  = r_uuv · r_v + r_uu · r_vv = sin²ω - cos ω ω_u ω_v`.

## References

* [Baek2018] C. Baek, A. O. Sageman-Furnas, M. K. Jawed, P. M. Reis, *Form finding in elastic
  gridshells*, PNAS 115(1) (2018).
* [Ghys2011] É. Ghys, *Sur la coupe des vêtements: variation autour d'un thème de Tchebychev*,
  Enseign. Math. (2011).
-/

open Matrix Real

noncomputable section

namespace ContinuumMechanics.Gridshells

/-! ### Calculus and algebra in `ℝ³` -/

/-- Derivative of a dot product. -/
theorem hasDerivAt_dot {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hf' i).mul (hg' i)
  convert this using 1
  · ext s; simp [dotProduct]
  · simp [dotProduct, Finset.sum_add_distrib]

/-- A function that is constant has zero derivative. -/
theorem deriv_zero_of_const {f : ℝ → ℝ} {c d t : ℝ} (hc : ∀ s, f s = c) (hf : HasDerivAt f d t) :
    d = 0 := by
  have : f = fun _ => c := funext hc
  rw [this] at hf
  exact hf.unique (hasDerivAt_const t c)

/-- **Parseval's identity** in an orthonormal frame of `ℝ³`. -/
theorem dot_eq_parseval {e₁ e₂ e₃ : Fin 3 → ℝ} (h11 : e₁ ⬝ᵥ e₁ = 1) (h22 : e₂ ⬝ᵥ e₂ = 1)
    (h33 : e₃ ⬝ᵥ e₃ = 1) (h12 : e₁ ⬝ᵥ e₂ = 0) (h13 : e₁ ⬝ᵥ e₃ = 0) (h23 : e₂ ⬝ᵥ e₃ = 0)
    (x y : Fin 3 → ℝ) :
    x ⬝ᵥ y = (e₁ ⬝ᵥ x) * (e₁ ⬝ᵥ y) + (e₂ ⬝ᵥ x) * (e₂ ⬝ᵥ y) + (e₃ ⬝ᵥ x) * (e₃ ⬝ᵥ y) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![e₁, e₂, e₃]
  have hM : M * Mᵀ = 1 := by
    ext i j
    have : (M * Mᵀ) i j = (![e₁, e₂, e₃] i) ⬝ᵥ (![e₁, e₂, e₃] j) := by
      simp [M, mul_apply, dotProduct]
    rw [this]
    fin_cases i <;> fin_cases j <;>
      simp [h11, h22, h33, h12, h13, h23, dotProduct_comm e₂ e₁, dotProduct_comm e₃ e₁,
        dotProduct_comm e₃ e₂]
  have hM' : Mᵀ * M = 1 := mul_eq_one_comm.mp hM
  have hv : ∀ z, M *ᵥ z = ![e₁ ⬝ᵥ z, e₂ ⬝ᵥ z, e₃ ⬝ᵥ z] := fun z => by
    ext i; fin_cases i <;> rfl
  calc x ⬝ᵥ y = x ⬝ᵥ ((Mᵀ * M) *ᵥ y) := by rw [hM', one_mulVec]
    _ = (M *ᵥ x) ⬝ᵥ (M *ᵥ y) := by
        rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by rw [hv, hv]; simp [dotProduct, Fin.sum_univ_three]

/-! ### Spherical Chebyshev nets -/

/-- A **Chebyshev net on the unit sphere** with its angle `ω`, given by the map `r` and its partial
derivatives up to `r_uuv`, and `ω` with `ω_u`, `ω_v` and the mixed derivative `ω_uv`. -/
structure SphericalNet where
  r : ℝ → ℝ → Fin 3 → ℝ
  ru : ℝ → ℝ → Fin 3 → ℝ
  rv : ℝ → ℝ → Fin 3 → ℝ
  ruu : ℝ → ℝ → Fin 3 → ℝ
  rvv : ℝ → ℝ → Fin 3 → ℝ
  ruv : ℝ → ℝ → Fin 3 → ℝ
  ruuv : ℝ → ℝ → Fin 3 → ℝ
  ω : ℝ → ℝ → ℝ
  ωu : ℝ → ℝ → ℝ
  ωv : ℝ → ℝ → ℝ
  ωuv : ℝ → ℝ → ℝ
  r_u : ∀ u v, HasDerivAt (fun u => r u v) (ru u v) u
  r_v : ∀ u v, HasDerivAt (r u) (rv u v) v
  ru_u : ∀ u v, HasDerivAt (fun u => ru u v) (ruu u v) u
  ru_v : ∀ u v, HasDerivAt (ru u) (ruv u v) v
  rv_u : ∀ u v, HasDerivAt (fun u => rv u v) (ruv u v) u
  rv_v : ∀ u v, HasDerivAt (rv u) (rvv u v) v
  ruu_v : ∀ u v, HasDerivAt (ruu u) (ruuv u v) v
  ruv_u : ∀ u v, HasDerivAt (fun u => ruv u v) (ruuv u v) u
  ω_u : ∀ u v, HasDerivAt (fun u => ω u v) (ωu u v) u
  ω_v : ∀ u v, HasDerivAt (ω u) (ωv u v) v
  ωu_v : ∀ u v, HasDerivAt (ωu u) (ωuv u v) v
  /-- The net lies on the unit sphere. -/
  on_sphere : ∀ u v, r u v ⬝ᵥ r u v = 1
  /-- Both families of curves are parametrized by arc length (inextensible rods). -/
  unit_u : ∀ u v, ru u v ⬝ᵥ ru u v = 1
  unit_v : ∀ u v, rv u v ⬝ᵥ rv u v = 1
  /-- `ω` is the angle between the rods. -/
  angle : ∀ u v, Real.cos (ω u v) = ru u v ⬝ᵥ rv u v
  /-- The net does not degenerate: the angle between the rods lies in `(0, π)`. -/
  angle_mem : ∀ u v, ω u v ∈ Set.Ioo 0 π

namespace SphericalNet

variable (N : SphericalNet) (u v : ℝ)

theorem sin_pos : 0 < Real.sin (N.ω u v) :=
  Real.sin_pos_of_pos_of_lt_pi (N.angle_mem u v).1 (N.angle_mem u v).2

theorem r_ru : N.r u v ⬝ᵥ N.ru u v = 0 := by
  have := deriv_zero_of_const (fun u => N.on_sphere u v) (hasDerivAt_dot (N.r_u u v) (N.r_u u v))
  rw [dotProduct_comm] at this; linarith

theorem r_rv : N.r u v ⬝ᵥ N.rv u v = 0 := by
  have := deriv_zero_of_const (N.on_sphere u) (hasDerivAt_dot (N.r_v u v) (N.r_v u v))
  rw [dotProduct_comm] at this; linarith

theorem ru_ruv : N.ru u v ⬝ᵥ N.ruv u v = 0 := by
  have := deriv_zero_of_const (N.unit_u u) (hasDerivAt_dot (N.ru_v u v) (N.ru_v u v))
  rw [dotProduct_comm] at this; linarith

theorem rv_ruv : N.rv u v ⬝ᵥ N.ruv u v = 0 := by
  have := deriv_zero_of_const (fun u => N.unit_v u v) (hasDerivAt_dot (N.rv_u u v) (N.rv_u u v))
  rw [dotProduct_comm] at this; linarith

theorem ru_ruu : N.ru u v ⬝ᵥ N.ruu u v = 0 := by
  have := deriv_zero_of_const (fun u => N.unit_u u v) (hasDerivAt_dot (N.ru_u u v) (N.ru_u u v))
  rw [dotProduct_comm] at this; linarith

theorem rv_rvv : N.rv u v ⬝ᵥ N.rvv u v = 0 := by
  have := deriv_zero_of_const (N.unit_v u) (hasDerivAt_dot (N.rv_v u v) (N.rv_v u v))
  rw [dotProduct_comm] at this; linarith

theorem r_ruv : N.r u v ⬝ᵥ N.ruv u v = -Real.cos (N.ω u v) := by
  have := deriv_zero_of_const (fun v => N.r_ru u v) (hasDerivAt_dot (N.r_v u v) (N.ru_v u v))
  rw [N.angle, dotProduct_comm (N.ru u v)]; linarith

theorem r_ruu : N.r u v ⬝ᵥ N.ruu u v = -1 := by
  have := deriv_zero_of_const (fun u => N.r_ru u v) (hasDerivAt_dot (N.r_u u v) (N.ru_u u v))
  rw [N.unit_u] at this; linarith

theorem r_rvv : N.r u v ⬝ᵥ N.rvv u v = -1 := by
  have := deriv_zero_of_const (fun v => N.r_rv u v) (hasDerivAt_dot (N.r_v u v) (N.rv_v u v))
  rw [N.unit_v] at this; linarith

/-- `-sin ω ω_u = r_uu · r_v`. -/
theorem ruu_rv : N.ruu u v ⬝ᵥ N.rv u v = -(Real.sin (N.ω u v) * N.ωu u v) := by
  have h1 := (N.ω_u u v).cos
  have h2 := hasDerivAt_dot (N.ru_u u v) (N.rv_u u v)
  have : (fun u => Real.cos (N.ω u v)) = fun u => N.ru u v ⬝ᵥ N.rv u v :=
    funext fun u => N.angle u v
  rw [this] at h1
  have := h1.unique h2
  rw [N.ru_ruv] at this; linarith

/-- `-sin ω ω_v = r_u · r_vv`. -/
theorem ru_rvv : N.ru u v ⬝ᵥ N.rvv u v = -(Real.sin (N.ω u v) * N.ωv u v) := by
  have h1 := (N.ω_v u v).cos
  have h2 := hasDerivAt_dot (N.ru_v u v) (N.rv_v u v)
  have : (fun v => Real.cos (N.ω u v)) = fun v => N.ru u v ⬝ᵥ N.rv u v :=
    funext fun v => N.angle u v
  rw [this] at h1
  have := h1.unique h2
  rw [dotProduct_comm (N.ruv u v), N.rv_ruv] at this; linarith

/-! ### The frame `(r, r_u, n)` -/

/-- The unit normal to `r_u` in the tangent plane, `n = r × r_u`. -/
def n : Fin 3 → ℝ := N.r u v ⨯₃ N.ru u v

theorem n_r : N.n u v ⬝ᵥ N.r u v = 0 := by rw [n, dotProduct_comm, dot_self_cross]
theorem n_ru : N.n u v ⬝ᵥ N.ru u v = 0 := by rw [n, dotProduct_comm, dot_cross_self]
theorem n_n : N.n u v ⬝ᵥ N.n u v = 1 := by
  rw [n, cross_dot_cross, N.on_sphere, N.unit_u, N.r_ru]; ring

/-- Parseval's identity in the frame `(r, r_u, n)`. -/
theorem parseval (x y : Fin 3 → ℝ) :
    x ⬝ᵥ y = (N.r u v ⬝ᵥ x) * (N.r u v ⬝ᵥ y) + (N.ru u v ⬝ᵥ x) * (N.ru u v ⬝ᵥ y) +
      (N.n u v ⬝ᵥ x) * (N.n u v ⬝ᵥ y) :=
  dot_eq_parseval (N.on_sphere u v) (N.unit_u u v) (N.n_n u v) (N.r_ru u v)
    (by rw [dotProduct_comm]; exact N.n_r u v) (by rw [dotProduct_comm]; exact N.n_ru u v) x y

/-- `(n · r_v)² = sin²ω`. -/
theorem n_rv_sq : (N.n u v ⬝ᵥ N.rv u v) ^ 2 = Real.sin (N.ω u v) ^ 2 := by
  have h := N.parseval u v (N.rv u v) (N.rv u v)
  rw [N.unit_v, N.r_rv, ← N.angle] at h
  nlinarith [Real.sin_sq_add_cos_sq (N.ω u v)]

/-- `r_uv = -cos ω r`. -/
theorem ruv_eq : N.ruv u v = -Real.cos (N.ω u v) • N.r u v := by
  have hs := N.sin_pos u v
  -- `n · r_uv = 0`, from `r_v · r_uv = 0`
  have hn : N.n u v ⬝ᵥ N.ruv u v = 0 := by
    have h := N.parseval u v (N.rv u v) (N.ruv u v)
    rw [N.rv_ruv, N.r_rv, N.ru_ruv, zero_mul, mul_zero, zero_add, zero_add] at h
    have hnv : N.n u v ⬝ᵥ N.rv u v ≠ 0 := by
      intro h0; have := N.n_rv_sq u v; rw [h0] at this; nlinarith
    exact (mul_eq_zero.mp h.symm).resolve_left hnv
  set w := N.ruv u v + Real.cos (N.ω u v) • N.r u v
  have hw : w ⬝ᵥ w = 0 := by
    rw [N.parseval u v w w]
    simp only [w, dotProduct_add, dotProduct_smul, smul_eq_mul, N.r_ruv, N.on_sphere, N.ru_ruv,
      hn, N.r_ru, dotProduct_comm (N.ru u v) (N.r u v), N.n_r]
    ring
  have : w = 0 := dotProduct_self_eq_zero.mp hw
  rw [← sub_eq_zero, sub_eq_add_neg, neg_smul, neg_neg]
  exact this

/-- `r_uuv · r_v = -cos²ω`. -/
theorem ruuv_rv : N.ruuv u v ⬝ᵥ N.rv u v = -Real.cos (N.ω u v) ^ 2 := by
  have h1 : HasDerivAt (fun u => (-Real.cos (N.ω u v)) • N.r u v)
      ((-Real.cos (N.ω u v)) • N.ru u v + (-(-Real.sin (N.ω u v) * N.ωu u v)) • N.r u v) u :=
    ((N.ω_u u v).cos.neg).smul (N.r_u u v)
  have : (fun u => (-Real.cos (N.ω u v)) • N.r u v) = fun u => N.ruv u v :=
    funext fun u => (N.ruv_eq u v).symm
  rw [this] at h1
  rw [(N.ruv_u u v).unique h1, add_dotProduct, smul_dotProduct, smul_dotProduct, ← N.angle,
    N.r_rv, smul_eq_mul, smul_eq_mul]
  ring

/-- `r_uu · r_vv = 1 - cos ω ω_u ω_v`. -/
theorem ruu_rvv : N.ruu u v ⬝ᵥ N.rvv u v =
    1 - Real.cos (N.ω u v) * N.ωu u v * N.ωv u v := by
  have hs := N.sin_pos u v
  have hS : Real.sin (N.ω u v) ^ 2 ≠ 0 := by positivity
  set s := N.n u v ⬝ᵥ N.rv u v
  -- `s (n · r_uu) = -sin ω ω_u`
  have h1 : s * (N.n u v ⬝ᵥ N.ruu u v) = -(Real.sin (N.ω u v) * N.ωu u v) := by
    have h := N.parseval u v (N.ruu u v) (N.rv u v)
    rw [N.ruu_rv, N.r_rv, N.ru_ruu] at h
    linarith
  -- `s (n · r_vv) = cos ω sin ω ω_v`
  have h2 : s * (N.n u v ⬝ᵥ N.rvv u v) =
      Real.cos (N.ω u v) * (Real.sin (N.ω u v) * N.ωv u v) := by
    have h := N.parseval u v (N.rv u v) (N.rvv u v)
    have hc : N.ru u v ⬝ᵥ N.rv u v = Real.cos (N.ω u v) := (N.angle u v).symm
    rw [N.rv_rvv, N.r_rv, N.ru_rvv, dotProduct_comm (N.ru u v) (N.rv u v)] at h
    rw [dotProduct_comm (N.rv u v) (N.ru u v), hc] at h
    linarith
  have hsq : s ^ 2 = Real.sin (N.ω u v) ^ 2 := N.n_rv_sq u v
  have hprod : (N.n u v ⬝ᵥ N.ruu u v) * (N.n u v ⬝ᵥ N.rvv u v) =
      -(Real.cos (N.ω u v) * N.ωu u v * N.ωv u v) := by
    apply mul_left_cancel₀ hS
    rw [← hsq]
    linear_combination (s * (N.n u v ⬝ᵥ N.rvv u v)) * h1 +
      (-(Real.sin (N.ω u v) * N.ωu u v)) * h2 +
      (N.ωu u v * Real.cos (N.ω u v) * N.ωv u v) * hsq
  have h := N.parseval u v (N.ruu u v) (N.rvv u v)
  rw [N.r_ruu, N.r_rvv, N.ru_ruu, hprod] at h
  linarith

/-- **The Chebyshev-net equation on the unit sphere**: `ω_uv = -sin ω`. -/
theorem sine_gordon : N.ωuv u v = -Real.sin (N.ω u v) := by
  have hs := N.sin_pos u v
  -- differentiate `-sin ω ω_u = r_uu · r_v` in `v`
  have h1 : HasDerivAt (fun v => -(Real.sin (N.ω u v) * N.ωu u v))
      (-(Real.cos (N.ω u v) * N.ωv u v * N.ωu u v + Real.sin (N.ω u v) * N.ωuv u v)) v :=
    (((N.ω_v u v).sin).mul (N.ωu_v u v)).neg
  have h2 := hasDerivAt_dot (N.ruu_v u v) (N.rv_v u v)
  have : (fun v => -(Real.sin (N.ω u v) * N.ωu u v)) = fun v => N.ruu u v ⬝ᵥ N.rv u v :=
    funext fun v => (N.ruu_rv u v).symm
  rw [this] at h1
  have e := h1.unique h2
  rw [N.ruuv_rv, N.ruu_rvv] at e
  have hc := Real.sin_sq_add_cos_sq (N.ω u v)
  apply mul_left_cancel₀ hs.ne'
  nlinarith [e]

/-- A spherical Chebyshev net satisfies the angle equation of `Gridshells.Chebyshev` with `K = 1`,
given the mixed derivative in the other order (`∂_u ω_v = ω_uv`) and the continuity used by the
integrals. -/
theorem isChebyshevAngle (hvu : ∀ u v, HasDerivAt (fun u => N.ωv u v) (N.ωuv u v) u)
    (hcv : ∀ u, Continuous (N.ωv u)) (hcuv : ∀ v, Continuous fun u => N.ωuv u v) :
    IsChebyshevAngle (fun _ _ => 1) N.ω N.ωv N.ωuv where
  hasDerivAt_v := N.ω_v
  hasDerivAt_u := hvu
  continuous_ωv := hcv
  continuous_ωuv := hcuv
  sine_gordon u v := by rw [N.sine_gordon, one_mul]

/-- **A Chebyshev quadrilateral on the unit sphere has area less than `2π`.** -/
theorem area_lt_two_pi (hvu : ∀ u v, HasDerivAt (fun u => N.ωv u v) (N.ωuv u v) u)
    (hcv : ∀ u, Continuous (N.ωv u)) (hcuv : ∀ v, Continuous fun u => N.ωuv u v) (a b : ℝ) :
    area N.ω a b < 2 * π :=
  Gridshells.area_lt_two_pi (N.isChebyshevAngle hvu hcv hcuv) a b (N.angle_mem 0 0).1
    (N.angle_mem a 0).2 (N.angle_mem a b).1 (N.angle_mem 0 b).2

end SphericalNet

end ContinuumMechanics.Gridshells
