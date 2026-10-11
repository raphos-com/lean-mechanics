import ContinuumMechanics.Elastostatics.NavierLame

/-!
# Plane waves in isotropic elastic media

For a profile `g` of class `C³`, a direction `k` and an amplitude `a` in `ℝⁿ`, the displacement
`u(x) = a g(k · x)` has Navier–Lamé residual (`res_planeWave`)

`Rᵢ = -(μ |k|² aᵢ + (λ + μ)(a · k) kᵢ) g''(k · x) = -(A(k) a)ᵢ g''(k · x)`,

with `A(k)` the acoustic tensor of `Constitutive/Ellipticity`. Consequently the travelling wave
`u(x, t) = a g(k · x - c t)` solves the equations of motion `div σ = ρ ∂²u/∂t²`
(`planeWave_solves`) whenever the **propagation condition** `A(k) a = ρ c² a` holds, i.e. for
longitudinal waves with `ρc² = λ + 2μ` and transverse waves with `ρc² = μ` (`|k| = 1`,
`Ellipticity.acoustic_eigen_iff`).

## References

* [Achenbach1973] J. D. Achenbach, *Wave Propagation in Elastic Solids*, §4.2.
* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §31.
-/

noncomputable section

namespace ContinuumMechanics.NavierLame

open Korn

variable {n : ℕ}

/-- The linear form `x ↦ k · x`. -/
def dotL (k : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, k j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j

theorem dotL_apply (k x : Fin n → ℝ) : dotL k x = ∑ j, k j * x j := by
  simp [dotL]

theorem pd_comp_dotL {g : ℝ → ℝ} (hg : Differentiable ℝ g) (k : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    pd (fun x => c * g (dotL k x)) j = fun x => c * k j * deriv g (dotL k x) := by
  funext x
  have h := ((hg (dotL k x)).hasDerivAt.comp_hasFDerivAt x (dotL k).hasFDerivAt).const_mul c
  rw [pd, show (fun x => c * g (dotL k x)) = fun y => c * (g ∘ ⇑(dotL k)) y from rfl, h.fderiv]
  simp [dotL, Pi.single_apply]
  ring

variable {g : ℝ → ℝ} {lam μ : ℝ}

/-- The Navier–Lamé residual of the plane wave `u = a g(k · x)`. -/
theorem res_planeWave (hg : ContDiff ℝ 3 g) (a k : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    res lam μ (fun i x => a i * g (dotL k x)) i x =
      -(μ * (∑ j, k j ^ 2) * a i + (lam + μ) * (∑ j, a j * k j) * k i) *
        deriv (deriv g) (dotL k x) := by
  have d1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h2 : ContDiff ℝ 2 (deriv g) := (contDiff_succ_iff_deriv (n := 2).mp hg).2.2
  have d2 : Differentiable ℝ (deriv g) := h2.differentiable (by norm_num)
  have hu : ∀ i, ContDiff ℝ 3 (fun x => a i * g (dotL k x)) := fun i =>
    contDiff_const.mul (hg.comp (dotL k).contDiff)
  have p1 : ∀ i l, pd (fun x => a i * g (dotL k x)) l =
      fun x => a i * k l * deriv g (dotL k x) := fun i l => pd_comp_dotL d1 k (a i) l
  have p2 : ∀ i l m, pd (pd (fun x => a i * g (dotL k x)) l) m =
      fun x => a i * k l * k m * deriv (deriv g) (dotL k x) := fun i l m => by
    rw [p1]; exact pd_comp_dotL d2 k _ m
  have hdiv : div (fun i x => a i * g (dotL k x)) =
      fun x => (∑ j, a j * k j) * deriv g (dotL k x) := by
    funext x
    simp only [div, p1, Finset.sum_mul]
  have pdiv : pd (div (fun i x => a i * g (dotL k x))) i =
      fun x => (∑ j, a j * k j) * k i * deriv (deriv g) (dotL k x) := by
    rw [hdiv]; exact pd_comp_dotL d2 k _ i
  rw [res_eq hu i]
  simp only [lap, p2, pdiv]
  have hl : ∑ l, a i * k l * k l * deriv (deriv g) (dotL k x) =
      (∑ l, k l ^ 2) * a i * deriv (deriv g) (dotL k x) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hl]
  ring

/-- **Plane waves solve the equations of motion**: if the propagation condition
`μ |k|² a + (λ + μ)(a · k) k = ρ c² a` holds, the travelling wave `u(x, t) = a g(k · x - c t)`
satisfies `div σ = -R = ρ ∂²u/∂t²` at every point and time. -/
theorem planeWave_solves (hg : ContDiff ℝ 3 g) (a k : Fin n → ℝ) (ρ c : ℝ)
    (hprop : ∀ i, μ * (∑ j, k j ^ 2) * a i + (lam + μ) * (∑ j, a j * k j) * k i = ρ * c ^ 2 * a i)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    -res lam μ (fun i x => a i * g (dotL k x - c * t)) i x =
      ρ * deriv (fun s => deriv (fun s => a i * g (dotL k x - c * s)) s) t := by
  have d1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h2 : ContDiff ℝ 2 (deriv g) := (contDiff_succ_iff_deriv (n := 2).mp hg).2.2
  have d2 : Differentiable ℝ (deriv g) := h2.differentiable (by norm_num)
  -- space: the profile `s ↦ g (s - c t)`
  set gt : ℝ → ℝ := fun s => g (s - c * t) with hgt
  have hgt3 : ContDiff ℝ 3 gt := hg.comp (contDiff_id.sub contDiff_const)
  have dd : deriv (deriv gt) = fun s => deriv (deriv g) (s - c * t) := by
    have e1 : deriv gt = fun s => deriv g (s - c * t) := funext fun s => by
      simp only [gt]; rw [deriv_comp_sub_const]
    rw [e1]
    funext s
    rw [deriv_comp_sub_const]
  have hs := res_planeWave (lam := lam) (μ := μ) hgt3 a k i x
  simp only [gt] at hs
  rw [hs, dd]
  -- time: `∂²ₜ (a g(k·x - c t)) = c² a g''(k·x - c t)`
  have ht1 : ∀ s, deriv (fun s => a i * g (dotL k x - c * s)) s =
      -(c * a i) * deriv g (dotL k x - c * s) := fun s => by
    have h := ((d1 (dotL k x - c * s)).hasDerivAt.comp s
      ((hasDerivAt_id s).const_mul c |>.const_sub (dotL k x))).const_mul (a i)
    refine h.deriv.trans ?_
    ring
  have ht2 : deriv (fun s => deriv (fun s => a i * g (dotL k x - c * s)) s) t =
      c ^ 2 * a i * deriv (deriv g) (dotL k x - c * t) := by
    simp only [ht1]
    have h := ((d2 (dotL k x - c * t)).hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul c |>.const_sub (dotL k x))).const_mul (-(c * a i))
    refine h.deriv.trans ?_
    ring
  rw [ht2, hprop]
  ring

end ContinuumMechanics.NavierLame
