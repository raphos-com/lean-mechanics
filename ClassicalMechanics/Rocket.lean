import ClassicalMechanics.Vector
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Variable mass: the rocket equation

A rocket moving on a line has mass `m(t) > 0` and velocity `v(t)`; it ejects mass at the
**exhaust speed** `u > 0` relative to itself, so that the ejected mass `-ṁ dt` leaves with velocity
`v - u`. Momentum balance of the rocket together with the ejected mass reads
`d/dt (m v) = ṁ (v - u) + F_ext`, which is the **rocket equation** (`rocket_equation`)

`m v̇ = -u ṁ + F_ext`.

* **Tsiolkovsky** (`tsiolkovsky`): in free space, `v(t) - v(0) = u log (m(0) / m(t))`, since
  `v + u log m` has zero derivative.
* **Uniform gravity** (`rocket_gravity`): with `F_ext = -m g`,
  `v(t) - v(0) = u log (m(0) / m(t)) - g t`.
* **Constant burn rate** (`constantBurn_velocity`, `constantBurn_delta_v`): for
  `m(t) = m₀ - β t` the velocity is `v(0) + u log (m₀ / (m₀ - β t)) - g t`, and the velocity gained
  in free space when the mass has dropped to `m_f` is `Δv = u log (m₀ / m_f)`.

The results are stated on a time interval `[0, T]` on which the mass stays positive, so that they
apply to a burn of finite duration.

## References

* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §1.2,
  exercise 1.
* [KleppnerKolenkow2014] D. Kleppner, R. Kolenkow, *An Introduction to Mechanics*, 2nd ed., §4.8.
-/

open Set Real

noncomputable section

namespace ClassicalMechanics

namespace Rocket

/-- **The rocket equation from momentum balance**: if the momentum of the rocket plus the mass it
ejects (at relative speed `u`) obeys `d/dt (m v) = ṁ (v - u) + F`, then `m v̇ = -u ṁ + F`. -/
theorem rocket_equation {m v : ℝ → ℝ} {m' v' u F t : ℝ} (hm : HasDerivAt m m' t)
    (hv : HasDerivAt v v' t) (hP : HasDerivAt (fun s => m s * v s) (m' * (v t - u) + F) t) :
    m t * v' = -u * m' + F := by
  have h := hP.unique (hm.mul hv)
  linarith

/-- **Rocket in uniform gravity**: if on `[0, T]` the mass stays positive and
`m v̇ = -u ṁ - m g`, then `v(t) - v(0) = u log (m(0) / m(t)) - g t` for `t ∈ [0, T]`. -/
theorem rocket_gravity {m v m' v' : ℝ → ℝ} {u g T : ℝ}
    (hm : ∀ s ∈ Icc 0 T, HasDerivAt m (m' s) s) (hv : ∀ s ∈ Icc 0 T, HasDerivAt v (v' s) s)
    (hpos : ∀ s ∈ Icc 0 T, 0 < m s)
    (heq : ∀ s ∈ Icc 0 T, m s * v' s = -u * m' s - m s * g) {t : ℝ} (ht : t ∈ Icc 0 T) :
    v t - v 0 = u * log (m 0 / m t) - g * t := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  set φ : ℝ → ℝ := fun s => v s + u * log (m s) + g * s with hφ
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt φ 0 s := by
    intro s hs
    have h := (((hv s hs).add (((hm s hs).log (hpos s hs).ne').const_mul u)).add
      ((hasDerivAt_id s).const_mul g))
    have hms := (hpos s hs).ne'
    refine (h.congr_deriv ?_ :)
    have hv' : v' s = (-u * m' s - m s * g) / m s := by
      rw [eq_div_iff hms, mul_comm, heq s hs]
    rw [hv']
    field_simp
    ring
  have hc : ContinuousOn φ (Icc 0 T) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  simp only [hφ, mul_zero, add_zero] at hconst
  rw [log_div (hpos 0 h0).ne' (hpos t ht).ne']
  linarith

/-- **Tsiolkovsky's rocket equation**: in free space (`m v̇ = -u ṁ`), as long as the mass stays
positive on `[0, T]`, `v(t) - v(0) = u log (m(0) / m(t))` for `t ∈ [0, T]`. -/
theorem tsiolkovsky {m v m' v' : ℝ → ℝ} {u T : ℝ}
    (hm : ∀ s ∈ Icc 0 T, HasDerivAt m (m' s) s) (hv : ∀ s ∈ Icc 0 T, HasDerivAt v (v' s) s)
    (hpos : ∀ s ∈ Icc 0 T, 0 < m s) (heq : ∀ s ∈ Icc 0 T, m s * v' s = -u * m' s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    v t - v 0 = u * log (m 0 / m t) := by
  have := rocket_gravity (g := 0) hm hv hpos (fun s hs => by rw [heq s hs]; ring) ht
  simpa using this

/-- The mass of a rocket burning fuel at the constant rate `β`: `m(t) = m₀ - β t`. -/
def constantBurn (m₀ β : ℝ) (t : ℝ) : ℝ := m₀ - β * t

/-- The constant-burn mass has derivative `-β`. -/
theorem hasDerivAt_constantBurn (m₀ β t : ℝ) : HasDerivAt (constantBurn m₀ β) (-β) t := by
  have := ((hasDerivAt_id t).const_mul β).const_sub m₀
  convert this using 1
  · funext x
    simp [constantBurn]
  · ring

/-- **Constant burn rate in uniform gravity**: if `m(t) = m₀ - β t` with `β ≥ 0` and the mass
`m₀ - β T` at the end of the burn is positive, any solution of `m v̇ = -u ṁ - m g` on `[0, T]` is
`v(t) = v(0) + u log (m₀ / (m₀ - β t)) - g t`. -/
theorem constantBurn_velocity {v v' : ℝ → ℝ} {m₀ β u g T : ℝ} (hβ : 0 ≤ β)
    (hT : 0 < m₀ - β * T) (hv : ∀ s ∈ Icc 0 T, HasDerivAt v (v' s) s)
    (heq : ∀ s ∈ Icc 0 T, constantBurn m₀ β s * v' s = -u * (-β) - constantBurn m₀ β s * g)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    v t = v 0 + u * log (m₀ / (m₀ - β * t)) - g * t := by
  have hpos : ∀ s ∈ Icc 0 T, 0 < constantBurn m₀ β s := fun s hs => by
    simp only [constantBurn]
    nlinarith [mul_le_mul_of_nonneg_left hs.2 hβ]
  have := rocket_gravity (m' := fun _ => -β) (fun s _ => hasDerivAt_constantBurn m₀ β s) hv
    hpos heq ht
  simp only [constantBurn, mul_zero, sub_zero] at this
  linarith

/-- **Burnout velocity**: for a constant burn in free space, when the mass has dropped from `m₀`
to `m_f = m₀ - β t_b > 0`, the velocity gained is `Δv = u log (m₀ / m_f)`. -/
theorem constantBurn_delta_v {v v' : ℝ → ℝ} {m₀ β u t_b : ℝ} (hβ : 0 ≤ β) (htb : 0 ≤ t_b)
    (hf : 0 < m₀ - β * t_b) (hv : ∀ s ∈ Icc 0 t_b, HasDerivAt v (v' s) s)
    (heq : ∀ s ∈ Icc 0 t_b, constantBurn m₀ β s * v' s = -u * (-β)) :
    v t_b - v 0 = u * log (m₀ / constantBurn m₀ β t_b) := by
  have := constantBurn_velocity (g := 0) hβ hf hv (fun s hs => by rw [heq s hs]; ring)
    ⟨htb, le_rfl⟩
  simp only [constantBurn]
  linarith

end Rocket

end ClassicalMechanics
