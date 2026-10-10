import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.OpenPos
import ContinuumMechanics.Beams.EulerBernoulli.Basic

/-!
# Euler–Bernoulli beams: energy and the variational principle

The total potential energy of an Euler–Bernoulli beam with deflection `w` under a load `q` is
`Π(w) = ∫₀ᴸ (½ EI w''² - q w) dx` ([Reddy2007], §3.3; [TimoshenkoGere1997], §9.9).

## Main results

* `EBBeam.green_formula`: `∫ EI w'' v'' = [EI w'' v' - EI w''' v]₀ᴸ + ∫ EI w'''' v`.
* `Beams.eq_zero_of_integral_mul_eq_zero`: the fundamental lemma of the calculus of variations
  on an interval (from Mathlib's version on open sets).
* `EBBeam.weak_iff_strong`: **for a `C⁴` deflection with `w(0) = w(L) = 0`, the strong form
  `EI w'''' = q` with the natural boundary conditions `w''(0) = w''(L) = 0` holds iff
  `∫ EI w'' v'' = ∫ q v` for every `C²` variation `v` with `v(0) = v(L) = 0`.**
* `EBBeam.energy_add`: `Π(w + v) = Π(w) + δΠ(w)[v] + ½ ∫ EI v''²`.
* `EBBeam.hasDerivAt_energy`: `d/dε Π(w + ε v)|₀ = δΠ(w)[v]`.
* `EBBeam.energy_le`: **minimum of the potential energy** — the simply supported solution
  minimises `Π` among admissible deflections.

## References

* [Reddy2007] J. N. Reddy, *Theory and Analysis of Elastic Plates and Shells*, §3.3.
* [TimoshenkoGere1997] S. P. Timoshenko, J. M. Gere, *Mechanics of Materials*, §9.9.
-/

open Set MeasureTheory intervalIntegral Polynomial
open scoped Topology ContDiff

namespace ContinuumMechanics.Beams

/-- **Fundamental lemma of the calculus of variations** on `[0, L]`: a continuous `f` with
`∫₀ᴸ f φ = 0` for all smooth `φ` compactly supported in `(0, L)` vanishes on `[0, L]`. -/
theorem eq_zero_of_integral_mul_eq_zero {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 L →
      ∫ x in (0)..L, f x * φ x = 0) :
    ∀ x ∈ Icc 0 L, f x = 0 := by
  have hae := (isOpen_Ioo (a := (0 : ℝ)) (b := L)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (hf.locallyIntegrable.locallyIntegrableOn _) (fun g hg hgc hgs => by
      rw [← h g hg hgc hgs, intervalIntegral.integral_of_le hL.le,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 L)]
      · refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
        simp [smul_eq_mul, mul_comm]
      · intro x hx
        have : g x = 0 := image_eq_zero_of_notMem_tsupport fun hx' =>
          hx (Ioo_subset_Ioc_self (hgs hx'))
        simp [this])
  have heq : EqOn f 0 (Ioo 0 L) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) ((ae_restrict_iff' measurableSet_Ioo).mpr hae)
      isOpen_Ioo hf.continuousOn continuousOn_const
  have := heq.of_subset_closure hf.continuousOn continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hL.ne])
  exact fun x hx => this hx

namespace EBBeam

variable (b : EBBeam)

private theorem i2 (f : ℝ → ℝ) (y : ℝ) : iteratedDeriv 2 f y = deriv (deriv f) y := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

private theorem i3 (f : ℝ → ℝ) (y : ℝ) : iteratedDeriv 3 f y = deriv (deriv (deriv f)) y := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]

private theorem i4 (f : ℝ → ℝ) (y : ℝ) :
    iteratedDeriv 4 f y = deriv (deriv (deriv (deriv f))) y := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]

/-- **Green's formula** for the beam operator:
`∫₀ᴸ EI w'' v'' = EI [w'' v']₀ᴸ - EI [w''' v]₀ᴸ + ∫₀ᴸ EI w'''' v`. -/
theorem green_formula {w v : ℝ → ℝ} (hw : ContDiff ℝ 4 w) (hv : ContDiff ℝ 2 v) :
    ∫ x in (0)..b.L, b.EI * iteratedDeriv 2 w x * iteratedDeriv 2 v x =
      b.EI * (iteratedDeriv 2 w b.L * deriv v b.L - iteratedDeriv 2 w 0 * deriv v 0)
      - b.EI * (iteratedDeriv 3 w b.L * v b.L - iteratedDeriv 3 w 0 * v 0)
      + ∫ x in (0)..b.L, b.EI * iteratedDeriv 4 w x * v x := by
  simp only [i2, i3, i4]
  have hw2 : ContDiff ℝ 2 (deriv (deriv w)) := by
    have := hw.iterate_deriv' 2 2; simpa using this
  have hw3 : ContDiff ℝ 1 (deriv (deriv (deriv w))) := by
    have := hw.iterate_deriv' 1 3; simpa using this
  have hw4 : Continuous (deriv (deriv (deriv (deriv w)))) := by
    have := hw.iterate_deriv' 0 4; simpa using this.continuous
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hv2 : Continuous (deriv (deriv v)) := by
    have := hv.iterate_deriv' 0 2; simpa using this.continuous
  -- first integration by parts: `∫ (EI w'') v'' = [EI w'' v'] - ∫ (EI w''') v'`
  have ibp1 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := b.L)
    (u := fun x => b.EI * deriv (deriv w) x) (u' := fun x => b.EI * deriv (deriv (deriv w)) x)
    (v := deriv v) (v' := deriv (deriv v))
    (fun x _ => ((hw2.differentiable (by norm_num) x).hasDerivAt.const_mul b.EI))
    (fun x _ => (hv1.differentiable (by norm_num) x).hasDerivAt)
    ((hw3.continuous.const_mul _).intervalIntegrable _ _) (hv2.intervalIntegrable _ _)
  -- second integration by parts: `∫ (EI w''') v' = [EI w''' v] - ∫ (EI w'''') v`
  have ibp2 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := b.L)
    (u := fun x => b.EI * deriv (deriv (deriv w)) x)
    (u' := fun x => b.EI * deriv (deriv (deriv (deriv w))) x) (v := v) (v' := deriv v)
    (fun x _ => ((hw3.differentiable (by norm_num) x).hasDerivAt.const_mul b.EI))
    (fun x _ => (hv.differentiable (by norm_num) x).hasDerivAt)
    ((hw4.const_mul _).intervalIntegrable _ _) (hv1.continuous.intervalIntegrable _ _)
  rw [ibp1, ibp2]
  ring

/-- **Strong form ⇔ weak form** (equivalently, stationarity of the potential energy) for a
`C⁴` deflection with `w(0) = w(L) = 0`. The conditions `w''(0) = w''(L) = 0` are the *natural*
boundary conditions of the simply supported beam. [Reddy2007], §3.3. -/
theorem weak_iff_strong {q w : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w) :
    (b.Equation q w ∧ iteratedDeriv 2 w 0 = 0 ∧ iteratedDeriv 2 w b.L = 0) ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → v 0 = 0 → v b.L = 0 →
        ∫ x in (0)..b.L, b.EI * iteratedDeriv 2 w x * iteratedDeriv 2 v x =
          ∫ x in (0)..b.L, q x * v x := by
  have hEI := b.EI_pos.ne'
  have hL := b.L_pos
  have hw4c : Continuous (iteratedDeriv 4 w) := hw.continuous_iteratedDeriv 4 le_rfl
  constructor
  · rintro ⟨heq, h20, h2L⟩ v hv hv0 hvL
    rw [b.green_formula hw hv, h20, h2L, hv0, hvL]
    simp only [zero_mul, sub_zero, mul_zero, zero_add]
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le hL.le] at hx
    rw [heq x hx]
  · intro h
    -- the residual `r = EI w'''' - q`
    let r := fun x => b.EI * iteratedDeriv 4 w x - q x
    have hr : Continuous r := (hw4c.const_mul _).sub hq
    have key : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → v 0 = 0 → v b.L = 0 →
        b.EI * (iteratedDeriv 2 w b.L * deriv v b.L - iteratedDeriv 2 w 0 * deriv v 0)
          + ∫ x in (0)..b.L, r x * v x = 0 := by
      intro v hv hv0 hvL
      have g := b.green_formula hw hv
      rw [h v hv hv0 hvL, hv0, hvL] at g
      have hint : ∫ x in (0)..b.L, r x * v x =
          (∫ x in (0)..b.L, b.EI * iteratedDeriv 4 w x * v x) - ∫ x in (0)..b.L, q x * v x := by
        have e : (fun x => r x * v x) =
            fun x => b.EI * iteratedDeriv 4 w x * v x - q x * v x := by
          ext x; simp only [r]; ring
        rw [show (∫ x in (0)..b.L, r x * v x) =
            ∫ x in (0)..b.L, (b.EI * iteratedDeriv 4 w x * v x - q x * v x) by rw [e]]
        have hvc := hv.continuous
        apply intervalIntegral.integral_sub <;> apply Continuous.intervalIntegrable <;> fun_prop
      rw [hint]
      simp only [mul_zero, sub_zero] at g
      linarith
    -- the equation, from test functions supported in `(0, L)`
    have hres : ∀ x ∈ Icc 0 b.L, r x = 0 := by
      refine eq_zero_of_integral_mul_eq_zero hL hr fun φ hφ hφc hφs => ?_
      have hφ0 : (0 : ℝ) ∉ tsupport φ := fun h0 => (lt_irrefl _ (hφs h0).1)
      have hφL : b.L ∉ tsupport φ := fun h0 => (lt_irrefl _ (hφs h0).2)
      have d0 : deriv φ 0 = 0 :=
        Function.notMem_support.mp fun h' => hφ0 (support_deriv_subset h')
      have dL : deriv φ b.L = 0 :=
        Function.notMem_support.mp fun h' => hφL (support_deriv_subset h')
      have := key φ (hφ.of_le (by norm_num)) (image_eq_zero_of_notMem_tsupport hφ0)
        (image_eq_zero_of_notMem_tsupport hφL)
      rw [d0, dL] at this
      simpa using this
    have heq : b.Equation q w := fun x hx => by
      have := hres x hx; simp only [r] at this; linarith
    have hint0 : ∀ v : ℝ → ℝ, ∫ x in (0)..b.L, r x * v x = 0 := fun v => by
      rw [integral_congr (g := fun _ => 0) fun x hx => by
        rw [uIcc_of_le hL.le] at hx; simp [hres x hx]]
      simp
    -- natural boundary conditions, from two cubic variations
    let v₁ : ℝ[X] := C (b.L ^ 2)⁻¹ * (X ^ 2 * (X - C b.L))
    let v₂ : ℝ[X] := C (b.L ^ 2)⁻¹ * (X * (X - C b.L) ^ 2)
    have hL0 := hL.ne'
    have k₁ := key (fun x => v₁.eval x) (contDiff_eval _ _) (by simp [v₁]) (by simp [v₁])
    have k₂ := key (fun x => v₂.eval x) (contDiff_eval _ _) (by simp [v₂]) (by simp [v₂])
    rw [hint0, add_zero, deriv_eval, deriv_eval] at k₁ k₂
    have e₁ : (derivative v₁).eval b.L = 1 ∧ (derivative v₁).eval 0 = 0 := by
      constructor <;> · simp only [v₁]; beam_poly
    have e₂ : (derivative v₂).eval b.L = 0 ∧ (derivative v₂).eval 0 = 1 := by
      constructor <;> · simp only [v₂]; beam_poly
    rw [e₁.1, e₁.2] at k₁
    rw [e₂.1, e₂.2] at k₂
    refine ⟨heq, ?_, ?_⟩
    · have : b.EI * iteratedDeriv 2 w 0 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hEI
    · have : b.EI * iteratedDeriv 2 w b.L = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hEI

/-! ### The potential energy -/

/-- The **total potential energy** `Π(w) = ∫₀ᴸ (½ EI w''² - q w)`. [Reddy2007], §3.3. -/
noncomputable def energy (q w : ℝ → ℝ) : ℝ :=
  ∫ x in (0)..b.L, (b.EI / 2 * iteratedDeriv 2 w x ^ 2 - q x * w x)

/-- The **first variation** `δΠ(w)[v] = ∫₀ᴸ (EI w'' v'' - q v)`. -/
noncomputable def firstVariation (q w v : ℝ → ℝ) : ℝ :=
  ∫ x in (0)..b.L, (b.EI * iteratedDeriv 2 w x * iteratedDeriv 2 v x - q x * v x)

/-- Exact expansion `Π(w + ε v) = Π(w) + ε δΠ(w)[v] + ε² ∫ ½ EI v''²`. -/
theorem energy_add_smul {q w v : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 2 w)
    (hv : ContDiff ℝ 2 v) (ε : ℝ) :
    b.energy q (w + ε • v) = b.energy q w + ε * b.firstVariation q w v
      + ε ^ 2 * ∫ x in (0)..b.L, b.EI / 2 * iteratedDeriv 2 v x ^ 2 := by
  have hw2 := hw.continuous_iteratedDeriv 2 le_rfl
  have hv2 := hv.continuous_iteratedDeriv 2 le_rfl
  have hd : ∀ x, iteratedDeriv 2 (w + ε • v) x = iteratedDeriv 2 w x + ε * iteratedDeriv 2 v x :=
    fun x => by
      have hsv : ContDiffAt ℝ 2 (ε • v) x := (hv.const_smul ε).contDiffAt
      rw [iteratedDeriv_add hw.contDiffAt hsv, iteratedDeriv_const_smul hv.contDiffAt, smul_eq_mul]
  simp only [energy, firstVariation, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
  · refine integral_congr fun x _ => ?_
    ring
  all_goals
    have hwc := hw.continuous
    have hvc := hv.continuous
    apply Continuous.intervalIntegrable
    fun_prop

/-- `d/dε Π(w + ε v)|_{ε=0} = δΠ(w)[v]`. -/
theorem hasDerivAt_energy {q w v : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 2 w)
    (hv : ContDiff ℝ 2 v) :
    HasDerivAt (fun ε : ℝ => b.energy q (w + ε • v)) (b.firstVariation q w v) 0 := by
  simp only [b.energy_add_smul hq hw hv]
  set c := ∫ x in (0)..b.L, b.EI / 2 * iteratedDeriv 2 v x ^ 2
  have := ((hasDerivAt_id (0 : ℝ)).mul_const (b.firstVariation q w v)).const_add (b.energy q w)
    |>.add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)
  convert this using 1
  · ext ε; simp
  · simp

/-- **Principle of minimum potential energy**: a `C⁴` simply supported solution of
`EI w'''' = q` minimises `Π` among `C²` deflections `u` with `u(0) = u(L) = 0`.
[Reddy2007], §3.3. -/
theorem energy_le {q w u : ℝ → ℝ} (hq : Continuous q) (hw : ContDiff ℝ 4 w)
    (hu : ContDiff ℝ 2 u) (heq : b.Equation q w) (hbc : b.SimplySupported w)
    (hu0 : u 0 = 0) (huL : u b.L = 0) : b.energy q w ≤ b.energy q u := by
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hv : ContDiff ℝ 2 (u - w) := hu.sub hw2
  have hweak := (b.weak_iff_strong hq hw).mp ⟨heq, hbc.2.1, hbc.2.2.2⟩ (u - w) hv
    (by simp [hu0, hbc.1]) (by simp [huL, hbc.2.2.1])
  have hfv : b.firstVariation q w (u - w) = 0 := by
    rw [firstVariation, intervalIntegral.integral_sub, hweak, sub_self]
    · exact ((((hw.continuous_iteratedDeriv 2 (by norm_num)).const_mul _).mul
        (hv.continuous_iteratedDeriv 2 le_rfl))).intervalIntegrable _ _
    · exact (hq.mul hv.continuous).intervalIntegrable _ _
  have e := b.energy_add_smul hq hw2 hv 1
  rw [one_smul, add_sub_cancel, hfv] at e
  rw [e]
  have : 0 ≤ ∫ x in (0)..b.L, b.EI / 2 * iteratedDeriv 2 (u - w) x ^ 2 :=
    integral_nonneg b.L_pos.le fun x _ => by have := b.EI_pos; positivity
  linarith

end EBBeam

end ContinuumMechanics.Beams
