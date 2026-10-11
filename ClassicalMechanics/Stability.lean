import ClassicalMechanics.SmallOscillations
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stability of equilibria: the Lagrange–Dirichlet theorem and linearization

A **natural system** on `ℝⁿ` has a constant symmetric positive definite mass matrix `M` and a
potential `U` with gradient `∇U`; its equations of motion are

`M q̈ = -∇U(q)`

([Arnold1989], §§22–23; [Goldstein2002], §6.1).

* **Equilibria** (`isMotion_rest_iff`, `gradU_eq_zero_of_const`): the constant motion `q ≡ q*`
  is a motion iff `∇U(q*) = 0`, and every motion with constant position sits at a critical
  point of `U`.
* **Energy** (`energy_const`): `E = ½ q̇ · M q̇ + U(q)` is conserved.
* **Lagrange–Dirichlet theorem** (`lagrange_dirichlet`): if `q*` is a strict minimum of `U` on
  the closed ball of radius `r`, then for every `ε ∈ (0, r]` there is `δ > 0` such that every
  motion starting `δ`-close to `(q*, 0)` in phase space stays `ε`-close to it for all times
  (Lyapunov stability). The proof uses the energy as a Lyapunov function: the minimum `m` of
  `U - U(q*)` on the sphere `‖q - q*‖ = ε` is positive by compactness, the initial energy
  exceeds `U(q*)` by less than `m`, and by the intermediate value theorem the motion can never
  reach the sphere.
* **Linearization** (`linearized_force`, `linearization`): if `∇U` has derivative `K` (the
  Hessian) at an equilibrium, the force is `-K ξ + o(ξ)` in the displacement `ξ = q - q*`, so
  the linearized equations are the small oscillations `M ξ̈ + K ξ = 0`.
* **Second-derivative test** (`quadratic_growth_of_posDef`, `strictMin_of_posDef`): a positive
  definite Hessian gives the quadratic growth `U(q) ≥ U(q*) + c ‖q - q*‖²` near `q*`, hence a
  strict local minimum, hence stability (`lyapunovStable_of_posDef`).

## References

* [Arnold1989] V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §§22–23.
* [Goldstein2002] H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., §6.1.
* [Lyapunov1892] A. M. Lyapunov, *The general problem of the stability of motion* (1892).
-/

open Matrix Filter Topology

noncomputable section

namespace ClassicalMechanics

variable {n : ℕ}

/-- A positive definite matrix is coercive: `c ‖v‖² ≤ v · A v` for some `c > 0`. -/
theorem exists_coercive_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℝ, c * ‖v‖ ^ 2 ≤ v ⬝ᵥ A *ᵥ v := by
  have hcont : Continuous fun v : Fin n → ℝ => v ⬝ᵥ A *ᵥ v :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hsph : ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with hs | hs
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have h := hsph v hv
      rw [hs] at h
      exact h
    simp [hv]
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere 0 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have hpos : 0 < u ⬝ᵥ A *ᵥ u := by simpa using hA.dotProduct_mulVec_pos hu0
    refine ⟨_, hpos, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have h := isMinOn_iff.mp hmin _ (hsph v hv)
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      calc u ⬝ᵥ A *ᵥ u * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ A *ᵥ v)) * ‖v‖ ^ 2 := by gcongr
        _ = v ⬝ᵥ A *ᵥ v := by field_simp

/-- In the sup norm, `|x · y| ≤ n ‖x‖ ‖y‖`. -/
theorem abs_dotProduct_le_card_mul (x y : Fin n → ℝ) : |x ⬝ᵥ y| ≤ n * (‖x‖ * ‖y‖) := by
  unfold dotProduct
  calc |∑ i, x i * y i| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul ((Real.norm_eq_abs (x i)).symm.trans_le (norm_le_pi_norm x i))
          ((Real.norm_eq_abs (y i)).symm.trans_le (norm_le_pi_norm y i)) (abs_nonneg _)
          (norm_nonneg _)
    _ = n * (‖x‖ * ‖y‖) := by simp

/-- A **natural system** `M q̈ = -∇U(q)` on `ℝⁿ`: a constant symmetric positive definite mass
matrix `M` and a differentiable potential `U` with gradient `gradU`. -/
structure NaturalSystem (n : ℕ) where
  M : Matrix (Fin n) (Fin n) ℝ
  M_symm : Mᵀ = M
  M_posDef : M.PosDef
  U : (Fin n → ℝ) → ℝ
  gradU : (Fin n → ℝ) → Fin n → ℝ
  hasFDerivAt_U : ∀ q, HasFDerivAt U (dotCLM (gradU q)) q

namespace NaturalSystem

variable (S : NaturalSystem n)

/-- A motion of the natural system: `M q̈ = -∇U(q)`. -/
def IsMotion (γ : MotionN n) : Prop := ∀ t, S.M *ᵥ γ.a t = -S.gradU (γ.q t)

/-- The potential is continuous. -/
theorem continuous_U : Continuous S.U :=
  continuous_iff_continuousAt.2 fun q => (S.hasFDerivAt_U q).continuousAt

/-! ### Equilibria -/

/-- The motion resting at `q`. -/
def rest (q : Fin n → ℝ) : MotionN n where
  q _ := q
  v _ := 0
  a _ := 0
  hasDerivAt_q _ := hasDerivAt_const _ _
  hasDerivAt_v _ := hasDerivAt_const _ _

/-- **Equilibria**: the rest motion at `q` is a motion iff `∇U(q) = 0`. -/
theorem isMotion_rest_iff (q : Fin n → ℝ) : S.IsMotion (rest q) ↔ S.gradU q = 0 := by
  constructor
  · intro h
    have h0 := h 0
    simp only [rest, mulVec_zero] at h0
    exact neg_eq_zero.mp h0.symm
  · intro h t
    simp [rest, h]

/-- A motion with constant position `q` forces `∇U(q) = 0`. -/
theorem gradU_eq_zero_of_const {γ : MotionN n} (h : S.IsMotion γ) {q : Fin n → ℝ}
    (hq : ∀ t, γ.q t = q) : S.gradU q = 0 := by
  have hv : ∀ t, γ.v t = 0 := fun t => by
    have h2 : HasDerivAt γ.q 0 t := by
      rw [show γ.q = fun _ => q from funext hq]
      exact hasDerivAt_const _ _
    exact (γ.hasDerivAt_q t).unique h2
  have ha : γ.a 0 = 0 := by
    have h2 : HasDerivAt γ.v 0 0 := by
      rw [show γ.v = fun _ => 0 from funext hv]
      exact hasDerivAt_const _ _
    exact (γ.hasDerivAt_v 0).unique h2
  have h0 := h 0
  rw [ha, mulVec_zero, hq] at h0
  exact neg_eq_zero.mp h0.symm

/-! ### Energy -/

/-- The kinetic energy `½ v · M v`. -/
def kinetic (v : Fin n → ℝ) : ℝ := (v ⬝ᵥ S.M *ᵥ v) / 2

/-- The kinetic energy is nonnegative. -/
theorem kinetic_nonneg (v : Fin n → ℝ) : 0 ≤ S.kinetic v := by
  have h := S.M_posDef.posSemidef.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h
  unfold kinetic
  positivity

/-- The kinetic energy is continuous. -/
theorem continuous_kinetic : Continuous S.kinetic :=
  (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).div_const 2

/-- The total energy `E = ½ q̇ · M q̇ + U(q)` along a motion. -/
def energy (γ : MotionN n) (t : ℝ) : ℝ := S.kinetic (γ.v t) + S.U (γ.q t)

/-- **Conservation of energy** for a natural system. -/
theorem energy_const {γ : MotionN n} (h : S.IsMotion γ) (s t : ℝ) :
    S.energy γ s = S.energy γ t := by
  refine eq_of_hasDerivAt_zero (fun t => ?_) s t
  have h1 := hasDerivAt_dotN (γ.hasDerivAt_v t) (hasDerivAt_mulVec S.M (γ.hasDerivAt_v t))
  have h2 := (S.hasFDerivAt_U (γ.q t)).comp_hasDerivAt t (γ.hasDerivAt_q t)
  convert (h1.div_const 2).add h2 using 1
  · funext x; rfl
  rw [dotCLM_apply, dot_mulVec_comm S.M_symm (γ.a t), h t, dotProduct_neg,
    dotProduct_comm (S.gradU _)]
  ring

/-! ### The Lagrange–Dirichlet theorem -/

/-- **Lagrange–Dirichlet theorem** (Lyapunov stability in phase space). If `U` has a strict
minimum at `q*` on the closed ball of radius `r`, then for every `ε ∈ (0, r]` there is `δ > 0`
such that every motion with `‖q(0) - q*‖ < δ` and `‖q̇(0)‖ < δ` satisfies `‖q(t) - q*‖ < ε` and
`‖q̇(t)‖ < ε` for all times `t`. -/
theorem lagrange_dirichlet {qs : Fin n → ℝ} {r : ℝ}
    (hmin : ∀ q, 0 < ‖q - qs‖ → ‖q - qs‖ ≤ r → S.U qs < S.U q)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) :
    ∃ δ > 0, ∀ γ : MotionN n, S.IsMotion γ → ‖γ.q 0 - qs‖ < δ → ‖γ.v 0‖ < δ →
      ∀ t, ‖γ.q t - qs‖ < ε ∧ ‖γ.v t‖ < ε := by
  -- the energy barrier `m` on the sphere `‖q - q*‖ = ε`
  obtain ⟨m, hm, hmS⟩ : ∃ m > 0, ∀ q ∈ Metric.sphere qs ε, S.U qs + m ≤ S.U q := by
    rcases (Metric.sphere qs ε).eq_empty_or_nonempty with hs | hs
    · exact ⟨1, one_pos, by simp [hs]⟩
    · obtain ⟨q0, hq0, hq0min⟩ :=
        (isCompact_sphere qs ε).exists_isMinOn hs S.continuous_U.continuousOn
      have hd : ‖q0 - qs‖ = ε := mem_sphere_iff_norm.mp hq0
      refine ⟨S.U q0 - S.U qs, sub_pos.2 (hmin q0 (hd ▸ hε) (hd ▸ hεr)), fun q hq => ?_⟩
      have := isMinOn_iff.mp hq0min q hq
      linarith
  obtain ⟨c, hc, hcM⟩ := exists_coercive_of_posDef S.M_posDef
  set η := min m (c * ε ^ 2 / 2) with hη_def
  have hη : 0 < η := lt_min hm (by positivity)
  -- continuity of the energy function at `(q*, 0)`
  have hF : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => S.kinetic p.2 + S.U p.1 :=
    (S.continuous_kinetic.comp continuous_snd).add (S.continuous_U.comp continuous_fst)
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousAt_iff.1 (hF.continuousAt (x := (qs, 0))) η hη
  refine ⟨min δ₀ ε, lt_min hδ₀ hε, fun γ hγ h0 hv0 => ?_⟩
  have hE0 : S.energy γ 0 < S.U qs + η := by
    have hd := hδ (x := (γ.q 0, γ.v 0)) (by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm, sub_zero]
      exact ⟨h0.trans_le (min_le_left _ _), hv0.trans_le (min_le_left _ _)⟩)
    rw [Real.dist_eq] at hd
    have hk0 : S.kinetic 0 = 0 := by simp [kinetic]
    simp only [hk0, zero_add] at hd
    have := (abs_lt.1 hd).2
    unfold energy
    linarith
  have hE : ∀ t, S.energy γ t < S.U qs + η := fun t => S.energy_const hγ t 0 ▸ hE0
  -- the motion never reaches the sphere
  have hpos : ∀ t, ‖γ.q t - qs‖ < ε := by
    intro t
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have hcq : Continuous γ.q :=
      continuous_iff_continuousAt.2 fun t => (γ.hasDerivAt_q t).continuousAt
    have hf : ContinuousOn (fun s => ‖γ.q s - qs‖) (Set.uIcc 0 t) :=
      (hcq.sub continuous_const).norm.continuousOn
    have hmem : ε ∈ Set.uIcc ‖γ.q 0 - qs‖ ‖γ.q t - qs‖ :=
      Set.mem_uIcc.2 (Or.inl ⟨(h0.trans_le (min_le_right _ _)).le, hcon⟩)
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hf hmem
    have h1 := hmS _ (mem_sphere_iff_norm.mpr hs)
    have h2 := hE s
    have h3 := S.kinetic_nonneg (γ.v s)
    have : η ≤ m := min_le_left _ _
    unfold energy at h2
    linarith
  refine fun t => ⟨hpos t, ?_⟩
  -- the velocity stays small
  have hU : S.U qs ≤ S.U (γ.q t) := by
    rcases eq_or_lt_of_le (norm_nonneg (γ.q t - qs)) with h | h
    · rw [eq_comm, norm_eq_zero, sub_eq_zero] at h
      rw [h]
    · exact (hmin _ h ((hpos t).le.trans hεr)).le
  have h2 := hE t
  unfold energy kinetic at h2
  have h3 := hcM (γ.v t)
  have : η ≤ c * ε ^ 2 / 2 := min_le_right _ _
  have h4 : c * ‖γ.v t‖ ^ 2 < c * ε ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_mul_lt_mul_left h4 hc.le)

/-- **Lagrange–Dirichlet theorem**, configuration-space form: motions starting close enough to a
strict minimum of `U` with small enough velocity remain `ε`-close to it forever. -/
theorem lagrange_dirichlet_position {qs : Fin n → ℝ} {r : ℝ}
    (hmin : ∀ q, 0 < ‖q - qs‖ → ‖q - qs‖ ≤ r → S.U qs < S.U q)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) :
    ∃ δ > 0, ∀ γ : MotionN n, S.IsMotion γ → ‖γ.q 0 - qs‖ < δ → ‖γ.v 0‖ < δ →
      ∀ t, 0 ≤ t → ‖γ.q t - qs‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := S.lagrange_dirichlet hmin hε hεr
  exact ⟨δ, hδ, fun γ hγ h0 hv0 t _ => (h γ hγ h0 hv0 t).1⟩

/-! ### Linearization about an equilibrium -/

/-- `K` is the **Hessian** of `U` at `q*`: the gradient `∇U` has derivative `ξ ↦ K ξ` at
`q*`. -/
def HasHessian (K : Matrix (Fin n) (Fin n) ℝ) (qs : Fin n → ℝ) : Prop :=
  HasFDerivAt S.gradU (LinearMap.toContinuousLinearMap (Matrix.toLin' K)) qs

/-- The **linearized system** `M ξ̈ + K ξ = 0` about an equilibrium with symmetric Hessian `K`. -/
def linearization (K : Matrix (Fin n) (Fin n) ℝ) (hK : Kᵀ = K) : SmallOscillations n :=
  ⟨S.M, K, S.M_symm, hK, S.M_posDef⟩

/-- **Linearized force**: at an equilibrium with Hessian `K`, the force is
`-∇U(q* + ξ) = -K ξ + o(ξ)`, so the linearized equations are `M ξ̈ + K ξ = 0`. -/
theorem linearized_force {K : Matrix (Fin n) (Fin n) ℝ} {qs : Fin n → ℝ}
    (hK : S.HasHessian K qs) (heq : S.gradU qs = 0) :
    (fun ξ => -S.gradU (qs + ξ) - -(K *ᵥ ξ)) =o[𝓝 0] fun ξ => ξ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hK).neg_left
  refine h.congr_left fun ξ => ?_
  simp [heq, sub_eq_add_neg, add_comm]

/-- A motion `q = q* + ξ` of the natural system satisfies the linearized equation
`M ξ̈ + K ξ = -R(ξ)` with the nonlinear remainder `R(ξ) = ∇U(q* + ξ) - K ξ = o(ξ)`. -/
theorem isMotion_iff_linearized (K : Matrix (Fin n) (Fin n) ℝ) (qs : Fin n → ℝ)
    (γ : MotionN n) :
    S.IsMotion γ ↔ ∀ t, S.M *ᵥ γ.a t + K *ᵥ (γ.q t - qs) =
      -(S.gradU (qs + (γ.q t - qs)) - K *ᵥ (γ.q t - qs)) := by
  refine forall_congr' fun t => ?_
  rw [add_sub_cancel]
  constructor <;> intro h
  · rw [h]; abel
  · calc S.M *ᵥ γ.a t = (S.M *ᵥ γ.a t + K *ᵥ (γ.q t - qs)) - K *ᵥ (γ.q t - qs) := by abel
      _ = -S.gradU (γ.q t) := by rw [h]; abel

/-- **Second-derivative test**, quantitative form: at an equilibrium with positive definite
Hessian `K`, `U` grows quadratically, `U(q) ≥ U(q*) + c ‖q - q*‖²` near `q*`. -/
theorem quadratic_growth_of_posDef {K : Matrix (Fin n) (Fin n) ℝ} {qs : Fin n → ℝ}
    (hK : S.HasHessian K qs) (heq : S.gradU qs = 0) (hKpos : K.PosDef) :
    ∃ r > 0, ∃ c > 0, ∀ q, ‖q - qs‖ ≤ r → S.U qs + c * ‖q - qs‖ ^ 2 ≤ S.U q := by
  obtain ⟨c, hc, hcK⟩ := exists_coercive_of_posDef hKpos
  set κ := c / (2 * (n + 1)) with hκ_def
  have hκ : 0 < κ := by positivity
  have hnκ : n * κ ≤ c / 2 := by
    have : (n + 1) * κ = c / 2 := by rw [hκ_def]; field_simp
    nlinarith
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hK).def hκ
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  refine ⟨ρ / 2, by positivity, c / 4, by positivity, fun q hq => ?_⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = q - qs := ⟨_, rfl⟩
  rw [← hξ] at hq ⊢
  have hR : ∀ w : Fin n → ℝ, ‖w‖ ≤ ‖ξ‖ → ‖S.gradU (qs + w) - K *ᵥ w‖ ≤ κ * ‖w‖ := by
    intro w hw
    have := hball (y := w) (by rw [dist_zero_right]; linarith)
    simpa [heq] using this
  -- `h(s) = U(q* + s ξ) - (c/4) s² ‖ξ‖²` is monotone on `[0, 1]`
  let h : ℝ → ℝ := fun s => S.U (qs + s • ξ) - c / 4 * s ^ 2 * ‖ξ‖ ^ 2
  let h' : ℝ → ℝ := fun s => S.gradU (qs + s • ξ) ⬝ᵥ ξ - c / 2 * s * ‖ξ‖ ^ 2
  have hderiv : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => qs + s • ξ) ξ s := by
      simpa using ((hasDerivAt_id s).smul_const ξ).const_add qs
    have hU := (S.hasFDerivAt_U (qs + s • ξ)).comp_hasDerivAt s hl
    have hq : HasDerivAt (fun s : ℝ => c / 4 * s ^ 2 * ‖ξ‖ ^ 2) (c / 2 * s * ‖ξ‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (c / 4)).mul_const (‖ξ‖ ^ 2)
      convert this using 1
      push_cast
      ring
    convert hU.sub hq using 1 <;> rfl
  have hmono : MonotoneOn h (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
      (fun s _ => (hderiv s).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hw : ‖s • ξ‖ ≤ ‖ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs0.le]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1.le
    have hRs := hR _ hw
    rw [norm_smul, Real.norm_of_nonneg hs0.le] at hRs
    have hdot := abs_dotProduct_le_card_mul (S.gradU (qs + s • ξ) - K *ᵥ (s • ξ)) ξ
    have hsplit : S.gradU (qs + s • ξ) ⬝ᵥ ξ =
        s * (ξ ⬝ᵥ K *ᵥ ξ) + (S.gradU (qs + s • ξ) - K *ᵥ (s • ξ)) ⬝ᵥ ξ := by
      rw [sub_dotProduct, mulVec_smul, smul_dotProduct, smul_eq_mul, dotProduct_comm (K *ᵥ ξ)]
      ring
    have hcξ := hcK ξ
    have hb : n * (‖S.gradU (qs + s • ξ) - K *ᵥ (s • ξ)‖ * ‖ξ‖) ≤ c / 2 * s * ‖ξ‖ ^ 2 := by
      calc n * (‖S.gradU (qs + s • ξ) - K *ᵥ (s • ξ)‖ * ‖ξ‖)
          ≤ n * (κ * (s * ‖ξ‖) * ‖ξ‖) := by gcongr
        _ = (n * κ) * s * ‖ξ‖ ^ 2 := by ring
        _ ≤ c / 2 * s * ‖ξ‖ ^ 2 := by gcongr
    have hlow := neg_abs_le ((S.gradU (qs + s • ξ) - K *ᵥ (s • ξ)) ⬝ᵥ ξ)
    have hsc : s * (c * ‖ξ‖ ^ 2) ≤ s * (ξ ⬝ᵥ K *ᵥ ξ) := by gcongr
    simp only [h']
    nlinarith
  have h01 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  simp only [h, zero_smul, add_zero, one_smul, hξ, add_sub_cancel] at h01
  rw [hξ]
  norm_num at h01
  linarith

/-- **Second-derivative test**: at an equilibrium with positive definite Hessian, `q*` is a
strict minimum of `U` on a closed ball around it. -/
theorem strictMin_of_posDef {K : Matrix (Fin n) (Fin n) ℝ} {qs : Fin n → ℝ}
    (hK : S.HasHessian K qs) (heq : S.gradU qs = 0) (hKpos : K.PosDef) :
    ∃ r > 0, ∀ q, 0 < ‖q - qs‖ → ‖q - qs‖ ≤ r → S.U qs < S.U q := by
  obtain ⟨r, hr, c, hc, h⟩ := S.quadratic_growth_of_posDef hK heq hKpos
  exact ⟨r, hr, fun q hq hqr => by have := h q hqr; nlinarith [pow_pos hq 2]⟩

/-- **Stability from the Hessian**: an equilibrium with positive definite Hessian is Lyapunov
stable in phase space (the linearized system then has real frequencies, see
`SmallOscillations.omega_sq_pos`). -/
theorem lyapunovStable_of_posDef {K : Matrix (Fin n) (Fin n) ℝ} {qs : Fin n → ℝ}
    (hK : S.HasHessian K qs) (heq : S.gradU qs = 0) (hKpos : K.PosDef) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r → ∃ δ > 0, ∀ γ : MotionN n, S.IsMotion γ →
      ‖γ.q 0 - qs‖ < δ → ‖γ.v 0‖ < δ → ∀ t, ‖γ.q t - qs‖ < ε ∧ ‖γ.v t‖ < ε := by
  obtain ⟨r, hr, hmin⟩ := S.strictMin_of_posDef hK heq hKpos
  exact ⟨r, hr, fun ε hε hεr => S.lagrange_dirichlet hmin hε hεr⟩

end NaturalSystem

end ClassicalMechanics
