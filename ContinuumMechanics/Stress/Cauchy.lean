import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ContinuumMechanics.Stress.Triangle
import ContinuumMechanics.Tensor.Second

/-!
# Cauchy's theorem via the tetrahedron argument

Let `t(x, n)` be a **traction field**: the force per unit area exerted across a surface through
`x` with unit normal `n`. Cauchy's theorem states that balance of forces forces `t` to be linear
in `n`: there is a tensor field `σ` with `t(x, n) = σ(x) n`.

We prove it from the balance of forces on **Cauchy tetrahedra**: given a point `x`, an orthonormal
frame `(e₀, e₁, e₂)` and a unit normal `n` with all `nᵢ = n · eᵢ > 0`, the tetrahedron with
vertices `x` and `x + (h / nᵢ) eᵢ` has three faces with outer normals `-eᵢ` and one face with
outer normal `n`. Balance of forces on it reads

`Σ_faces ∫_F t(y, n_F) dA + ∫_T b dV = 0`,

where `b` collects the body force and the inertial force density. The surface integrals over the
flat faces are the triangle integrals of `ContinuumMechanics.Stress.Triangle`; nothing about the
geometry is assumed. The face areas are `h²/(2nⱼnₖ)` and `h²/(2n₀n₁n₂)` while the volume is
`O(h³)`, so dividing by `h²` and letting `h → 0` gives

`t(x, n) + Σᵢ nᵢ t(x, -eᵢ) = 0`.

Continuity of `t(x, ·)` on the unit sphere extends this to the closed octant. With `n = e₀`, it
gives **Cauchy's reciprocal theorem** `t(x, -n) = -t(x, n)`. Flipping the frame into the octant of
an arbitrary `n` then gives `t(x, n) = Σᵢ (n · eᵢ) t(x, eᵢ) = σ(x) n` with
`σ(x) = Σᵢ t(x, eᵢ) ⊗ eᵢ` ([Gurtin1981], §14; [MarsdenHughes1983], §2.2).

## Main results

* `ContinuumMechanics.tetra_identity`: the identity above for `n` in the open octant.
* `ContinuumMechanics.traction_neg`: Cauchy's reciprocal theorem.
* `ContinuumMechanics.cauchy_tetrahedron`: **Cauchy's theorem**, `t(x, n) = σ(x) n` with `σ`
  continuous.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §14.
* [MarsdenHughes1983] J. E. Marsden, T. J. R. Hughes, *Mathematical Foundations of Elasticity*,
  §2.2.
-/

open MeasureTheory Metric Set Filter Topology Module
open scoped InnerProductSpace ContinuumMechanics

namespace ContinuumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Geometry

/-- The edge `nᵢ⁻¹ eᵢ` of the unit Cauchy tetrahedron. -/
noncomputable def tetraEdge (n : E) (e : Fin 3 → E) (i : Fin 3) : E := (⟪n, e i⟫_ℝ)⁻¹ • e i

/-- The **Cauchy tetrahedron** with vertices `x` and `x + (h / nᵢ) eᵢ`. [Gurtin1981], §14. -/
noncomputable def cauchyTetra (x n : E) (e : Fin 3 → E) (h : ℝ) : Set E :=
  convexHull ℝ {x, x + h • tetraEdge n e 0, x + h • tetraEdge n e 1, x + h • tetraEdge n e 2}

/-- The total surface force `Σ_F ∫_F t(y, n_F) dA` on the Cauchy tetrahedron: three faces through
`x` with outer normals `-eᵢ`, and the slanted face with outer normal `n`. -/
noncomputable def tetraFlux (t : E → E → E) (x n : E) (e : Fin 3 → E) (h : ℝ) : E :=
  triangleIntegral (fun y => t y (-e 0)) x (h • tetraEdge n e 1) (h • tetraEdge n e 2) +
  triangleIntegral (fun y => t y (-e 1)) x (h • tetraEdge n e 0) (h • tetraEdge n e 2) +
  triangleIntegral (fun y => t y (-e 2)) x (h • tetraEdge n e 0) (h • tetraEdge n e 1) +
  triangleIntegral (fun y => t y n) (x + h • tetraEdge n e 0)
    (h • (tetraEdge n e 1 - tetraEdge n e 0)) (h • (tetraEdge n e 2 - tetraEdge n e 0))

variable {n : E} {e : Fin 3 → E}

theorem norm_tetraEdge (hon : Orthonormal ℝ e) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) (i : Fin 3) :
    ‖tetraEdge n e i‖ = (⟪n, e i⟫_ℝ)⁻¹ := by
  rw [tetraEdge, norm_smul, hon.1 i, mul_one, Real.norm_of_nonneg (inv_nonneg.2 (hpos i).le)]

theorem gramArea_tetraEdge (hon : Orthonormal ℝ e) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) {i j : Fin 3}
    (hij : i ≠ j) :
    gramArea (tetraEdge n e i) (tetraEdge n e j) = (⟪n, e i⟫_ℝ * ⟪n, e j⟫_ℝ)⁻¹ := by
  have h0 : ⟪tetraEdge n e i, tetraEdge n e j⟫_ℝ = 0 := by
    rw [tetraEdge, tetraEdge, real_inner_smul_left, real_inner_smul_right, hon.2 hij, mul_zero,
      mul_zero]
  have hi := hpos i
  have hj := hpos j
  rw [gramArea, norm_tetraEdge hon hpos, norm_tetraEdge hon hpos, h0,
    show (⟪n, e i⟫_ℝ)⁻¹ ^ 2 * (⟪n, e j⟫_ℝ)⁻¹ ^ 2 - 0 ^ 2 = ((⟪n, e i⟫_ℝ * ⟪n, e j⟫_ℝ)⁻¹) ^ 2 by
      rw [zero_pow two_ne_zero, sub_zero, mul_inv, mul_pow],
    Real.sqrt_sq (by positivity)]

/-- An orthonormal triple in a three-dimensional space, as an orthonormal basis. -/
noncomputable def orthonormalBasisOfTriple [Fact (finrank ℝ E = 3)] (hon : Orthonormal ℝ e) :
    OrthonormalBasis (Fin 3) ℝ E :=
  OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin]; exact (Fact.out (p := finrank ℝ E = 3)).symm)).ge

theorem coe_orthonormalBasisOfTriple [Fact (finrank ℝ E = 3)] (hon : Orthonormal ℝ e) :
    ⇑(orthonormalBasisOfTriple hon) = e :=
  OrthonormalBasis.coe_mk _ _

theorem sum_sq_inner_triple [Fact (finrank ℝ E = 3)] (hon : Orthonormal ℝ e) (n : E) :
    ⟪n, e 0⟫_ℝ ^ 2 + ⟪n, e 1⟫_ℝ ^ 2 + ⟪n, e 2⟫_ℝ ^ 2 = ‖n‖ ^ 2 := by
  have := (orthonormalBasisOfTriple hon).sum_sq_inner_left n
  rwa [coe_orthonormalBasisOfTriple, Fin.sum_univ_three] at this

theorem gramArea_tetraEdge_slant [Fact (finrank ℝ E = 3)] (hon : Orthonormal ℝ e)
    (hn : ‖n‖ = 1) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) :
    gramArea (tetraEdge n e 1 - tetraEdge n e 0) (tetraEdge n e 2 - tetraEdge n e 0) =
      (⟪n, e 0⟫_ℝ * ⟪n, e 1⟫_ℝ * ⟪n, e 2⟫_ℝ)⁻¹ := by
  have o := orthonormal_iff_ite.mp hon
  have hs := sum_sq_inner_triple hon n
  rw [hn, one_pow] at hs
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  rw [gramArea, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [tetraEdge, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, o]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (⟪n, e 0⟫_ℝ * ⟪n, e 1⟫_ℝ * ⟪n, e 2⟫_ℝ)⁻¹)]
  congr 1
  field_simp
  linear_combination ⟪n, e 0⟫_ℝ ^ 2 * hs

theorem cauchyTetra_subset (hon : Orthonormal ℝ e) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) (x : E)
    {h : ℝ} (hh : 0 ≤ h) :
    cauchyTetra x n e h ⊆ closedBall x (h * ∑ i, (⟪n, e i⟫_ℝ)⁻¹) := by
  have hR : ∀ i, h * (⟪n, e i⟫_ℝ)⁻¹ ≤ h * ∑ i, (⟪n, e i⟫_ℝ)⁻¹ := fun i =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => (inv_pos.2 (hpos j)).le)
      (Finset.mem_univ i)) hh
  have hv : ∀ i, x + h • tetraEdge n e i ∈ closedBall x (h * ∑ i, (⟪n, e i⟫_ℝ)⁻¹) := fun i => by
    rw [mem_closedBall, dist_self_add_left, norm_smul, norm_tetraEdge hon hpos,
      Real.norm_of_nonneg hh]
    exact hR i
  refine convexHull_min ?_ (convex_closedBall _ _)
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_closedBall_self
    (mul_nonneg hh (Finset.sum_nonneg fun i _ => (inv_pos.2 (hpos i)).le)), hv 0, hv 1, hv 2⟩

end Geometry

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Balance of forces on Cauchy tetrahedra**: for every point `x`, orthonormal frame `e`, unit
normal `n` in the open positive octant of `e` and size `h > 0`, the surface forces on the Cauchy
tetrahedron balance the body force (including inertia) `b`. [Gurtin1981], §14. -/
def TetraBalance (t : E → E → E) (b : E → E) : Prop :=
  ∀ (x n : E) (e : Fin 3 → E), Orthonormal ℝ e → ‖n‖ = 1 → (∀ i, 0 < ⟪n, e i⟫_ℝ) →
    ∀ h : ℝ, 0 < h → tetraFlux t x n e h + ∫ y in cauchyTetra x n e h, b y = 0

variable {t : E → E → E} {b : E → E}

/-- The body force on a shrinking Cauchy tetrahedron is `o(h²)`. -/
theorem tendsto_tetra_volume [Fact (finrank ℝ E = 3)] (hb : Continuous b) (x n : E)
    {e : Fin 3 → E} (hon : Orthonormal ℝ e) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) :
    Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • ∫ y in cauchyTetra x n e h, b y) (𝓝[>] 0) (𝓝 0) := by
  set R := ∑ i, (⟪n, e i⟫_ℝ)⁻¹
  have hR : 0 < R := Finset.sum_pos (fun i _ => inv_pos.2 (hpos i)) Finset.univ_nonempty
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hb.continuousOn
  set K := (volume : Measure E).real (ball 0 1)
  have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ‖(h ^ 2)⁻¹ • ∫ y in cauchyTetra x n e h, b y‖ ≤ |M| * R ^ 3 * K * h := by
    filter_upwards [Ioo_mem_nhdsGT (inv_pos.2 hR)] with h hh
    have hh0 : 0 < h := hh.1
    have hsub := cauchyTetra_subset hon hpos x hh0.le
    have hball : closedBall x (h * R) ⊆ closedBall x 1 :=
      closedBall_subset_closedBall (by
        have := mul_lt_mul_of_pos_right hh.2 hR
        rw [inv_mul_cancel₀ hR.ne'] at this
        exact this.le)
    have hfin : volume (closedBall x (h * R)) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := b)
      ((measure_mono hsub).trans_lt measure_closedBall_lt_top)
      (fun y hy => (hM y (hball (hsub hy))).trans (le_abs_self M))
    have hvol : (volume : Measure E).real (cauchyTetra x n e h) ≤ (h * R) ^ 3 * K := by
      calc (volume : Measure E).real (cauchyTetra x n e h)
          ≤ (volume : Measure E).real (closedBall x (h * R)) := measureReal_mono hsub hfin
        _ = (h * R) ^ 3 * K := by
          rw [Measure.addHaar_real_closedBall _ _ (by positivity), Fact.out (p := finrank ℝ E = 3)]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (h ^ 2)⁻¹ * ‖∫ y in cauchyTetra x n e h, b y‖
        ≤ (h ^ 2)⁻¹ * (|M| * ((h * R) ^ 3 * K)) := by
          gcongr
          exact hint.trans (mul_le_mul_of_nonneg_left hvol (abs_nonneg M))
      _ = |M| * R ^ 3 * K * h := by field_simp
  refine squeeze_zero_norm' hbound ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have : Tendsto (fun h : ℝ => |M| * R ^ 3 * K * h) (𝓝 0) (𝓝 (|M| * R ^ 3 * K * 0)) :=
    tendsto_const_nhds.mul tendsto_id
  simpa using this

/-- **The tetrahedron identity**: `t(x, n) + Σᵢ nᵢ t(x, -eᵢ) = 0` for `n` in the open positive
octant of an orthonormal frame `e`. [Gurtin1981], §14. -/
theorem tetra_identity [Fact (finrank ℝ E = 3)] (ht : ∀ m, Continuous fun y => t y m)
    (hb : Continuous b) (hbal : TetraBalance t b) (x n : E) {e : Fin 3 → E}
    (hon : Orthonormal ℝ e) (hn : ‖n‖ = 1) (hpos : ∀ i, 0 < ⟪n, e i⟫_ℝ) :
    t x n + ∑ i, ⟪n, e i⟫_ℝ • t x (-e i) = 0 := by
  have L := ((((tendsto_triangleIntegral_vertex (ht (-e 0)) x (tetraEdge n e 1)
    (tetraEdge n e 2)).add (tendsto_triangleIntegral_vertex (ht (-e 1)) x (tetraEdge n e 0)
    (tetraEdge n e 2))).add (tendsto_triangleIntegral_vertex (ht (-e 2)) x (tetraEdge n e 0)
    (tetraEdge n e 1))).add (tendsto_triangleIntegral (ht n) x (tetraEdge n e 0)
    (tetraEdge n e 1 - tetraEdge n e 0) (tetraEdge n e 2 - tetraEdge n e 0))).add
    (tendsto_tetra_volume hb x n hon hpos)
  have L0 : Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • (tetraFlux t x n e h +
      ∫ y in cauchyTetra x n e h, b y)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hbal x n e hon hn hpos h hh, smul_zero]
  simp only [tetraFlux, smul_add] at L0
  have hlim := tendsto_nhds_unique L L0
  rw [gramArea_tetraEdge hon hpos (by decide), gramArea_tetraEdge hon hpos (by decide),
    gramArea_tetraEdge hon hpos (by decide), gramArea_tetraEdge_slant hon hn hpos,
    add_zero] at hlim
  have h0 := (hpos 0).ne'
  have h1 := (hpos 1).ne'
  have h2 := (hpos 2).ne'
  rw [Fin.sum_univ_three]
  calc t x n + (⟪n, e 0⟫_ℝ • t x (-e 0) + ⟪n, e 1⟫_ℝ • t x (-e 1) + ⟪n, e 2⟫_ℝ • t x (-e 2))
      = (2 * ⟪n, e 0⟫_ℝ * ⟪n, e 1⟫_ℝ * ⟪n, e 2⟫_ℝ) •
          ((2⁻¹ * (⟪n, e 1⟫_ℝ * ⟪n, e 2⟫_ℝ)⁻¹) • t x (-e 0) +
            (2⁻¹ * (⟪n, e 0⟫_ℝ * ⟪n, e 2⟫_ℝ)⁻¹) • t x (-e 1) +
            (2⁻¹ * (⟪n, e 0⟫_ℝ * ⟪n, e 1⟫_ℝ)⁻¹) • t x (-e 2) +
            (2⁻¹ * (⟪n, e 0⟫_ℝ * ⟪n, e 1⟫_ℝ * ⟪n, e 2⟫_ℝ)⁻¹) • t x n) := by
        simp only [smul_add, smul_smul]
        match_scalars <;> field_simp
    _ = 0 := by rw [hlim, smul_zero]

/-- The tetrahedron identity on the **closed** octant, using continuity of `t(x, ·)` on the unit
sphere. -/
theorem tetra_identity_of_nonneg [Fact (finrank ℝ E = 3)] (ht : ∀ m, Continuous fun y => t y m)
    (htn : ∀ x, ContinuousOn (t x) (sphere 0 1)) (hb : Continuous b) (hbal : TetraBalance t b)
    (x n : E) {e : Fin 3 → E} (hon : Orthonormal ℝ e) (hn : ‖n‖ = 1)
    (hnn : ∀ i, 0 ≤ ⟪n, e i⟫_ℝ) :
    t x n + ∑ i, ⟪n, e i⟫_ℝ • t x (-e i) = 0 := by
  have o := orthonormal_iff_ite.mp hon
  set s := ∑ i, e i
  have hs : ∀ i, ⟪s, e i⟫_ℝ = 1 := fun i => by
    simp only [s, sum_inner, o, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  let v : ℝ → E := fun ε => n + ε • s
  have hv : ∀ ε i, ⟪v ε, e i⟫_ℝ = ⟪n, e i⟫_ℝ + ε := fun ε i => by
    simp only [v, inner_add_left, real_inner_smul_left, hs, mul_one]
  let m : ℝ → E := fun ε => ‖v ε‖⁻¹ • v ε
  have hv0 : ∀ ε, 0 < ε → v ε ≠ 0 := fun ε hε h => by
    have := hv ε 0
    rw [h, inner_zero_left] at this
    linarith [hnn 0]
  -- `m ε` lies in the open octant, so the identity holds there
  have hG : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t x (m ε) + ∑ i, ⟪m ε, e i⟫_ℝ • t x (-e i) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine tetra_identity ht hb hbal x (m ε) hon (norm_smul_inv_norm (hv0 ε hε)) fun i => ?_
    rw [real_inner_smul_left, hv]
    have hε' : 0 < ε := hε
    exact mul_pos (inv_pos.2 (norm_pos_iff.2 (hv0 ε hε))) (by linarith [hnn i])
  -- `m ε → n` on the sphere
  have hvt : Tendsto v (𝓝 0) (𝓝 n) := by
    have : Tendsto v (𝓝 0) (𝓝 (n + (0 : ℝ) • s)) :=
      tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
    simpa using this
  have hmt : Tendsto m (𝓝[>] 0) (𝓝[sphere 0 1] n) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((hvt.norm.inv₀ (by rw [hn]; exact one_ne_zero)).smul hvt)
      rw [hn, inv_one, one_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm (hv0 ε hε)
  have hcont : ContinuousWithinAt (fun m => t x m + ∑ i, ⟪m, e i⟫_ℝ • t x (-e i))
      (sphere 0 1) n :=
    (htn x n (by rw [mem_sphere_zero_iff_norm, hn])).add
      (continuous_finsetSum _ fun i _ =>
        (continuous_id.inner continuous_const).smul continuous_const).continuousWithinAt
  exact tendsto_nhds_unique (hcont.tendsto.comp hmt) (tendsto_const_nhds.congr' (hG.mono
    fun ε hε => hε.symm))

/-- **Cauchy's reciprocal theorem**: `t(x, -n) = -t(x, n)`. [Gurtin1981], §14. -/
theorem traction_neg [Fact (finrank ℝ E = 3)] (ht : ∀ m, Continuous fun y => t y m)
    (htn : ∀ x, ContinuousOn (t x) (sphere 0 1)) (hb : Continuous b) (hbal : TetraBalance t b)
    (x v : E) (hv : ‖v‖ = 1) : t x (-v) = -t x v := by
  have hv1 : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict fun _ : Fin 3 => v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j]
    simp [hv]
  obtain ⟨B, hB⟩ := hv1.exists_orthonormalBasis_extension_of_card_eq
    (by rw [Fintype.card_fin]; exact Fact.out)
  have hB0 : B 0 = v := hB 0 rfl
  have o := orthonormal_iff_ite.mp B.orthonormal
  have hi : ∀ i, ⟪v, B i⟫_ℝ = if 0 = i then 1 else 0 := fun i => by rw [← hB0, o]
  have := tetra_identity_of_nonneg ht htn hb hbal x v B.orthonormal hv fun i => by
    rw [hi]; split_ifs <;> norm_num
  simp only [hi, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_smul,
    zero_smul, add_zero, hB0] at this
  exact eq_neg_of_add_eq_zero_right this

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_dyad_left (c : E) : Continuous fun a : E => a ⊗ c := by
  let L : E →ₗ[ℝ] Lin E :=
    { toFun := fun a => a ⊗ c
      map_add' := fun a a' => by ext v; simp [smul_add]
      map_smul' := fun r a => by ext v; simp [smul_comm r] }
  exact L.continuous_of_finiteDimensional

/-- **Cauchy's theorem**: if the tractions balance the body force on every Cauchy tetrahedron,
then `t(x, n) = σ(x) n` for a continuous tensor field `σ`, the **Cauchy stress**.
[Gurtin1981], §14; [MarsdenHughes1983], §2.2, Thm. 2.2. -/
theorem cauchy_tetrahedron [Fact (finrank ℝ E = 3)] (ht : ∀ m, Continuous fun y => t y m)
    (htn : ∀ x, ContinuousOn (t x) (sphere 0 1)) (hb : Continuous b) (hbal : TetraBalance t b) :
    ∃ σ : E → Lin E, Continuous σ ∧ ∀ x n, ‖n‖ = 1 → t x n = σ x n := by
  let B := (stdOrthonormalBasis ℝ E).reindex (finCongr (Fact.out : finrank ℝ E = 3))
  refine ⟨fun x => ∑ i, t x (B i) ⊗ B i, continuous_finsetSum _ fun i _ =>
    (continuous_dyad_left (B i)).comp (ht (B i)), fun x n hn => ?_⟩
  have o := orthonormal_iff_ite.mp B.orthonormal
  -- flip the frame into the closed octant of `n`
  let sg : Fin 3 → ℝ := fun i => if 0 ≤ ⟪n, B i⟫_ℝ then 1 else -1
  let e' : Fin 3 → E := fun i => sg i • B i
  have hon' : Orthonormal ℝ e' := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [e', real_inner_smul_left, real_inner_smul_right, o]
    split_ifs with h
    · subst h; simp only [sg]; split_ifs <;> norm_num
    · simp
  have hnn : ∀ i, 0 ≤ ⟪n, e' i⟫_ℝ := fun i => by
    simp only [e', sg, real_inner_smul_right]
    split_ifs with h <;> linarith
  have key := tetra_identity_of_nonneg ht htn hb hbal x n hon' hn hnn
  have hterm : ∀ i, ⟪n, e' i⟫_ℝ • t x (-e' i) = -(⟪n, B i⟫_ℝ • t x (B i)) := fun i => by
    simp only [e', sg, real_inner_smul_right]
    split_ifs
    · rw [one_smul, one_mul, traction_neg ht htn hb hbal x _ (B.orthonormal.1 i), smul_neg]
    · simp [neg_smul]
  simp only [hterm, Finset.sum_neg_distrib] at key
  rw [sum_apply]
  simp only [dyad_apply, real_inner_comm n]
  exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact key)

/-- The zero traction field balances zero body force. -/
example : TetraBalance (fun _ _ => (0 : E)) (fun _ => 0) := by
  intro x n e _ _ _ h _
  simp [tetraFlux, triangleIntegral]

end ContinuumMechanics
