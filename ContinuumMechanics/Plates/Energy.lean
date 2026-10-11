import ContinuumMechanics.Elastostatics.Korn
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Kirchhoff–Love plate energy: strong ⇔ stationary, minimum energy

For a deflection `w : ℝⁿ → ℝ` (`n = 2` for plates) with Hessian `∇²w = (∂ᵢ∂ⱼw)`, the
**Kirchhoff–Love bending energy** of an isotropic plate with rigidity `D` and Poisson ratio `ν`
has density

`D/2 (ν (Δw)² + (1 - ν) |∇²w|²)`,

which for `n = 2` is the classical `D/2 ((Δw)² - 2(1 - ν)(w₁₁w₂₂ - w₁₂²))` (`density_two`); its
bilinear form is `a(w, v) = D ∫ ν Δw Δv + (1 - ν) ∇²w : ∇²v` (`bending`).

* **Null Lagrangian** (`integral_hessDot`): `∫ ∇²w : ∇²v = ∫ Δw Δv` whenever `v` has compact
  support, so the `ν`-dependent part of the energy does not contribute to the equilibrium
  equations, and `a(w, v) = D ∫ Δ²w v` (`bending_eq`).
* **Strong ⇔ stationary** (`isStationary_iff`): on an open set `U`, `a(w, v) = ∫ q v` for every
  smooth test function `v` compactly supported in `U` iff `D Δ²w = q` in `U` (the
  Sophie Germain–Lagrange equation of `Plates/KirchhoffLove`).
* **Minimum potential energy** (`energy_le`): with `Π(w) = a(w, w)/2 - ∫ q w`, a compactly
  supported (clamped) solution of `D Δ²w = q` minimises `Π` among compactly supported
  deflections, for every `ν`, since `a(v, v) = D ∫ (Δv)² ≥ 0`.

Partial derivatives are `Korn.pd` (Fréchet derivatives along coordinate vectors).

## References

* [TimoshenkoWoinowsky1959] S. P. Timoshenko, S. Woinowsky-Krieger, *Theory of Plates and
  Shells*, §§10–11.
* [Ciarlet1978] P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, §1.2.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Plates.Energy

open Korn

variable {n : ℕ}

variable {f g w v : (Fin n → ℝ) → ℝ}

theorem pd_add (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    pd (f + g) j = pd f j + pd g j := by
  funext x
  simp [pd, fderiv_add (hf x) (hg x)]

theorem contDiff_pd_of_le {k m : WithTop ℕ∞} (hf : ContDiff ℝ m f) (hk : k + 1 ≤ m) (j : Fin n) :
    ContDiff ℝ k (pd f j) :=
  (hf.fderiv_right hk).clm_apply contDiff_const

/-- **Integration by parts** with the compact support on the differentiated factor:
`∫ f ∂ⱼg = -∫ ∂ⱼf g`. -/
theorem integral_mul_pd' (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (j : Fin n) : ∫ x, f x * pd g j x = -∫ x, pd f j x * g x := by
  have cf := hf.continuous; have cg := hg.continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_pd hf j).mul cg).integrable_of_hasCompactSupport hgc.mul_left)
    ((cf.mul (continuous_pd hg j)).integrable_of_hasCompactSupport
      (hasCompactSupport_pd hgc j).mul_left)
    ((cf.mul cg).integrable_of_hasCompactSupport hgc.mul_left)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

/-- The Laplacian `Δf = Σᵢ ∂ᵢ∂ᵢf`. -/
def lap (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, pd (pd f i) i x

/-- The Hessian contraction `∇²w : ∇²v = Σᵢⱼ ∂ᵢ∂ⱼw ∂ᵢ∂ⱼv`. -/
def hessDot (w v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, pd (pd w i) j x * pd (pd v i) j x

theorem continuous_pd_pd (hf : ContDiff ℝ 2 f) (i j : Fin n) : Continuous (pd (pd f i) j) :=
  continuous_pd (contDiff_pd hf i) j

theorem continuous_lap (hf : ContDiff ℝ 2 f) : Continuous (lap f) :=
  continuous_finsetSum _ fun i _ => continuous_pd_pd hf i i

theorem hasCompactSupport_pd_pd (hf : HasCompactSupport f) (i j : Fin n) :
    HasCompactSupport (pd (pd f i) j) :=
  hasCompactSupport_pd (hasCompactSupport_pd hf i) j

theorem hasCompactSupport_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℝ) → ℝ)
    (h : ∀ i ∈ s, HasCompactSupport (F i)) : HasCompactSupport (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasCompactSupport_lap (hf : HasCompactSupport f) : HasCompactSupport (lap f) :=
  hasCompactSupport_sum _ _ fun i _ => hasCompactSupport_pd_pd hf i i

/-- The bilaplacian `Δ²w = Σᵢⱼ ∂ⱼ∂ⱼ∂ᵢ∂ᵢw`. -/
def bilap (w : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, pd (pd (pd (pd w i) i) j) j x

/-- `∫ ∂ᵢ∂ᵢw ∂ⱼ∂ⱼv = ∫ ∂ᵢ∂ⱼw ∂ᵢ∂ⱼv` for `w ∈ C³` and `v ∈ C²` with compact support. -/
theorem integral_pd_pd_swap (hw : ContDiff ℝ 3 w) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (i j : Fin n) :
    ∫ x, pd (pd w i) i x * pd (pd v j) j x = ∫ x, pd (pd w i) j x * pd (pd v i) j x := by
  have hwi : ContDiff ℝ 2 (pd w i) := contDiff_pd_of_le hw (by norm_num) i
  have hA : ContDiff ℝ 1 (pd (pd w i) i) := contDiff_pd hwi i
  have hB : ContDiff ℝ 1 (pd (pd w i) j) := contDiff_pd hwi j
  have hvj : ContDiff ℝ 1 (pd v j) := contDiff_pd hv j
  have hvjc : HasCompactSupport (pd v j) := hasCompactSupport_pd hvc j
  rw [integral_mul_pd' hA hvj hvjc j, pd_pd_comm hwi i j, pd_pd_comm hv i j,
    integral_mul_pd' hB hvj hvjc i]

/-- `∫ A ∂ⱼ∂ⱼv = ∫ ∂ⱼ∂ⱼA v` for `A ∈ C²` and `v ∈ C²` with compact support. -/
theorem integral_mul_pd_pd (hA : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (j : Fin n) : ∫ x, f x * pd (pd v j) j x = ∫ x, pd (pd f j) j x * v x := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  rw [integral_mul_pd' (hA.of_le (by norm_num)) (contDiff_pd hv j) (hasCompactSupport_pd hvc j),
    integral_mul_pd' (contDiff_pd hA j) hv1 hvc j, neg_neg]

theorem integrable_mul (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (k l : Fin n)
    {F : (Fin n → ℝ) → ℝ} (hF : Continuous F) :
    Integrable fun x => F x * pd (pd v k) l x :=
  (hF.mul (continuous_pd_pd hv k l)).integrable_of_hasCompactSupport
    (hasCompactSupport_pd_pd hvc k l).mul_left

/-- The **bending bilinear form** `a(w, v) = D ∫ ν Δw Δv + (1 - ν) ∇²w : ∇²v`. -/
def bending (D ν : ℝ) (w v : (Fin n → ℝ) → ℝ) : ℝ :=
  D * ∫ x, (ν * (lap w x * lap v x) + (1 - ν) * hessDot w v x)

/-- The **potential energy** `Π(w) = a(w, w)/2 - ∫ q w`. -/
def energy (D ν : ℝ) (q w : (Fin n → ℝ) → ℝ) : ℝ := bending D ν w w / 2 - ∫ x, q x * w x

/-- `w` is **stationary** for the plate energy with load `q` in the open set `U`:
`a(w, v) = ∫ q v` for every smooth `v` compactly supported in `U`. -/
def IsStationary (D ν : ℝ) (q w : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) : Prop :=
  ∀ v : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v → tsupport v ⊆ U →
    bending D ν w v = ∫ x, q x * v x

/-- For `n = 2` the energy density is the classical
`(Δw)² - 2(1 - ν)(w₁₁w₂₂ - w₁₂²)`. -/
theorem density_two {w : (Fin 2 → ℝ) → ℝ} (hw : ContDiff ℝ 2 w) (ν : ℝ) (x : Fin 2 → ℝ) :
    ν * (lap w x * lap w x) + (1 - ν) * hessDot w w x =
      lap w x ^ 2 - 2 * (1 - ν) * (pd (pd w 0) 0 x * pd (pd w 1) 1 x - pd (pd w 0) 1 x ^ 2) := by
  have h := congrFun (pd_pd_comm hw 0 1) x
  simp only [lap, hessDot, Fin.sum_univ_two] at h ⊢
  rw [h]
  ring

theorem continuous_bilap (hw : ContDiff ℝ 4 w) : Continuous (bilap w) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_pd_pd (contDiff_pd_of_le (contDiff_pd_of_le hw (k := 3) (by norm_num) i)
      (by norm_num) i) j j

theorem lap_add (hw : ContDiff ℝ 2 w) (hv : ContDiff ℝ 2 v) : lap (w + v) = lap w + lap v := by
  funext x
  have d1 : ∀ {f : (Fin n → ℝ) → ℝ}, ContDiff ℝ 2 f → Differentiable ℝ f :=
    fun hf => hf.differentiable (by norm_num)
  have d2 : ∀ {f : (Fin n → ℝ) → ℝ}, ContDiff ℝ 2 f → ∀ i, Differentiable ℝ (pd f i) :=
    fun hf i => (contDiff_pd hf i).differentiable one_ne_zero
  simp only [lap, pd_add (d1 hw) (d1 hv), pd_add (d2 hw _) (d2 hv _), Pi.add_apply,
    Finset.sum_add_distrib]

section Bilinear

variable {F : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 4 w) (hv : ContDiff ℝ 2 v)
  (hvc : HasCompactSupport v)
include hw hv hvc

/-- **Null Lagrangian**: `∫ ∇²w : ∇²v = ∫ Δw Δv` when `v` has compact support. -/
theorem integral_hessDot : ∫ x, hessDot w v x = ∫ x, lap w x * lap v x := by
  have hw3 : ContDiff ℝ 3 w := hw.of_le (by norm_num)
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have I : ∀ i j k l : Fin n, Integrable fun x => pd (pd w i) j x * pd (pd v k) l x :=
    fun i j k l => integrable_mul hv hvc k l (continuous_pd_pd hw2 i j)
  have e : ∀ x, lap w x * lap v x = ∑ i, ∑ j, pd (pd w i) i x * pd (pd v j) j x := fun x => by
    rw [lap, lap, Finset.sum_mul_sum]
  simp_rw [e, hessDot]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => I i j i j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => I i i j j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => I i j i j, integral_finsetSum _ fun j _ => I i i j j]
  exact Finset.sum_congr rfl fun j _ => (integral_pd_pd_swap hw3 hv hvc i j).symm

/-- `∫ Δw Δv = ∫ Δ²w v` when `v` has compact support. -/
theorem integral_lap_mul_lap : ∫ x, lap w x * lap v x = ∫ x, bilap w x * v x := by
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hA : ∀ i, ContDiff ℝ 2 (pd (pd w i) i) := fun i =>
    contDiff_pd_of_le (contDiff_pd_of_le hw (k := 3) (by norm_num) i) (by norm_num) i
  have cv := hv.continuous
  have I : ∀ i j, Integrable fun x => pd (pd w i) i x * pd (pd v j) j x :=
    fun i j => integrable_mul hv hvc j j (continuous_pd_pd hw2 i i)
  have J : ∀ i j, Integrable fun x => pd (pd (pd (pd w i) i) j) j x * v x := fun i j =>
    ((continuous_pd_pd (hA i) j j).mul cv).integrable_of_hasCompactSupport hvc.mul_left
  have e1 : ∀ x, lap w x * lap v x = ∑ i, ∑ j, pd (pd w i) i x * pd (pd v j) j x := fun x => by
    rw [lap, lap, Finset.sum_mul_sum]
  have e2 : ∀ x, bilap w x * v x = ∑ i, ∑ j, pd (pd (pd (pd w i) i) j) j x * v x := fun x => by
    simp only [bilap, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => I i j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => J i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => I i j, integral_finsetSum _ fun j _ => J i j]
  exact Finset.sum_congr rfl fun j _ => integral_mul_pd_pd (hA i) hv hvc j

omit hw in
theorem integrable_lap_mul (hF : Continuous F) : Integrable fun x => F x * lap v x :=
  (hF.mul (continuous_lap hv)).integrable_of_hasCompactSupport (hasCompactSupport_lap hvc).mul_left

/-- `a(w, v) = D ∫ Δw Δv`: the `ν`-term is a null Lagrangian. -/
theorem bending_eq_lap (D ν : ℝ) : bending D ν w v = D * ∫ x, lap w x * lap v x := by
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have iA : Integrable fun x => lap w x * lap v x := integrable_lap_mul hv hvc (continuous_lap hw2)
  have iH : Integrable (hessDot w v) := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_mul hv hvc i j (continuous_pd_pd hw2 i j)
  rw [bending, integral_add (iA.const_mul ν) (iH.const_mul (1 - ν)), integral_const_mul,
    integral_const_mul, integral_hessDot hw hv hvc]
  ring

/-- `a(w, v) = D ∫ Δ²w v`. -/
theorem bending_eq (D ν : ℝ) : bending D ν w v = D * ∫ x, bilap w x * v x := by
  rw [bending_eq_lap hw hv hvc, integral_lap_mul_lap hw hv hvc]

end Bilinear

variable {D ν : ℝ} {q : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}

/-- **Fundamental lemma of the calculus of variations**: a continuous `F` with `∫ g F = 0` for
every smooth `g` compactly supported in the open set `U` vanishes on `U`. -/
theorem eq_zero_on_of_integral {F : (Fin n → ℝ) → ℝ} (hF : Continuous F) (hU : IsOpen U)
    (h : ∀ g : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x * F x = 0) :
    ∀ x ∈ U, F x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := F) (μ := volume)
    (hF.locallyIntegrable.locallyIntegrableOn U) fun g hg hgc hgU => by
      simpa only [smul_eq_mul] using h g hg hgc hgU
  have hS : IsOpen (U ∩ {x | F x ≠ 0}) := hU.inter (isOpen_ne_fun hF continuous_const)
  have h0 : volume (U ∩ {x | F x ≠ 0}) = 0 := by
    rw [ae_iff] at hae
    convert hae using 2
    ext x
    simp
  have he := (hS.measure_eq_zero_iff volume).mp h0
  intro x hx
  by_contra hne
  have : x ∈ U ∩ {x | F x ≠ 0} := ⟨hx, hne⟩
  rw [he] at this
  exact this

/-- `∫ F g = ∫ G g` when `F = G` on `U ⊇ tsupport g`. -/
theorem integral_mul_congr_on {F G g : (Fin n → ℝ) → ℝ} (hg : tsupport g ⊆ U)
    (h : ∀ x ∈ U, F x = G x) : ∫ x, F x * g x = ∫ x, G x * g x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ U
  · simp only [h x hx]
  · have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hg h')
    simp [this]

/-- **Strong ⇔ stationary**: `w` is stationary in the open set `U` iff it solves the plate
equation `D Δ²w = q` there. -/
theorem isStationary_iff (hw : ContDiff ℝ 4 w) (hq : Continuous q) (hU : IsOpen U) :
    IsStationary D ν q w U ↔ ∀ x ∈ U, D * bilap w x = q x := by
  constructor
  · intro h x hx
    refine sub_eq_zero.mp (eq_zero_on_of_integral (F := fun x => D * bilap w x - q x)
      ((continuous_const.mul (continuous_bilap hw)).sub hq) hU (fun g hg hgc hgU => ?_) x hx)
    have hg2 : ContDiff ℝ 2 g := hg.of_le (by simp)
    have i1 : Integrable fun x => g x * (D * bilap w x) :=
      (hg2.continuous.mul (continuous_const.mul (continuous_bilap hw)))
        |>.integrable_of_hasCompactSupport hgc.mul_right
    have i2 : Integrable fun x => g x * q x :=
      (hg2.continuous.mul hq).integrable_of_hasCompactSupport hgc.mul_right
    simp only [mul_sub]
    rw [integral_sub i1 i2, ← sub_eq_zero.mpr (h g hg hgc hgU), bending_eq hw hg2 hgc,
      ← integral_const_mul]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · intro h v hv hvc hvU
    have hv2 : ContDiff ℝ 2 v := hv.of_le (by simp)
    rw [bending_eq hw hv2 hvc, ← integral_const_mul]
    simp_rw [← mul_assoc]
    exact integral_mul_congr_on hvU h

/-- **Minimum potential energy**: a compactly supported (clamped) solution of `D Δ²w = q` with
`D ≥ 0` minimises `Π` among compactly supported `C⁴` deflections, for every Poisson ratio. -/
theorem energy_le (hD : 0 ≤ D) (hw : ContDiff ℝ 4 w) (hwc : HasCompactSupport w)
    (hq : ∀ x, D * bilap w x = q x) (hv : ContDiff ℝ 4 v) (hvc : HasCompactSupport v) :
    energy D ν q w ≤ energy D ν q (w + v) := by
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have cw := continuous_lap hw2; have cv := continuous_lap hv2
  have iww : Integrable fun x => lap w x * lap w x := integrable_lap_mul hw2 hwc cw
  have iwv : Integrable fun x => lap w x * lap v x := integrable_lap_mul hv2 hvc cw
  have ivv : Integrable fun x => lap v x * lap v x := integrable_lap_mul hv2 hvc cv
  have iqw : Integrable fun x => q x * w x := by
    simp_rw [← hq]
    exact ((continuous_const.mul (continuous_bilap hw)).mul hw2.continuous)
      |>.integrable_of_hasCompactSupport
      hwc.mul_left
  have iqv : Integrable fun x => q x * v x := by
    simp_rw [← hq]
    exact ((continuous_const.mul (continuous_bilap hw)).mul hv2.continuous)
      |>.integrable_of_hasCompactSupport
      hvc.mul_left
  have eqv : ∫ x, q x * v x = D * ∫ x, lap w x * lap v x := by
    rw [integral_lap_mul_lap hw hv2 hvc, ← integral_const_mul]
    simp_rw [← hq, mul_assoc]
  have e : ∫ x, lap (w + v) x * lap (w + v) x =
      (∫ x, lap w x * lap w x) + 2 * (∫ x, lap w x * lap v x) + ∫ x, lap v x * lap v x := by
    have hx : ∀ x, lap (w + v) x * lap (w + v) x =
        (lap w x * lap w x + 2 * (lap w x * lap v x)) + lap v x * lap v x := fun x => by
      rw [lap_add hw2 hv2, Pi.add_apply]; ring
    have h1 := integral_add (iww.add (iwv.const_mul 2)) ivv
    have h2 := integral_add iww (iwv.const_mul 2)
    simp only [Pi.add_apply] at h1 h2
    rw [integral_congr_ae (Filter.Eventually.of_forall hx), h1, h2, integral_const_mul]
  have hwv : HasCompactSupport (w + v) := hwc.add hvc
  rw [energy, energy, bending_eq_lap hw hw2 hwc,
    bending_eq_lap (w := w + v) (v := w + v) (hw.add hv) (hw2.add hv2) hwv, e]
  have hqs : ∫ x, q x * (w + v) x = (∫ x, q x * w x) + ∫ x, q x * v x := by
    rw [← integral_add iqw iqv]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  rw [hqs, eqv]
  have : 0 ≤ D * ∫ x, lap v x * lap v x :=
    mul_nonneg hD (integral_nonneg fun x => mul_self_nonneg _)
  nlinarith

end ContinuumMechanics.Plates.Energy
