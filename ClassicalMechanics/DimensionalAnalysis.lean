import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Dimensional analysis and the Buckingham π theorem

Fix a finite set `ι` of **base dimensions** (e.g. mass `M`, length `L`, time `T`) and a finite
set `κ` of physical quantities with positive values `q : κ → ℝ`. The **dimension matrix**
`A : Matrix ι κ ℝ` has as column `j` the exponent vector of quantity `j`: `[q j] = ∏ᵢ Dᵢ ^ A i j`.
A **monomial** `∏ⱼ q j ^ k j` (`monomial q k`) has dimension vector `A *ᵥ k`, and it is
**dimensionless** when `A *ᵥ k = 0`.

A **change of units** rescales the base unit `i` by a factor `s i > 0`; the numerical value of
quantity `j` is then multiplied by `∏ᵢ s i ^ A i j` (`changeUnits`).

## Main results

* `monomial_add`, `dimension_add`: multiplying monomials adds exponents and dimensions.
* `monomial_changeUnits`: under a change of units a monomial with exponent `k` is multiplied by
  `∏ᵢ s i ^ (A *ᵥ k) i`.
* `monomial_invariant_iff`: a monomial is invariant under all changes of units iff it is
  dimensionless.
* `finrank_dimensionless`: **Buckingham π (counting)**. The dimensionless exponent vectors form
  a subspace of dimension `card κ - rank A`, so there are exactly `n - r` independent π-groups.
* `exists_vecMul_eq_iff`: a vector is orthogonal to `ker A` iff it lies in the row space of `A`.
* `buckingham_pi`: **Buckingham π (functional form)**. Two positive quantity vectors take the
  same value on every dimensionless monomial iff a change of units maps one onto the other.
* `buckingham_pi_basis`, `exists_function_of_pi`: a unit-invariant function of the quantities
  is a function of the `n - r` π-groups `π_m = monomial q (b m)` of a basis `b` of `ker A`.
* Worked examples: the pendulum (`pendulum_ker_iff`, `pendulum_finrank_ker`,
  `pendulum_period`: `T = C √(L / g)`, independent of the mass) and the drag on a sphere
  (`drag_ker_iff`, `drag_finrank_ker`, `drag_law`: `F = ρ V² D² Φ(Re)`).

## References

* [Buckingham1914] E. Buckingham, *On physically similar systems; illustrations of the use of
  dimensional equations*, Phys. Rev. **4** (1914) 345–376.
* [Bridgman1922] P. W. Bridgman, *Dimensional Analysis*, Yale University Press, 1922.
* [Barenblatt1996] G. I. Barenblatt, *Scaling, Self-similarity, and Intermediate Asymptotics*,
  Cambridge University Press, 1996, ch. 1.
-/

open Matrix Module

noncomputable section

namespace ClassicalMechanics

namespace DimensionalAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Monomials and dimensions -/

/-- The monomial `∏ⱼ q j ^ k j` in the quantities `q` with real exponents `k`. -/
def monomial (q k : κ → ℝ) : ℝ := ∏ j, q j ^ k j

/-- Componentwise logarithm of a vector of positive quantities. -/
def logVec (q : κ → ℝ) : κ → ℝ := fun j => Real.log (q j)

/-- The dimension vector `A *ᵥ k` of the monomial with exponent vector `k`. -/
def dimension (A : Matrix ι κ ℝ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) := A.mulVecLin

/-- A monomial with exponent vector `k` is dimensionless iff `A *ᵥ k = 0`. -/
def IsDimensionless (A : Matrix ι κ ℝ) (k : κ → ℝ) : Prop := A *ᵥ k = 0

/-- The subspace of exponent vectors of dimensionless monomials, i.e. the kernel of `A`. -/
def dimensionless (A : Matrix ι κ ℝ) : Submodule ℝ (κ → ℝ) := LinearMap.ker A.mulVecLin

omit [Fintype ι] in
/-- Membership in `dimensionless A` is `IsDimensionless A`. -/
theorem mem_dimensionless {A : Matrix ι κ ℝ} {k : κ → ℝ} :
    k ∈ dimensionless A ↔ IsDimensionless A k := by
  simp [dimensionless, IsDimensionless]

/-- For positive quantities, `monomial q k = exp (log q ⬝ᵥ k)`. -/
theorem monomial_eq_exp {q : κ → ℝ} (hq : ∀ j, 0 < q j) (k : κ → ℝ) :
    monomial q k = Real.exp (logVec q ⬝ᵥ k) := by
  simp only [monomial, dotProduct, logVec, Real.exp_sum]
  exact Finset.prod_congr rfl fun j _ => Real.rpow_def_of_pos (hq j) _

/-- A monomial in positive quantities is positive. -/
theorem monomial_pos {q : κ → ℝ} (hq : ∀ j, 0 < q j) (k : κ → ℝ) : 0 < monomial q k := by
  rw [monomial_eq_exp hq]; exact Real.exp_pos _

/-- Multiplying monomials adds the exponents. -/
theorem monomial_add {q : κ → ℝ} (hq : ∀ j, 0 < q j) (k k' : κ → ℝ) :
    monomial q (k + k') = monomial q k * monomial q k' := by
  simp only [monomial_eq_exp hq, dotProduct_add, Real.exp_add]

omit [Fintype ι] in
/-- The dimension of a product of monomials is the sum of their dimensions. -/
theorem dimension_add (A : Matrix ι κ ℝ) (k k' : κ → ℝ) :
    dimension A (k + k') = dimension A k + dimension A k' := map_add _ _ _

omit [Fintype ι] in
/-- The product of dimensionless monomials is dimensionless. -/
theorem IsDimensionless.add {A : Matrix ι κ ℝ} {k k' : κ → ℝ} (h : IsDimensionless A k)
    (h' : IsDimensionless A k') : IsDimensionless A (k + k') := by
  simp_all [IsDimensionless, mulVec_add]

/-! ### Changes of units -/

/-- The factor `∏ᵢ s i ^ A i j` by which the value of quantity `j` is multiplied when the base
unit `i` is rescaled by `s i`. -/
def unitFactor (A : Matrix ι κ ℝ) (s : ι → ℝ) (j : κ) : ℝ := ∏ i, s i ^ A i j

/-- The values of the quantities `q` after rescaling the base units by `s`. -/
def changeUnits (A : Matrix ι κ ℝ) (s : ι → ℝ) (q : κ → ℝ) : κ → ℝ :=
  fun j => unitFactor A s j * q j

omit [Fintype κ] in
/-- For positive scale factors, `unitFactor A s j = exp ((log s ᵥ* A) j)`. -/
theorem unitFactor_eq_exp (A : Matrix ι κ ℝ) {s : ι → ℝ} (hs : ∀ i, 0 < s i) (j : κ) :
    unitFactor A s j = Real.exp ((logVec s ᵥ* A) j) := by
  simp only [unitFactor, vecMul, dotProduct, logVec, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (hs i) _

omit [Fintype κ] in
/-- A change of units keeps quantities positive. -/
theorem changeUnits_pos (A : Matrix ι κ ℝ) {s : ι → ℝ} (hs : ∀ i, 0 < s i) {q : κ → ℝ}
    (hq : ∀ j, 0 < q j) (j : κ) : 0 < changeUnits A s q j := by
  rw [changeUnits, unitFactor_eq_exp A hs]; exact mul_pos (Real.exp_pos _) (hq j)

omit [Fintype κ] in
/-- The logarithm of the rescaled quantities: `log q' = log s ᵥ* A + log q`. -/
theorem logVec_changeUnits (A : Matrix ι κ ℝ) {s : ι → ℝ} (hs : ∀ i, 0 < s i) {q : κ → ℝ}
    (hq : ∀ j, 0 < q j) : logVec (changeUnits A s q) = logVec s ᵥ* A + logVec q := by
  ext j
  simp only [logVec, changeUnits, unitFactor_eq_exp A hs, Pi.add_apply]
  rw [Real.log_mul (Real.exp_pos _).ne' (hq j).ne', Real.log_exp]

/-- **Scaling of a monomial**: under a change of units by `s`, the monomial with exponent `k`
is multiplied by `∏ᵢ s i ^ (A *ᵥ k) i`, the unit factor of its dimension vector. -/
theorem monomial_changeUnits (A : Matrix ι κ ℝ) {s : ι → ℝ} (hs : ∀ i, 0 < s i) {q : κ → ℝ}
    (hq : ∀ j, 0 < q j) (k : κ → ℝ) :
    monomial (changeUnits A s q) k = (∏ i, s i ^ (A *ᵥ k) i) * monomial q k := by
  have h : ∏ i, s i ^ (A *ᵥ k) i = Real.exp (logVec s ⬝ᵥ (A *ᵥ k)) := by
    simp only [dotProduct, logVec, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (hs i) _
  rw [monomial_eq_exp (changeUnits_pos A hs hq), monomial_eq_exp hq, h,
    logVec_changeUnits A hs hq, add_dotProduct, dotProduct_mulVec, Real.exp_add]

/-- A dimensionless monomial is invariant under every change of units. -/
theorem monomial_changeUnits_of_isDimensionless {A : Matrix ι κ ℝ} {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) {q : κ → ℝ} (hq : ∀ j, 0 < q j) {k : κ → ℝ}
    (hk : IsDimensionless A k) : monomial (changeUnits A s q) k = monomial q k := by
  rw [monomial_changeUnits A hs hq, hk]; simp

/-- **Invariance criterion**: a monomial (in positive quantities) is invariant under all changes
of units iff it is dimensionless. For the converse, rescale the base units by
`s i = exp ((A *ᵥ k) i)`, which multiplies the monomial by `exp ‖A *ᵥ k‖²`. -/
theorem monomial_invariant_iff (A : Matrix ι κ ℝ) {q : κ → ℝ} (hq : ∀ j, 0 < q j)
    (k : κ → ℝ) :
    (∀ s : ι → ℝ, (∀ i, 0 < s i) → monomial (changeUnits A s q) k = monomial q k) ↔
      IsDimensionless A k := by
  refine ⟨fun h => ?_, fun hk s hs => monomial_changeUnits_of_isDimensionless hs hq hk⟩
  set v := A *ᵥ k
  have hs : ∀ i, 0 < Real.exp (v i) := fun i => Real.exp_pos _
  have h1 := h _ hs
  rw [monomial_changeUnits A hs hq] at h1
  have h2 : ∏ i, Real.exp (v i) ^ v i = Real.exp (v ⬝ᵥ v) := by
    simp only [dotProduct, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (hs i), Real.log_exp]
  rw [h2] at h1
  have h3 : Real.exp (v ⬝ᵥ v) = 1 := by
    have := monomial_pos hq k
    field_simp at h1
    linarith [h1]
  rw [Real.exp_eq_one_iff, dotProduct_self_eq_zero] at h3
  exact h3

/-! ### Buckingham π: counting -/

omit [Fintype ι] in
/-- **Buckingham π theorem (counting)**: the space of dimensionless exponent vectors has
dimension `n - r`, where `n` is the number of quantities and `r = rank A`. -/
theorem finrank_dimensionless (A : Matrix ι κ ℝ) :
    finrank ℝ (dimensionless A) = Fintype.card κ - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Matrix.rank, dimensionless]
  omega

omit [Fintype ι] in
/-- Any basis of the dimensionless exponent vectors (a complete set of independent π-groups)
has exactly `n - rank A` elements. -/
theorem card_pi_groups (A : Matrix ι κ ℝ) {β : Type*} [Fintype β]
    (b : Basis β ℝ (dimensionless A)) : Fintype.card β = Fintype.card κ - A.rank := by
  rw [← finrank_dimensionless, finrank_eq_card_basis b]

/-! ### Buckingham π: functional form -/

/-- The **dot-product functional** `k ↦ w ⬝ᵥ k`. -/
def dotLinear (w : κ → ℝ) : Dual ℝ (κ → ℝ) where
  toFun k := w ⬝ᵥ k
  map_add' := dotProduct_add w
  map_smul' c k := by simp [dotProduct_smul]

/-- **Orthogonal complement of the kernel**: a vector `w` is orthogonal to every dimensionless
exponent vector iff it lies in the row space of `A`, i.e. `w = u ᵥ* A` for some `u`. -/
theorem exists_vecMul_eq_iff (A : Matrix ι κ ℝ) (w : κ → ℝ) :
    (∀ k, IsDimensionless A k → w ⬝ᵥ k = 0) ↔ ∃ u : ι → ℝ, u ᵥ* A = w := by
  classical
  constructor
  · intro h
    have hmem : dotLinear w ∈ (LinearMap.ker A.mulVecLin).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      exact h k (by simpa [IsDimensionless] using hk)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨ψ, hψ⟩ := hmem
    refine ⟨fun i => ψ (Pi.single i 1), ?_⟩
    ext j
    have hj := LinearMap.congr_fun hψ (Pi.single j 1)
    simp only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply, mulVec_single_one,
      dotLinear, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single, mul_one] at hj
    rw [← hj, LinearMap.pi_apply_eq_sum_univ ψ]
    simp only [vecMul, dotProduct, col_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 2
    ext i'
    simp [Pi.single_apply, eq_comm]
  · rintro ⟨u, rfl⟩ k hk
    rw [← dotProduct_mulVec, hk, dotProduct_zero]

/-- **Buckingham π theorem (functional form)**. Two vectors of positive quantities give the same
value to every dimensionless monomial iff some change of units maps one onto the other. -/
theorem buckingham_pi (A : Matrix ι κ ℝ) {q q' : κ → ℝ} (hq : ∀ j, 0 < q j)
    (hq' : ∀ j, 0 < q' j) :
    (∀ k, IsDimensionless A k → monomial q k = monomial q' k) ↔
      ∃ s : ι → ℝ, (∀ i, 0 < s i) ∧ changeUnits A s q = q' := by
  constructor
  · intro h
    have hw : ∀ k, IsDimensionless A k → (logVec q' - logVec q) ⬝ᵥ k = 0 := by
      intro k hk
      have := h k hk
      rw [monomial_eq_exp hq, monomial_eq_exp hq', Real.exp_eq_exp] at this
      rw [sub_dotProduct, this, sub_self]
    obtain ⟨u, hu⟩ := (exists_vecMul_eq_iff A _).1 hw
    have hs : ∀ i, 0 < Real.exp (u i) := fun i => Real.exp_pos _
    refine ⟨fun i => Real.exp (u i), hs, ?_⟩
    have hlog : logVec (fun i => Real.exp (u i)) = u := by
      ext i; simp [logVec]
    ext j
    have hj := congr_fun hu j
    simp only [changeUnits, unitFactor_eq_exp A hs, hlog, hj, Pi.sub_apply, logVec,
      Real.exp_sub, Real.exp_log (hq j), Real.exp_log (hq' j)]
    field_simp [(hq j).ne']
  · rintro ⟨s, hs, rfl⟩ k hk
    exact (monomial_changeUnits_of_isDimensionless hs hq hk).symm

/-- A function of the quantities is **unit-invariant** if it takes the same value on positive
quantities and on their values after any change of units. -/
def UnitInvariant {β : Type*} (A : Matrix ι κ ℝ) (F : (κ → ℝ) → β) : Prop :=
  ∀ s : ι → ℝ, (∀ i, 0 < s i) → ∀ q : κ → ℝ, (∀ j, 0 < q j) → F (changeUnits A s q) = F q

/-- A unit-invariant function takes equal values on quantity vectors with equal π-groups. -/
theorem UnitInvariant.eq_of_monomial_eq {β : Type*} {A : Matrix ι κ ℝ} {F : (κ → ℝ) → β}
    (hF : UnitInvariant A F) {q q' : κ → ℝ} (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : ∀ k, IsDimensionless A k → monomial q k = monomial q' k) : F q = F q' := by
  obtain ⟨s, hs, rfl⟩ := (buckingham_pi A hq hq').1 h
  exact (hF s hs q hq).symm

omit [Fintype ι] in
/-- The values of the π-groups of a basis `b` of `ker A` determine all dimensionless monomials. -/
theorem monomial_eq_of_basis {A : Matrix ι κ ℝ} {β : Type*} (b : Basis β ℝ (dimensionless A))
    {q q' : κ → ℝ} (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : ∀ m, monomial q (b m) = monomial q' (b m)) (k : κ → ℝ) (hk : IsDimensionless A k) :
    monomial q k = monomial q' k := by
  let φ : dimensionless A →ₗ[ℝ] ℝ := (dotLinear (logVec q - logVec q')).comp
    (dimensionless A).subtype
  have hφ : φ = 0 := by
    refine b.ext fun m => ?_
    have := h m
    rw [monomial_eq_exp hq, monomial_eq_exp hq', Real.exp_eq_exp] at this
    simp [φ, dotLinear, sub_dotProduct, this]
  have := LinearMap.congr_fun hφ ⟨k, mem_dimensionless.2 hk⟩
  simp only [φ, dotLinear, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, sub_dotProduct] at this
  rw [monomial_eq_exp hq, monomial_eq_exp hq', sub_eq_zero.1 this]

/-- **Buckingham π theorem (with a basis)**: a unit-invariant function takes equal values on
quantity vectors whose `n - r` basic π-groups `π_m = monomial q (b m)` agree. -/
theorem buckingham_pi_basis {β γ : Type*} {A : Matrix ι κ ℝ} {F : (κ → ℝ) → γ}
    (hF : UnitInvariant A F) (b : Basis β ℝ (dimensionless A)) {q q' : κ → ℝ}
    (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : ∀ m, monomial q (b m) = monomial q' (b m)) : F q = F q' :=
  hF.eq_of_monomial_eq hq hq' (monomial_eq_of_basis b hq hq' h)

/-- **Buckingham π theorem**: a unit-invariant function `F` of the positive quantities is a
function `Φ` of the basic π-groups `π_m = monomial q (b m)` (`m` ranging over a basis of
`ker A`, which has `n - rank A` elements by `card_pi_groups`). -/
theorem exists_function_of_pi {β γ : Type*} [Nonempty γ] {A : Matrix ι κ ℝ}
    {F : (κ → ℝ) → γ} (hF : UnitInvariant A F) (b : Basis β ℝ (dimensionless A)) :
    ∃ Φ : (β → ℝ) → γ, ∀ q : κ → ℝ, (∀ j, 0 < q j) → F q = Φ fun m => monomial q (b m) := by
  classical
  let P : (β → ℝ) → (κ → ℝ) → Prop := fun π q => (∀ j, 0 < q j) ∧
    (fun m => monomial q (b m)) = π
  refine ⟨fun π => if h : ∃ q, P π q then F h.choose else Classical.arbitrary γ, ?_⟩
  intro q hq
  have hex : ∃ q', P (fun m => monomial q (b m)) q' := ⟨q, hq, rfl⟩
  dsimp only
  split_ifs
  obtain ⟨hpos, heq⟩ := hex.choose_spec
  exact buckingham_pi_basis hF b hq hpos fun m => (congr_fun heq m).symm

/-! ### Worked example: the simple pendulum -/

/-- Dimension matrix of the pendulum. Base dimensions `(M, L, T)`; quantities
`(period T, length L, gravity g, mass m)` with `[T] = T`, `[L] = L`, `[g] = L T⁻²`, `[m] = M`. -/
def pendulumDim : Matrix (Fin 3) (Fin 4) ℝ :=
  !![0, 0, 0, 1;
     0, 1, 1, 0;
     1, 0, -2, 0]

/-- The exponent vector of the π-group `T² g / L`. -/
def pendulumPi : Fin 4 → ℝ := ![2, -1, 1, 0]

/-- The kernel of the pendulum dimension matrix is spanned by `T² g / L`. -/
theorem pendulum_ker_iff (k : Fin 4 → ℝ) :
    IsDimensionless pendulumDim k ↔ ∃ c : ℝ, k = c • pendulumPi := by
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    have h2 := congr_fun h 2
    simp [pendulumDim, mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2
    refine ⟨k 2, ?_⟩
    ext j; fin_cases j <;> simp [pendulumPi] <;> linarith
  · rintro ⟨c, rfl⟩
    ext i
    fin_cases i <;> simp [pendulumDim, pendulumPi, mulVec, dotProduct, Fin.sum_univ_four]
    ring

/-- The mass cannot appear in any dimensionless monomial of the pendulum. -/
theorem pendulum_mass_exponent {k : Fin 4 → ℝ} (hk : IsDimensionless pendulumDim k) :
    k 3 = 0 := by
  obtain ⟨c, rfl⟩ := (pendulum_ker_iff k).1 hk
  simp [pendulumPi]

/-- The pendulum dimension matrix has full rank `3`. -/
theorem pendulum_rank : pendulumDim.rank = 3 := by
  have hs : LinearMap.range pendulumDim.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨![v 2, v 1, 0, v 0], ?_⟩
    ext i; fin_cases i <;> simp [pendulumDim, mulVec, dotProduct, Fin.sum_univ_four]
  rw [Matrix.rank, hs, finrank_top, Module.finrank_fin_fun]

/-- The pendulum has exactly one independent π-group (`4 - 3 = 1`). -/
theorem pendulum_finrank_ker : finrank ℝ (dimensionless pendulumDim) = 1 := by
  rw [finrank_dimensionless, pendulum_rank]; rfl

/-- **Period of the pendulum**: if the law `T = τ(L, g, m)` holds in every system of units, then
`T = C √(L / g)` with `C = τ(1, 1, 1)`; in particular the period does not depend on the mass. -/
theorem pendulum_period (τ : ℝ → ℝ → ℝ → ℝ)
    (hτ : ∀ s : Fin 3 → ℝ, (∀ i, 0 < s i) → ∀ L g m : ℝ, 0 < L → 0 < g → 0 < m →
      let q := changeUnits pendulumDim s ![τ L g m, L, g, m]
      q 0 = τ (q 1) (q 2) (q 3))
    {L g m : ℝ} (hL : 0 < L) (hg : 0 < g) (hm : 0 < m) :
    τ L g m = τ 1 1 1 * Real.sqrt (L / g) := by
  have hT : 0 < Real.sqrt (g / L) := Real.sqrt_pos.2 (div_pos hg hL)
  have hs : ∀ i, 0 < ![1 / m, 1 / L, Real.sqrt (g / L)] i := by
    intro i; fin_cases i <;> simp [hm, hL, hT]
  have h := hτ _ hs L g m hL hg hm
  simp only [changeUnits, unitFactor, pendulumDim, Fin.prod_univ_three] at h
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.isValue, cons_val_zero, of_apply,
    cons_val', cons_val_fin_one, Real.rpow_zero, cons_val_one, mul_one, cons_val, Real.rpow_one,
    one_mul, ne_eq, hL.ne', not_false_eq_true, inv_mul_cancel₀, Real.rpow_neg hT.le,
    Real.rpow_ofNat, Real.sq_sqrt (div_pos hg hL).le, inv_div, hm.ne'] at h
  have e : L⁻¹ * (L / g) * g = 1 := by field_simp
  rw [e] at h
  rw [← h, mul_comm √(g / L), mul_assoc, ← Real.sqrt_mul (div_pos hg hL).le, div_mul_div_comm,
    mul_comm g L, div_self (by positivity), Real.sqrt_one, mul_one]

/-! ### Worked example: drag on a sphere -/

/-- Dimension matrix for the drag on a sphere. Base dimensions `(M, L, T)`; quantities
`(drag F, density ρ, speed V, diameter D, viscosity μ)` with `[F] = M L T⁻²`, `[ρ] = M L⁻³`,
`[V] = L T⁻¹`, `[D] = L`, `[μ] = M L⁻¹ T⁻¹`. -/
def dragDim : Matrix (Fin 3) (Fin 5) ℝ :=
  !![1, 1, 0, 0, 1;
     1, -3, 1, 1, -1;
     -2, 0, -1, 0, -1]

/-- The exponent vector of the drag coefficient `F / (ρ V² D²)`. -/
def dragCoeff : Fin 5 → ℝ := ![1, -1, -2, -2, 0]

/-- The exponent vector of the Reynolds number `Re = ρ V D / μ`. -/
def reynolds : Fin 5 → ℝ := ![0, 1, 1, 1, -1]

/-- The dimensionless monomials of the drag problem are exactly the products of powers of the
drag coefficient and the Reynolds number. -/
theorem drag_ker_iff (k : Fin 5 → ℝ) :
    IsDimensionless dragDim k ↔ ∃ a b : ℝ, k = a • dragCoeff + b • reynolds := by
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    have h2 := congr_fun h 2
    simp [dragDim, mulVec, dotProduct, Fin.sum_univ_five] at h0 h1 h2
    refine ⟨k 0, -k 4, ?_⟩
    ext j; fin_cases j <;> simp [dragCoeff, reynolds] <;> linarith
  · rintro ⟨a, b, rfl⟩
    ext i
    fin_cases i <;> simp [dragDim, dragCoeff, reynolds, mulVec, dotProduct, Fin.sum_univ_five]
    all_goals ring

/-- The drag dimension matrix has full rank `3`. -/
theorem drag_rank : dragDim.rank = 3 := by
  have hs : LinearMap.range dragDim.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨![0, v 0, -v 2, v 1 + 3 * v 0 + v 2, 0], ?_⟩
    ext i; fin_cases i <;> simp [dragDim, mulVec, dotProduct, Fin.sum_univ_five]
    all_goals ring
  rw [Matrix.rank, hs, finrank_top, Module.finrank_fin_fun]

/-- The drag problem has exactly two independent π-groups (`5 - 3 = 2`). -/
theorem drag_finrank_ker : finrank ℝ (dimensionless dragDim) = 2 := by
  rw [finrank_dimensionless, drag_rank]; rfl

/-- **Drag on a sphere**: if the law `F = f(ρ, V, D, μ)` holds in every system of units, then
`F = ρ V² D² Φ(Re)` with `Re = ρ V D / μ`, i.e. the drag coefficient `F / (ρ V² D²)` is a
function of the Reynolds number alone. -/
theorem drag_law (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ s : Fin 3 → ℝ, (∀ i, 0 < s i) → ∀ ρ V D μ : ℝ, 0 < ρ → 0 < V → 0 < D → 0 < μ →
      let q := changeUnits dragDim s ![f ρ V D μ, ρ, V, D, μ]
      q 0 = f (q 1) (q 2) (q 3) (q 4)) :
    ∃ Φ : ℝ → ℝ, ∀ ρ V D μ : ℝ, 0 < ρ → 0 < V → 0 < D → 0 < μ →
      f ρ V D μ = ρ * V ^ 2 * D ^ 2 * Φ (ρ * V * D / μ) := by
  refine ⟨fun r => f 1 1 1 r⁻¹, fun ρ V D μ hρ hV hD hμ => ?_⟩
  have hs : ∀ i, 0 < ![1 / (ρ * D ^ 3), 1 / D, V / D] i := by
    intro i
    fin_cases i
    · change 0 < 1 / (ρ * D ^ 3); positivity
    · change 0 < 1 / D; positivity
    · change 0 < V / D; positivity
  have h := hf _ hs ρ V D μ hρ hV hD hμ
  simp only [changeUnits, unitFactor, dragDim, Fin.prod_univ_three] at h
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, _root_.mul_inv_rev, Fin.isValue,
    cons_val_zero, of_apply, cons_val', cons_val_fin_one, Real.rpow_one, cons_val_one, cons_val,
    Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, inv_inv, Real.rpow_zero,
    mul_one, one_mul, Real.rpow_neg_one, inv_div] at h
  have e1 : (D ^ 3)⁻¹ * ρ⁻¹ * D ^ 3 * ρ = 1 := by field_simp
  have e2 : D⁻¹ * (D / V) * V = 1 := by field_simp
  have e3 : D⁻¹ * D = 1 := by field_simp
  have e4 : (D ^ 3)⁻¹ * ρ⁻¹ * D * (D / V) * μ = (ρ * V * D / μ)⁻¹ := by field_simp
  rw [e1, e2, e3, e4] at h
  beta_reduce
  rw [← h]
  field_simp

end DimensionalAnalysis

end ClassicalMechanics
