import ContinuumMechanics.Plates.Energy

/-!
# Plane elasticity and the Airy stress function

In plane elasticity (`n = 2`, coordinates `x₁ = x 0`, `x₂ = x 1`) the **Airy stress function**
`φ` generates the stresses

`σ₁₁ = ∂₂∂₂φ`, `σ₂₂ = ∂₁∂₁φ`, `σ₁₂ = -∂₁∂₂φ`   (`sig11`, `sig22`, `sig12`).

## Main results

* `airy_equilibrium₁`, `airy_equilibrium₂`: for `φ ∈ C³` the Airy stresses satisfy the
  equilibrium equations without body force, `∂₁σ₁₁ + ∂₂σ₁₂ = 0` and `∂₁σ₁₂ + ∂₂σ₂₂ = 0`.
* `compat_airy`: for an isotropic in-plane compliance law
  `ε₁₁ = a σ₁₁ - b σ₂₂`, `ε₂₂ = a σ₂₂ - b σ₁₁`, `ε₁₂ = (a + b) σ₁₂` and `φ ∈ C⁴`, the
  two-dimensional Saint-Venant compatibility residual `∂₂∂₂ε₁₁ + ∂₁∂₁ε₂₂ - 2∂₁∂₂ε₁₂` equals
  `a Δ²φ`; hence (`compat_iff_biharmonic`) the Airy strains are compatible iff `Δ²φ = 0`
  (for `a ≠ 0`).
* Specialisations: **plane stress** (`a = 1/E`, `b = ν/E`; `compat_planeStress`),
  **plane strain** (`a = (1 - ν²)/E`, `b = ν(1 + ν)/E`; `compat_planeStrain`) and plane strain
  in Lamé moduli (`a = (λ + 2μ)/(4μ(λ + μ))`, `b = λ/(4μ(λ + μ))`; `compat_planeStrainLame`),
  with the inverse (stiffness) laws `planeStress_hooke` and `planeStrainLame_hooke`.
* Classical polynomial solutions, computed exactly and shown to be biharmonic:
  uniaxial tension `φ = σ₀ x₂²/2` (`uniaxial_*`), pure bending `φ = c x₂³/6` with
  `σ₁₁ = c x₂` (`bending_*`), the end-loaded cantilever `φ = d (x₁x₂³ - 3c²x₁x₂)`
  (`cantilever_*`) and the simply supported beam under uniform load (`ssBeam_*`).

Partial derivatives are `Korn.pd` and `Δ²` is `Plates.Energy.bilap`. A small calculus of `pd`
on sums, products and powers (`pd_fun_add`, `pd_fun_mul`, `pd_fun_pow`, …) evaluates the
derivatives of the polynomial examples.

## References

* [TimoshenkoGoodier1970] S. P. Timoshenko, J. N. Goodier, *Theory of Elasticity*, 3rd ed.,
  §§16–24.
* [Barber2010] J. R. Barber, *Elasticity*, 3rd ed., Chapters 4–5.
-/

open scoped ContDiff

noncomputable section

namespace ContinuumMechanics.Airy

open Korn Plates.Energy

/-! ### Calculus of partial derivatives -/

section Calculus

variable {n : ℕ} {f g : (Fin n → ℝ) → ℝ}

/-- `∂ⱼ c = 0`. -/
theorem pd_fun_const (c : ℝ) (j : Fin n) : pd (fun _ => c) j = fun _ => 0 := by
  funext x; simp [pd]

/-- `∂ⱼ xᵢ = δᵢⱼ`. -/
theorem pd_coord (i j : Fin n) : pd (fun x => x i) j = fun _ => if i = j then 1 else 0 := by
  funext x
  simp only [pd]
  rw [show (fun x : Fin n → ℝ => x i) =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i from rfl,
    ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

/-- Additivity of `∂ⱼ`. -/
theorem pd_fun_add (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    pd (fun x => f x + g x) j = fun x => pd f j x + pd g j x := by
  funext x; simp [pd, fderiv_fun_add (hf x) (hg x)]

/-- `∂ⱼ (f - g) = ∂ⱼ f - ∂ⱼ g`. -/
theorem pd_fun_sub (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    pd (fun x => f x - g x) j = fun x => pd f j x - pd g j x := by
  funext x; simp [pd, fderiv_fun_sub (hf x) (hg x)]

/-- `∂ⱼ (-f) = -∂ⱼ f`. -/
theorem pd_fun_neg (j : Fin n) : pd (fun x => -f x) j = fun x => -pd f j x := by
  funext x; simp [pd, fderiv_fun_neg]

/-- **Product rule** for `∂ⱼ`. -/
theorem pd_fun_mul (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    pd (fun x => f x * g x) j = fun x => pd f j x * g x + f x * pd g j x := by
  funext x; simp [pd, fderiv_fun_mul (hf x) (hg x)]; ring

/-- **Power rule** for `∂ⱼ`. -/
theorem pd_fun_pow (hf : Differentiable ℝ f) (k : ℕ) (j : Fin n) :
    pd (fun x => f x ^ k) j = fun x => k * f x ^ (k - 1) * pd f j x := by
  funext x; simp [pd, fderiv_fun_pow k (hf x)]

/-- `∂ⱼ (f / c) = ∂ⱼ f / c`. -/
theorem pd_fun_div_const (hf : Differentiable ℝ f) (c : ℝ) (j : Fin n) :
    pd (fun x => f x / c) j = fun x => pd f j x / c := by
  simp only [div_eq_mul_inv]
  rw [pd_fun_mul hf (differentiable_const _), pd_fun_const]
  simp

end Calculus

/-- Evaluates partial derivatives of explicit polynomial expressions. -/
macro "pd_simp" : tactic =>
  `(tactic| simp (disch := fun_prop) only [pd_fun_mul, pd_fun_pow, pd_fun_const, pd_coord,
    pd_fun_add, pd_fun_sub, pd_fun_neg, pd_fun_div_const, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one, pow_one, pow_zero, mul_one, one_mul, mul_zero,
    zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div])

/-! ### Airy stresses and equilibrium -/

variable {φ : (Fin 2 → ℝ) → ℝ}

/-- The Airy normal stress `σ₁₁ = ∂₂∂₂φ`. -/
def sig11 (φ : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ := pd (pd φ 1) 1

/-- The Airy normal stress `σ₂₂ = ∂₁∂₁φ`. -/
def sig22 (φ : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ := pd (pd φ 0) 0

/-- The Airy shear stress `σ₁₂ = -∂₁∂₂φ`. -/
def sig12 (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := -pd (pd φ 0) 1 x

/-- `σ₁₂` as a function. -/
theorem sig12_eq (φ : (Fin 2 → ℝ) → ℝ) : sig12 φ = fun x => -pd (pd φ 0) 1 x := rfl

/-- **First equilibrium equation**: `∂₁σ₁₁ + ∂₂σ₁₂ = 0` for `φ ∈ C³`. -/
theorem airy_equilibrium₁ (hφ : ContDiff ℝ 3 φ) (x : Fin 2 → ℝ) :
    pd (sig11 φ) 0 x + pd (sig12 φ) 1 x = 0 := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have h1 : ContDiff ℝ 2 (pd φ 1) := contDiff_pd_of_le hφ (by norm_num) 1
  simp only [sig11, sig12_eq, pd_fun_neg, pd_pd_comm h1 1 0, pd_pd_comm h2 1 0]
  ring

/-- **Second equilibrium equation**: `∂₁σ₁₂ + ∂₂σ₂₂ = 0` for `φ ∈ C³`. -/
theorem airy_equilibrium₂ (hφ : ContDiff ℝ 3 φ) (x : Fin 2 → ℝ) :
    pd (sig12 φ) 0 x + pd (sig22 φ) 1 x = 0 := by
  have h0 : ContDiff ℝ 2 (pd φ 0) := contDiff_pd_of_le hφ (by norm_num) 0
  simp only [sig22, sig12_eq, pd_fun_neg, pd_pd_comm h0 0 1]
  ring

/-! ### Constitutive law and compatibility -/

/-- In-plane strain `ε₁₁ = a σ₁₁ - b σ₂₂` from the Airy stresses (compliances `a`, `b`). -/
def eps11 (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := a * sig11 φ x - b * sig22 φ x

/-- In-plane strain `ε₂₂ = a σ₂₂ - b σ₁₁` from the Airy stresses. -/
def eps22 (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := a * sig22 φ x - b * sig11 φ x

/-- In-plane shear strain `ε₁₂ = (a + b) σ₁₂` from the Airy stresses. -/
def eps12 (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := (a + b) * sig12 φ x

/-- `ε₁₁` as a function. -/
theorem eps11_eq (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) :
    eps11 a b φ = fun x => a * sig11 φ x - b * sig22 φ x := rfl

/-- `ε₂₂` as a function. -/
theorem eps22_eq (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) :
    eps22 a b φ = fun x => a * sig22 φ x - b * sig11 φ x := rfl

/-- `ε₁₂` as a function. -/
theorem eps12_eq (a b : ℝ) (φ : (Fin 2 → ℝ) → ℝ) :
    eps12 a b φ = fun x => (a + b) * sig12 φ x := rfl

/-- The 2D Saint-Venant compatibility residual `∂₂∂₂ε₁₁ + ∂₁∂₁ε₂₂ - 2∂₁∂₂ε₁₂`. -/
def compat (e11 e22 e12 : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  pd (pd e11 1) 1 x + pd (pd e22 0) 0 x - 2 * pd (pd e12 0) 1 x

/-- **Compatibility of the Airy strains**: the residual equals `a Δ²φ` for `φ ∈ C⁴`. -/
theorem compat_airy (a b : ℝ) (hφ : ContDiff ℝ 4 φ) (x : Fin 2 → ℝ) :
    compat (eps11 a b φ) (eps22 a b φ) (eps12 a b φ) x = a * bilap φ x := by
  have c2 : ∀ i j, ContDiff ℝ 2 (pd (pd φ i) j) := fun i j =>
    contDiff_pd_of_le (contDiff_pd_of_le hφ (k := 3) (by norm_num) i) (by norm_num) j
  have c3 : ∀ i j k, ContDiff ℝ 1 (pd (pd (pd φ i) j) k) := fun i j k => contDiff_pd (c2 i j) k
  have d2 : ∀ i j, Differentiable ℝ (pd (pd φ i) j) := fun i j =>
    (c2 i j).differentiable (by norm_num)
  have d3 : ∀ i j k, Differentiable ℝ (pd (pd (pd φ i) j) k) := fun i j k =>
    (c3 i j k).differentiable one_ne_zero
  -- equality of the mixed fourth derivatives
  have hφ3 : ContDiff ℝ 2 (pd φ 0) := contDiff_pd_of_le hφ (by norm_num) 0
  have hφ3' : ContDiff ℝ 2 (pd φ 1) := contDiff_pd_of_le hφ (by norm_num) 1
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have e1 : pd (pd (pd (pd φ 0) 1) 0) 1 = pd (pd (pd (pd φ 0) 0) 1) 1 := by
    rw [pd_pd_comm hφ3 1 0]
  have e2 : pd (pd (pd (pd φ 1) 1) 0) 0 = pd (pd (pd (pd φ 0) 0) 1) 1 := by
    rw [pd_pd_comm hφ3' 1 0, pd_pd_comm h2 1 0, pd_pd_comm (c2 0 1) 1 0, pd_pd_comm hφ3 1 0]
  simp only [compat, eps11_eq, eps22_eq, eps12_eq, sig11, sig22, sig12_eq]
  have := d2 0 0; have := d2 1 1; have := d2 0 1
  have := d3 1 1 1; have := d3 0 0 1; have := d3 0 0 0; have := d3 1 1 0; have := d3 0 1 0
  simp (disch := fun_prop) only [pd_fun_sub, pd_fun_mul, pd_fun_const, pd_fun_neg,
    zero_mul, zero_add]
  simp only [bilap, Fin.sum_univ_two, e1, e2]
  ring

/-- **Compatible ⇔ biharmonic**: for `a ≠ 0` and `φ ∈ C⁴` the Airy strains satisfy the
Saint-Venant compatibility equation everywhere iff `Δ²φ = 0`. -/
theorem compat_iff_biharmonic {a : ℝ} (b : ℝ) (ha : a ≠ 0) (hφ : ContDiff ℝ 4 φ) :
    (∀ x, compat (eps11 a b φ) (eps22 a b φ) (eps12 a b φ) x = 0) ↔ ∀ x, bilap φ x = 0 := by
  simp only [compat_airy a b hφ, mul_eq_zero, ha, false_or]

/-- **Plane stress** (`ε₁₁ = (σ₁₁ - νσ₂₂)/E`, `ε₁₂ = (1 + ν)σ₁₂/E`): the compatibility residual
is `Δ²φ / E`. -/
theorem compat_planeStress (E ν : ℝ) (hφ : ContDiff ℝ 4 φ) (x : Fin 2 → ℝ) :
    compat (eps11 (1 / E) (ν / E) φ) (eps22 (1 / E) (ν / E) φ) (eps12 (1 / E) (ν / E) φ) x =
      bilap φ x / E := by
  rw [compat_airy _ _ hφ]; ring

/-- **Plane strain** (`ε₁₁ = ((1 - ν²)σ₁₁ - ν(1 + ν)σ₂₂)/E`): the compatibility residual is
`(1 - ν²) Δ²φ / E`. -/
theorem compat_planeStrain (E ν : ℝ) (hφ : ContDiff ℝ 4 φ) (x : Fin 2 → ℝ) :
    compat (eps11 ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ)
        (eps22 ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ)
        (eps12 ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ) x =
      (1 - ν ^ 2) / E * bilap φ x :=
  compat_airy _ _ hφ x

/-- Plane-strain compliances in terms of the Lamé moduli: `a = (λ + 2μ)/(4μ(λ + μ))`. -/
def lameA (lam μ : ℝ) : ℝ := (lam + 2 * μ) / (4 * μ * (lam + μ))

/-- Plane-strain compliances in terms of the Lamé moduli: `b = λ/(4μ(λ + μ))`. -/
def lameB (lam μ : ℝ) : ℝ := lam / (4 * μ * (lam + μ))

/-- **Plane strain, Lamé form**: the compatibility residual is `(λ + 2μ)/(4μ(λ + μ)) Δ²φ`. -/
theorem compat_planeStrainLame (lam μ : ℝ) (hφ : ContDiff ℝ 4 φ) (x : Fin 2 → ℝ) :
    compat (eps11 (lameA lam μ) (lameB lam μ) φ) (eps22 (lameA lam μ) (lameB lam μ) φ)
        (eps12 (lameA lam μ) (lameB lam μ) φ) x =
      (lam + 2 * μ) / (4 * μ * (lam + μ)) * bilap φ x :=
  compat_airy _ _ hφ x

/-- The plane-stress compliance law inverts to the plane-stress Hooke law
`σ₁₁ = E/(1 - ν²) (ε₁₁ + ν ε₂₂)`, `σ₂₂ = E/(1 - ν²) (ε₂₂ + ν ε₁₁)`, `σ₁₂ = E/(1 + ν) ε₁₂`. -/
theorem planeStress_hooke {E ν : ℝ} (hE : E ≠ 0) (h1 : 1 - ν ≠ 0) (h2 : 1 + ν ≠ 0)
    (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    sig11 φ x = E / (1 - ν ^ 2) * (eps11 (1 / E) (ν / E) φ x + ν * eps22 (1 / E) (ν / E) φ x) ∧
    sig22 φ x = E / (1 - ν ^ 2) * (eps22 (1 / E) (ν / E) φ x + ν * eps11 (1 / E) (ν / E) φ x) ∧
    sig12 φ x = E / (1 + ν) * eps12 (1 / E) (ν / E) φ x := by
  have h3 : 1 - ν ^ 2 ≠ 0 := by
    rw [show 1 - ν ^ 2 = (1 - ν) * (1 + ν) by ring]; exact mul_ne_zero h1 h2
  simp only [eps11, eps22, eps12]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The Lamé plane-strain compliance law inverts to `σ₁₁ = (λ + 2μ)ε₁₁ + λε₂₂`,
`σ₂₂ = λε₁₁ + (λ + 2μ)ε₂₂`, `σ₁₂ = 2μ ε₁₂`. -/
theorem planeStrainLame_hooke {lam μ : ℝ} (hμ : μ ≠ 0) (hlm : lam + μ ≠ 0)
    (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    sig11 φ x = (lam + 2 * μ) * eps11 (lameA lam μ) (lameB lam μ) φ x +
      lam * eps22 (lameA lam μ) (lameB lam μ) φ x ∧
    sig22 φ x = lam * eps11 (lameA lam μ) (lameB lam μ) φ x +
      (lam + 2 * μ) * eps22 (lameA lam μ) (lameB lam μ) φ x ∧
    sig12 φ x = 2 * μ * eps12 (lameA lam μ) (lameB lam μ) φ x := by
  simp only [eps11, eps22, eps12, lameA, lameB]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ### Polynomial solutions -/

/-- **Uniaxial tension** `φ = σ₀ x₂²/2`. -/
def uniaxial (σ₀ : ℝ) (x : Fin 2 → ℝ) : ℝ := σ₀ * x 1 ^ 2 / 2

/-- Uniaxial tension: `σ₁₁ = σ₀`, `σ₂₂ = σ₁₂ = 0`, and `Δ²φ = 0`. -/
theorem uniaxial_stress (σ₀ : ℝ) (x : Fin 2 → ℝ) :
    sig11 (uniaxial σ₀) x = σ₀ ∧ sig22 (uniaxial σ₀) x = 0 ∧ sig12 (uniaxial σ₀) x = 0 ∧
      bilap (uniaxial σ₀) x = 0 := by
  unfold uniaxial
  simp only [sig11, sig22, sig12, bilap, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> pd_simp
  ring

/-- **Pure bending** of a beam, `φ = m x₂³/6`. -/
def bending (m : ℝ) (x : Fin 2 → ℝ) : ℝ := m * x 1 ^ 3 / 6

/-- Pure bending: `σ₁₁ = m x₂`, `σ₂₂ = σ₁₂ = 0`, and `Δ²φ = 0`. -/
theorem bending_stress (m : ℝ) (x : Fin 2 → ℝ) :
    sig11 (bending m) x = m * x 1 ∧ sig22 (bending m) x = 0 ∧ sig12 (bending m) x = 0 ∧
      bilap (bending m) x = 0 := by
  unfold bending
  simp only [sig11, sig22, sig12, bilap, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> pd_simp
  ring

/-- **End-loaded cantilever** `φ = d (x₁x₂³ - 3c²x₁x₂)` on the strip `|x₂| ≤ c`. -/
def cantilever (d c : ℝ) (x : Fin 2 → ℝ) : ℝ := d * (x 0 * x 1 ^ 3 - 3 * c ^ 2 * x 0 * x 1)

/-- `∂₁` of the cantilever Airy function. -/
theorem cantilever_pd0 (d c : ℝ) :
    pd (cantilever d c) 0 = fun x => d * (x 1 ^ 3 - 3 * c ^ 2 * x 1) := by
  unfold cantilever; pd_simp

/-- `∂₂` of the cantilever Airy function. -/
theorem cantilever_pd1 (d c : ℝ) :
    pd (cantilever d c) 1 = fun x => d * (3 * x 0 * x 1 ^ 2 - 3 * c ^ 2 * x 0) := by
  unfold cantilever; pd_simp; funext x; ring

/-- Cantilever: `σ₁₁ = 6d x₁x₂` (bending stress growing linearly from the loaded end),
`σ₂₂ = 0`, the parabolic shear `σ₁₂ = 3d (c² - x₂²)`, and `Δ²φ = 0`. -/
theorem cantilever_stress (d c : ℝ) (x : Fin 2 → ℝ) :
    sig11 (cantilever d c) x = 6 * d * x 0 * x 1 ∧ sig22 (cantilever d c) x = 0 ∧
      sig12 (cantilever d c) x = 3 * d * (c ^ 2 - x 1 ^ 2) ∧ bilap (cantilever d c) x = 0 := by
  simp only [sig11, sig22, sig12, bilap, Fin.sum_univ_two, cantilever_pd0, cantilever_pd1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try pd_simp) <;> ring

/-- Cantilever: the long edges `x₂ = ±c` are traction free (`σ₂₂ = σ₁₂ = 0`). -/
theorem cantilever_traction_free (d c : ℝ) (x : Fin 2 → ℝ) (hx : x 1 = c ∨ x 1 = -c) :
    sig22 (cantilever d c) x = 0 ∧ sig12 (cantilever d c) x = 0 := by
  obtain ⟨-, h2, h12, -⟩ := cantilever_stress d c x
  refine ⟨h2, ?_⟩
  rw [h12]
  rcases hx with h | h <;> rw [h] <;> ring

/-- **Simply supported beam under uniform load** (span `|x₁| ≤ l`, depth `|x₂| ≤ c`), with
`k = q/(2I)`:
`φ = k (-x₁²(x₂³/3 - c²x₂ + 2c³/3)/2 + l²x₂³/6 + x₂⁵/30 - c²x₂³/15)`. -/
def ssBeam (k l c : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  k * (-(x 0 ^ 2 * (x 1 ^ 3 / 3 - c ^ 2 * x 1 + 2 * c ^ 3 / 3)) / 2 + l ^ 2 * x 1 ^ 3 / 6 +
    x 1 ^ 5 / 30 - c ^ 2 * x 1 ^ 3 / 15)

/-- `∂₁` of the simply supported beam Airy function. -/
theorem ssBeam_pd0 (k l c : ℝ) :
    pd (ssBeam k l c) 0 = fun x => -k * x 0 * (x 1 ^ 3 / 3 - c ^ 2 * x 1 + 2 * c ^ 3 / 3) := by
  unfold ssBeam; pd_simp; funext x; ring

/-- `∂₂` of the simply supported beam Airy function. -/
theorem ssBeam_pd1 (k l c : ℝ) :
    pd (ssBeam k l c) 1 = fun x => k * (-(x 0 ^ 2 * (x 1 ^ 2 - c ^ 2)) / 2 +
      l ^ 2 * x 1 ^ 2 / 2 + x 1 ^ 4 / 6 - c ^ 2 * x 1 ^ 2 / 5) := by
  unfold ssBeam; pd_simp; funext x; ring

/-- `σ₂₂ = ∂₁∂₁φ` for the simply supported beam. -/
theorem ssBeam_pd00 (k l c : ℝ) :
    pd (pd (ssBeam k l c) 0) 0 = fun x => -k * (x 1 ^ 3 / 3 - c ^ 2 * x 1 + 2 * c ^ 3 / 3) := by
  rw [ssBeam_pd0]; pd_simp

/-- `∂₂∂₂φ` for the simply supported beam. -/
theorem ssBeam_pd11 (k l c : ℝ) :
    pd (pd (ssBeam k l c) 1) 1 = fun x =>
      k * ((l ^ 2 - x 0 ^ 2) * x 1 + 2 * x 1 ^ 3 / 3 - 2 * c ^ 2 * x 1 / 5) := by
  rw [ssBeam_pd1]; pd_simp; funext x; ring

/-- `∂₁∂₂φ` for the simply supported beam. -/
theorem ssBeam_pd01 (k l c : ℝ) :
    pd (pd (ssBeam k l c) 0) 1 = fun x => -k * x 0 * (x 1 ^ 2 - c ^ 2) := by
  rw [ssBeam_pd0]; pd_simp; funext x; ring

/-- Simply supported beam: the classical stresses
`σ₁₁ = k ((l² - x₁²)x₂ + 2x₂³/3 - 2c²x₂/5)`, `σ₂₂ = -k (x₂³/3 - c²x₂ + 2c³/3)`,
`σ₁₂ = -k (c² - x₂²) x₁`, and `Δ²φ = 0`. -/
theorem ssBeam_stress (k l c : ℝ) (x : Fin 2 → ℝ) :
    sig11 (ssBeam k l c) x =
        k * ((l ^ 2 - x 0 ^ 2) * x 1 + 2 * x 1 ^ 3 / 3 - 2 * c ^ 2 * x 1 / 5) ∧
      sig22 (ssBeam k l c) x = -k * (x 1 ^ 3 / 3 - c ^ 2 * x 1 + 2 * c ^ 3 / 3) ∧
      sig12 (ssBeam k l c) x = -k * (c ^ 2 - x 1 ^ 2) * x 0 ∧ bilap (ssBeam k l c) x = 0 := by
  simp only [sig11, sig22, sig12, bilap, Fin.sum_univ_two, ssBeam_pd00, ssBeam_pd11,
    ssBeam_pd01]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try pd_simp) <;> ring

/-- Simply supported beam: the lower edge `x₂ = c` is traction free and the upper edge
`x₂ = -c` carries the normal pressure `σ₂₂ = -4kc³/3 = -q` (with `I = 2c³/3`) and no shear. -/
theorem ssBeam_edges (k l c : ℝ) (x : Fin 2 → ℝ) :
    (x 1 = c → sig22 (ssBeam k l c) x = 0 ∧ sig12 (ssBeam k l c) x = 0) ∧
    (x 1 = -c → sig22 (ssBeam k l c) x = -(4 * k * c ^ 3 / 3) ∧
      sig12 (ssBeam k l c) x = 0) := by
  obtain ⟨-, h2, h12, -⟩ := ssBeam_stress k l c x
  rw [h2, h12]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] <;> constructor <;> ring

/-- Every polynomial example is smooth, so `compat_iff_biharmonic` applies: e.g. the
simply supported beam stresses give compatible plane-stress strains. -/
theorem ssBeam_compat (k l c E ν : ℝ) (x : Fin 2 → ℝ) :
    compat (eps11 (1 / E) (ν / E) (ssBeam k l c)) (eps22 (1 / E) (ν / E) (ssBeam k l c))
      (eps12 (1 / E) (ν / E) (ssBeam k l c)) x = 0 := by
  rw [compat_planeStress E ν (by unfold ssBeam; fun_prop), (ssBeam_stress k l c x).2.2.2,
    zero_div]

end ContinuumMechanics.Airy
