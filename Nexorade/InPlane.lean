import Nexorade.OutOfPlane

/-!
# The nexorade unit cell: in-plane (membrane) auxiliary problem

In the plane of the nexorade the spherical joints transmit in-plane forces as well. Let
`X = (X₀, …, X₃)` and `Y = (Y₀, …, Y₃)` be the components along `e₁` and `e₂` of the contact
forces on the beam `h` (along `e₁`). Through the lattice (action–reaction, as out of plane) the
forces on `v` (along `e₂`) are `partner X` along `e₁` and `partner Y` along `e₂`. Hence

* `X` is the **axial** load of `h` and the **in-plane transverse** load of `v`;
* `Y` is the **in-plane transverse** load of `h` and the **axial** load of `v`.

Equilibrium of both beams (forces and in-plane moments, hinged ends) leaves **four** free
unknowns; prescribing the macroscopic membrane forces `N₁₁ = (1/A)∫_h N`, `N₂₂ = (1/A)∫_v N`
removes two, and the remaining two are fixed by **minimising the complementary energy**
([Greco2013], App. 8).

## Main results

* `InPlane.N12_eq_zero`: the cell carries no membrane shear (`∫` of the in-plane shear of a hinged
  beam vanishes).
* `InPlane.admissible_opt`, `InPlane.energy_opt`: the optimal field and its energy
  `Π / A = ½ A₁₁₁₁ (N₁₁² + N₂₂²)`.
* `InPlane.energy_opt_le`: **minimum complementary energy**: every admissible field with the same
  `N₁₁, N₂₂` has at least this energy.
* Consequently the membrane compliance is diagonal: `A₁₁₁₁ = A₂₂₂₂`, **`A₂₂₁₁ = 0`** (no Poisson
  effect), with

  `A₁₁₁₁ = (1/A) (a b (2a + b) / (2 G Sₛ) + (4a³ + 6a²b + 5ab² + 2b³) / (2 E S)
                + a² b² (2a + b) / (12 E I))`.

  The shear and axial terms agree with [Greco2013], App. 8; the bending term there reads
  `a²b²(16a + b)/(24EI)`, which does not match the cell problem (here `a²b²(4a + 2b)/(24EI)`).

## References

* [Greco2013] L. Greco, *Nexorade* (homogenization of reciprocal systems), draft 2013, App. 8.
-/

noncomputable section

namespace ContinuumMechanics.Nexorade

namespace Cell

variable (c : Cell)

/-- Sum of the forces on one beam. -/
def Forces.sum (f : Forces) : ℝ := f.f₀ + f.f₁ + f.f₂ + f.f₃

/-- Axial complementary energy of one beam under axial contact forces `f`. -/
def axialEnergy (ES : ℝ) (f : Forces) : ℝ :=
  (c.a * f.f₀ ^ 2 + c.b * (f.f₀ + f.f₁) ^ 2 + c.a * (f.f₀ + f.f₁ + f.f₂) ^ 2) / (2 * ES)

/-- Bending + shear complementary energy of one beam under transverse contact forces `f`, with
bending stiffness `EI` and shear stiffness `GS`. -/
def bendEnergy (EI GS : ℝ) (f : Forces) : ℝ :=
  (c.a * (0 ^ 2 + 0 * c.m₁ f + c.m₁ f ^ 2) / 3 +
      c.b * (c.m₁ f ^ 2 + c.m₁ f * c.m₂ f + c.m₂ f ^ 2) / 3 +
      c.a * (c.m₂ f ^ 2 + c.m₂ f * c.m₃ f + c.m₃ f ^ 2) / 3) / (2 * EI) +
    (c.a * f.f₀ ^ 2 + c.b * (f.f₀ + f.f₁) ^ 2 + c.a * (f.f₀ + f.f₁ + f.f₂) ^ 2) / (2 * GS)

/-- An in-plane field: contact forces on `h` along `e₁` (`X`) and `e₂` (`Y`). -/
structure InPlane where
  X : Forces
  Y : Forces

namespace InPlane

variable {c}

/-- Static admissibility: `h` and `v` in equilibrium in the plane. -/
def Admissible (c : Cell) (F : InPlane) : Prop :=
  Forces.sum F.X = 0 ∧ c.m₃ (partner F.X) = 0 ∧ Forces.sum F.Y = 0 ∧ c.m₃ F.Y = 0

/-- `N₁₁ = (1/A) ∫_h N` (`∫` of the piecewise-constant axial force of `h` is `m₃ X`). -/
def N11 (c : Cell) (F : InPlane) : ℝ := c.m₃ F.X / c.area
/-- `N₂₂ = (1/A) ∫_v N`. -/
def N22 (c : Cell) (F : InPlane) : ℝ := c.m₃ (partner F.Y) / c.area
/-- `N₁₂ = (1/2A) (∫_h V + ∫_v V)` (in-plane shear forces). -/
def N12 (c : Cell) (F : InPlane) : ℝ := (c.m₃ F.Y + c.m₃ (partner F.X)) / (2 * c.area)

/-- **No membrane shear**: `N₁₂ = 0` for every admissible field. -/
theorem N12_eq_zero {F : InPlane} (hF : Admissible c F) : N12 c F = 0 := by
  rw [N12, hF.2.2.2, hF.2.1, add_zero, zero_div]

/-- Complementary energy of the cell (axial `ES`, in-plane bending `EI`, in-plane shear `GS`). -/
def energy (c : Cell) (ES EI GS : ℝ) (F : InPlane) : ℝ :=
  c.axialEnergy ES F.X + c.bendEnergy EI GS (partner F.X) +
    c.bendEnergy EI GS F.Y + c.axialEnergy ES (partner F.Y)

/-- The optimal field for prescribed `N₁₁ = n₁`, `N₂₂ = n₂`. -/
def opt (c : Cell) (n₁ n₂ : ℝ) : InPlane where
  X := ⟨n₁ * (2 * c.a + c.b) / 2, c.b * n₁ / 2, -(c.b * n₁ / 2), -(n₁ * (2 * c.a + c.b) / 2)⟩
  Y := ⟨c.b * n₂ / 2, -(c.b * n₂ / 2) - c.a * n₂, c.a * n₂ + c.b * n₂ / 2, -(c.b * n₂ / 2)⟩

theorem m3_optX (n₁ n₂ : ℝ) : c.m₃ (opt c n₁ n₂).X = n₁ * c.area := by
  simp only [m₃, m₂, m₁, opt, area]; ring

theorem m3_optY (n₁ n₂ : ℝ) : c.m₃ (partner (opt c n₁ n₂).Y) = n₂ * c.area := by
  simp only [m₃, m₂, m₁, partner, opt, area]; ring

theorem admissible_opt (n₁ n₂ : ℝ) :
    Admissible c (opt c n₁ n₂) ∧ N11 c (opt c n₁ n₂) = n₁ ∧ N22 c (opt c n₁ n₂) = n₂ := by
  have hA := c.area_pos.ne'
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Forces.sum, opt]; ring
  · simp only [m₃, m₂, m₁, partner, opt]; ring
  · simp only [Forces.sum, opt]; ring
  · simp only [m₃, m₂, m₁, opt]; ring
  · rw [N11, m3_optX]; field_simp
  · rw [N22, m3_optY]; field_simp

/-- The **membrane compliance** `A₁₁₁₁ = A₂₂₂₂`. -/
def compliance11 (c : Cell) (ES EI GS : ℝ) : ℝ :=
  (c.a * c.b * (2 * c.a + c.b) / (2 * GS) +
      (4 * c.a ^ 3 + 6 * c.a ^ 2 * c.b + 5 * c.a * c.b ^ 2 + 2 * c.b ^ 3) / (2 * ES) +
      c.a ^ 2 * c.b ^ 2 * (2 * c.a + c.b) / (12 * EI)) / c.area

/-- **Energy of the optimal field**: `Π / A = ½ A₁₁₁₁ (N₁₁² + N₂₂²)`; in particular the membrane
compliance is diagonal with `A₂₂₁₁ = 0`. -/
theorem energy_opt {ES EI GS : ℝ} (hES : ES ≠ 0) (hEI : EI ≠ 0) (hGS : GS ≠ 0) (n₁ n₂ : ℝ) :
    energy c ES EI GS (opt c n₁ n₂) / c.area =
      compliance11 c ES EI GS * (n₁ ^ 2 + n₂ ^ 2) / 2 := by
  have hA := c.area_pos.ne'
  simp only [energy, axialEnergy, bendEnergy, compliance11, m₃, m₂, m₁, partner, opt]
  field_simp
  ring

/-- Differences of forces. -/
def Forces.sub (f g : Forces) : Forces := ⟨f.f₀ - g.f₀, f.f₁ - g.f₁, f.f₂ - g.f₂, f.f₃ - g.f₃⟩

theorem kernel {D : Forces} (h1 : Forces.sum D = 0) (h2 : c.m₃ D = 0) (h3 : c.m₃ (partner D) = 0) :
    ∃ t, D = fourPoint t := by
  refine (c.admissible_iff D).1 ⟨⟨h1, h2⟩, ⟨?_, h3⟩⟩
  simp only [Forces.sum] at h1
  simp only [partner]
  linarith

/-- **Minimum complementary energy**: among admissible in-plane fields with prescribed `N₁₁, N₂₂`,
the optimal field has the least energy. [Greco2013], App. 8. -/
theorem energy_opt_le {ES EI GS : ℝ} (hES : 0 < ES) (hEI : 0 < EI) (hGS : 0 < GS) {F : InPlane}
    (hF : Admissible c F) :
    energy c ES EI GS (opt c (N11 c F) (N22 c F)) ≤ energy c ES EI GS F := by
  have hA := c.area_pos.ne'
  set n₁ := N11 c F
  set n₂ := N22 c F
  obtain ⟨hFo, h11, h22⟩ := admissible_opt (c := c) n₁ n₂
  obtain ⟨hXs, hXm, hYs, hYm⟩ := hF
  obtain ⟨hoXs, hoXm, hoYs, hoYm⟩ := hFo
  -- the differences lie in the one-dimensional kernel
  have hm3X : c.m₃ F.X = c.m₃ (opt c n₁ n₂).X := by
    rw [m3_optX]; simp only [n₁, N11]; field_simp
  have hm3Y : c.m₃ (partner F.Y) = c.m₃ (partner (opt c n₁ n₂).Y) := by
    rw [m3_optY]; simp only [n₂, N22]; field_simp
  obtain ⟨t, ht⟩ := kernel (c := c) (D := Forces.sub F.X (opt c n₁ n₂).X)
    (by simp only [Forces.sum, Forces.sub] at hXs hoXs ⊢; linarith)
    (by simp only [m₃, m₂, m₁, Forces.sub] at hm3X ⊢; linarith)
    (by simp only [m₃, m₂, m₁, partner, Forces.sub] at hXm hoXm ⊢; linarith)
  obtain ⟨u, hu⟩ := kernel (c := c) (D := Forces.sub F.Y (opt c n₁ n₂).Y)
    (by simp only [Forces.sum, Forces.sub] at hYs hoYs ⊢; linarith)
    (by simp only [m₃, m₂, m₁, Forces.sub] at hYm hoYm ⊢; linarith)
    (by simp only [m₃, m₂, m₁, partner, Forces.sub] at hm3Y ⊢; linarith)
  -- write `F = opt + (four-point fields)` and expand the energy
  obtain ⟨⟨x₀, x₁, x₂, x₃⟩, ⟨y₀, y₁, y₂, y₃⟩⟩ := F
  simp only [Forces.sub, fourPoint, Forces.mk.injEq] at ht hu
  have ex : (⟨x₀, x₁, x₂, x₃⟩ : Forces) = ⟨(opt c n₁ n₂).X.f₀ + t, (opt c n₁ n₂).X.f₁ - t,
      (opt c n₁ n₂).X.f₂ - t, (opt c n₁ n₂).X.f₃ + t⟩ := by
    rw [Forces.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
  have ey : (⟨y₀, y₁, y₂, y₃⟩ : Forces) = ⟨(opt c n₁ n₂).Y.f₀ + u, (opt c n₁ n₂).Y.f₁ - u,
      (opt c n₁ n₂).Y.f₂ - u, (opt c n₁ n₂).Y.f₃ + u⟩ := by
    rw [Forces.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2]
  have key : energy c ES EI GS ⟨⟨x₀, x₁, x₂, x₃⟩, ⟨y₀, y₁, y₂, y₃⟩⟩ =
      energy c ES EI GS (opt c n₁ n₂) +
        c.a * (t ^ 2 + u ^ 2) * (6 * EI * ES + 6 * EI * GS + 2 * ES * GS * c.a ^ 2 +
          3 * ES * GS * c.a * c.b) / (6 * EI * ES * GS) := by
    rw [ex, ey]
    simp only [energy, axialEnergy, bendEnergy, m₃, m₂, m₁, partner, opt]
    field_simp
    ring
  rw [key]
  have := c.a_pos
  have := c.b_nonneg
  have : 0 ≤ c.a * (t ^ 2 + u ^ 2) * (6 * EI * ES + 6 * EI * GS + 2 * ES * GS * c.a ^ 2 +
      3 * ES * GS * c.a * c.b) / (6 * EI * ES * GS) := by positivity
  linarith

end InPlane

end Cell

end ContinuumMechanics.Nexorade

end
