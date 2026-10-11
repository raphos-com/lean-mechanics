import ContinuumMechanics.Frames.Periodic

/-!
# Square and kagome lattices

Two of the Maxwell lattices of [KaneLubensky2014], as periodic pin-jointed frames
(`ContinuumMechanics.PeriodicTruss`).

* **Square lattice** (one node, two bars per cell): `d|N| = 2 = |B|`. Its Bloch compatibility
  matrix is diagonal, `C(θ) = diag(e^{iθ₁} - 1, e^{iθ₂} - 1)`. Away from the lines
  `e^{iθ₁} = 1`, `e^{iθ₂} = 1` it has no zero mode and no self-stress
  (`square_zeroModes_eq_bot`); on the line `θ₁ = 0` the uniform horizontal motion of a row is a
  zero mode (`square_floppy_line`): the **lines of floppy modes** of the square lattice.
* **Kagome lattice** (three nodes, six bars per cell): `d|N| = 6 = |B|`, so at every wave vector
  the numbers of zero modes and of self-stresses agree, and at `θ = 0` there are at least two
  states of self-stress (`kagome_selfStresses_zero`).

The topological polarization of deformed kagome lattices, and the counting of their boundary modes
from it, are not formalized; the one-dimensional bulk–edge correspondence is
`KaneLubensky.Chain.winding_eq_one_iff_left`.

## References

* [KaneLubensky2014] C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
  lattices*, Nature Physics 10, 39–45 (2014).
-/

open Matrix

noncomputable section

namespace ContinuumMechanics.KaneLubensky

open PeriodicTruss

/-- The square lattice of unit bars. -/
def square : PeriodicTruss 2 (Fin 1) (Fin 2) where
  lattice := ![![1, 0], ![0, 1]]
  x := fun _ => 0
  src := fun _ => 0
  tgt := fun _ => 0
  shift := ![![1, 0], ![0, 1]]

theorem square_maxwell : 2 * Fintype.card (Fin 1) = Fintype.card (Fin 2) := rfl

theorem square_bar (b : Fin 2) (i : Fin 2) : square.bar b i = if b = i then 1 else 0 := by
  fin_cases b <;> fin_cases i <;> simp [square, bar, pos, Fin.sum_univ_two]

theorem square_phase (θ : Fin 2 → ℝ) (b : Fin 2) :
    phase θ (square.shift b) = Complex.exp (θ b * Complex.I) := by
  fin_cases b <;> simp [square, phase, Fin.sum_univ_two]

/-- `C(θ) u = ((e^{iθ₁} - 1) u₁, (e^{iθ₂} - 1) u₂)`. -/
theorem square_compat (θ : Fin 2 → ℝ) (u : Fin 1 × Fin 2 → ℂ) (b : Fin 2) :
    (square.compatBloch θ *ᵥ u) b = (Complex.exp (θ b * Complex.I) - 1) * u (0, b) := by
  simp only [mulVec, dotProduct, compatBloch, square_bar, Fintype.sum_prod_type,
    Fin.sum_univ_two, Finset.univ_unique, Finset.sum_singleton, square_phase]
  have hs : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim _ _
  fin_cases b <;> simp [square, hs]

/-- Away from the lines `e^{iθᵢ} = 1` the square lattice has no Bloch zero mode. -/
theorem square_zeroModes_eq_bot (θ : Fin 2 → ℝ)
    (h : ∀ b, Complex.exp (θ b * Complex.I) ≠ 1) : square.zeroModes θ = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  simp only [zeroModes, LinearMap.mem_ker, mulVecLin_apply] at hu
  rw [Submodule.mem_bot]
  funext ⟨j, i⟩
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have := congrFun hu i
  rw [square_compat, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (h i))

/-- ... and then no Bloch self-stress either (Maxwell–Calladine). -/
theorem square_selfStresses_eq_bot (θ : Fin 2 → ℝ)
    (h : ∀ b, Complex.exp (θ b * Complex.I) ≠ 1) : square.selfStresses θ = ⊥ := by
  rw [← Submodule.finrank_eq_zero, ← square.finrank_zeroModes_eq_selfStresses square_maxwell,
    square_zeroModes_eq_bot θ h, finrank_bot]

/-- **Lines of floppy modes**: on `θ₁ = 0` the uniform horizontal displacement is a zero mode. -/
theorem square_floppy_line (θ₂ : ℝ) :
    (fun p : Fin 1 × Fin 2 => if p.2 = 0 then (1 : ℂ) else 0) ∈ square.zeroModes ![0, θ₂] := by
  simp only [zeroModes, LinearMap.mem_ker, mulVecLin_apply]
  funext b
  rw [square_compat]
  fin_cases b <;> simp

/-- The kagome lattice: corner-sharing triangles, lattice `(2, 0)`, `(1, √3)`. -/
def kagome : PeriodicTruss 2 (Fin 3) (Fin 6) where
  lattice := ![![2, 0], ![1, √3]]
  x := ![![0, 0], ![1, 0], ![1 / 2, √3 / 2]]
  src := ![0, 1, 2, 1, 2, 2]
  tgt := ![1, 2, 0, 0, 0, 1]
  shift := ![0, 0, 0, ![1, 0], ![0, 1], ![-1, 1]]

theorem kagome_maxwell : 2 * Fintype.card (Fin 3) = Fintype.card (Fin 6) := rfl

/-- The kagome bars all have unit length. -/
theorem kagome_bar_length (b : Fin 6) : ∑ i, kagome.bar b i ^ 2 = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases b <;> simp [kagome, bar, pos, Fin.sum_univ_two] <;> nlinarith [h3]

/-- In the kagome lattice zero modes and self-stresses are equinumerous at every wave vector. -/
theorem kagome_zeroModes_eq_selfStresses (θ : Fin 2 → ℝ) :
    Module.finrank ℂ (kagome.zeroModes θ) = Module.finrank ℂ (kagome.selfStresses θ) :=
  kagome.finrank_zeroModes_eq_selfStresses kagome_maxwell θ

/-- At `θ = 0` the kagome lattice has at least two states of self-stress. -/
theorem kagome_selfStresses_zero : 2 ≤ Module.finrank ℂ (kagome.selfStresses 0) :=
  kagome.le_finrank_selfStresses_zero kagome_maxwell

end ContinuumMechanics.KaneLubensky
