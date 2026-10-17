import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# High-cycle fatigue and fatigue crack growth

Stress-life (S–N) fatigue and linear-elastic fatigue crack growth. The empirical laws are
definitions; the theorems are their mathematical consequences
([Suresh1998], ch. 7–9; [Dowling2013], ch. 9–11; [Stephens2001], ch. 4–6).

* **Basquin's law** `σ_a = σ_f' (2N)^b` with `b < 0`, and its inverse, the life
  `N(σ_a) = ½ (σ_a / σ_f')^{1/b}`.
* **Palmgren–Miner rule**: damage `D = Σᵢ nᵢ / Nᵢ`, failure iff `D ≥ 1`.
* **Mean-stress corrections** of Goodman, Gerber and Soderberg.
* **Paris law** `da/dN = C (ΔK)^m` with `ΔK = Y Δσ √(π a)`, and the critical crack length
  from `K_max = K_IC`.

## Main results

* `basquinAmplitude_basquinLife`, `basquinLife_basquinAmplitude`: the life inverts Basquin's
  law; `basquinLife_strictAntiOn`: `N(σ_a)` is strictly decreasing for `b < 0`;
  `log_basquinAmplitude`, `basquin_loglog_slope`: the S–N curve is a line of slope `b` in
  log–log coordinates.
* `minerDamage_union`, `minerDamage_add`: additivity of damage over load blocks;
  `sequenceDamage_perm`, `sequenceDamage_swap`: independence of the load sequence (the known
  limitation of Miner's rule); `minerDamage_mono`, `minerDamage_update_lt`: monotonicity.
* `sequenceDamage_replicate`, `minerFails_mul_iff`, `minerFails_basquin_iff`: a block of damage
  `D` repeated `k` times fails iff `k ≥ 1 / D`; `minerDamage_basquin`:
  `D = 2 Σ nᵢ (σᵢ / σ_f')^{-1/b}`.
* `basquinLife_equivalentAmplitude`, `damage_equivalentAmplitude`, `equivalentAmplitude_eq`:
  the equivalent constant amplitude `σ_eq = σ_f' (Σ nᵢ (σᵢ/σ_f')^{-1/b} / Σ nᵢ)^{-b}` has
  life `Σ nᵢ / D`.
* `meanStress_ranking`: for `0 ≤ σ_m < σ_u`, `0 < σ_y ≤ σ_u`, the allowable amplitudes satisfy
  Soderberg ≤ Goodman ≤ Gerber; `equivalent_ranking`: the reverse order for the equivalent
  fully reversed amplitudes.
* `paris_cycles_eq`: if `a(N) > 0` solves the Paris ODE on `[0, T]`, then `T` equals the
  closed-form Paris life from `a(0)` to `a(T)` (cases `m ≠ 2` and `m = 2`);
  `parisLife_strictMonoOn`, `parisLife_pos`: the life is increasing in `a_f` and positive.
* `stressIntensity_criticalCrackLength`, `stressIntensity_lt_iff`: `a_c = (K_IC/(Y σ_max))² / π`
  is exactly where `K_max = K_IC`, and `K_max < K_IC ↔ a < a_c`.

## References

* [Suresh1998] S. Suresh, *Fatigue of Materials*, 2nd ed., ch. 7–9.
* [Dowling2013] N. E. Dowling, *Mechanical Behavior of Materials*, 4th ed., ch. 9–11.
* [Stephens2001] R. I. Stephens, A. Fatemi, R. R. Stephens, H. O. Fuchs, *Metal Fatigue in
  Engineering*, 2nd ed., ch. 4–6.
* [Paris1963] P. Paris, F. Erdogan, *A critical analysis of crack propagation laws*,
  J. Basic Eng. 85 (1963) 528–534.
-/

open Real Set Finset

noncomputable section

namespace ContinuumMechanics

namespace Fatigue

/-! ### Basquin's law -/

/-- **Basquin's law**: the stress amplitude `σ_a = σ_f' (2N)^b` sustained for `N` cycles,
with fatigue strength coefficient `σ_f' > 0` and fatigue strength exponent `b < 0`. -/
def basquinAmplitude (σf b N : ℝ) : ℝ := σf * (2 * N) ^ b

/-- The **Basquin life**: the number of cycles to failure `N(σ_a) = ½ (σ_a / σ_f')^{1/b}`
at stress amplitude `σ_a`, the inverse of `basquinAmplitude`. -/
def basquinLife (σf b σa : ℝ) : ℝ := (σa / σf) ^ b⁻¹ / 2

/-- The Basquin life is positive for positive amplitudes. -/
theorem basquinLife_pos {σf b σa : ℝ} (hσf : 0 < σf) (hσa : 0 < σa) :
    0 < basquinLife σf b σa := by
  unfold basquinLife; positivity

/-- The Basquin life inverts Basquin's law: `σ_f' (2 N(σ_a))^b = σ_a`. -/
theorem basquinAmplitude_basquinLife {σf b σa : ℝ} (hσf : 0 < σf) (hb : b ≠ 0)
    (hσa : 0 < σa) : basquinAmplitude σf b (basquinLife σf b σa) = σa := by
  unfold basquinAmplitude basquinLife
  rw [mul_div_cancel₀ _ two_ne_zero, rpow_inv_rpow (by positivity) hb]
  field_simp

/-- Basquin's law inverts the Basquin life: `N(σ_f' (2N)^b) = N` for `N > 0`. -/
theorem basquinLife_basquinAmplitude {σf b N : ℝ} (hσf : 0 < σf) (hb : b ≠ 0)
    (hN : 0 < N) : basquinLife σf b (basquinAmplitude σf b N) = N := by
  unfold basquinAmplitude basquinLife
  rw [mul_div_cancel_left₀ _ hσf.ne', rpow_rpow_inv (by positivity) hb]
  ring

/-- **The S–N curve is decreasing**: for `b < 0` the Basquin life is strictly decreasing in
the stress amplitude `σ_a > 0`. -/
theorem basquinLife_strictAntiOn {σf b : ℝ} (hσf : 0 < σf) (hb : b < 0) :
    StrictAntiOn (basquinLife σf b) (Ioi 0) := by
  intro x hx y _ hxy
  unfold basquinLife
  have h := rpow_lt_rpow_of_neg (div_pos hx hσf) (div_lt_div_of_pos_right hxy hσf)
    (inv_lt_zero.mpr hb)
  linarith

/-- **Log-linearity of the S–N curve**: `log σ_a = log σ_f' + b log 2 + b log N`, i.e.
`log σ_a` is an affine function of `log N` with slope `b`. -/
theorem log_basquinAmplitude {σf b N : ℝ} (hσf : 0 < σf) (hN : 0 < N) :
    log (basquinAmplitude σf b N) = log σf + b * log 2 + b * log N := by
  unfold basquinAmplitude
  rw [log_mul hσf.ne' (rpow_pos_of_pos (by positivity) b).ne', log_rpow (by positivity),
    log_mul two_ne_zero hN.ne']
  ring

/-- The slope of the S–N line in log–log coordinates between two lives is the Basquin
exponent `b`. -/
theorem basquin_loglog_slope {σf b N₁ N₂ : ℝ} (hσf : 0 < σf) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hne : N₁ ≠ N₂) :
    (log (basquinAmplitude σf b N₂) - log (basquinAmplitude σf b N₁)) /
      (log N₂ - log N₁) = b := by
  rw [log_basquinAmplitude hσf hN₁, log_basquinAmplitude hσf hN₂]
  have : log N₂ - log N₁ ≠ 0 := by
    intro h
    exact hne (log_injOn_pos hN₁ hN₂ (by linarith))
  field_simp
  ring

/-! ### Palmgren–Miner linear damage rule -/

section Miner

variable {ι : Type*}

/-- **Palmgren–Miner damage** of a load spectrum over a finite set `s` of load levels:
`D = Σᵢ nᵢ / Nᵢ`, where `nᵢ` cycles are applied at level `i`, whose constant-amplitude life
is `Nᵢ`. -/
def minerDamage (s : Finset ι) (n N : ι → ℝ) : ℝ := ∑ i ∈ s, n i / N i

/-- **Miner's failure criterion**: failure is predicted iff the accumulated damage `D ≥ 1`. -/
def MinerFails (D : ℝ) : Prop := 1 ≤ D

/-- Damage of a loading *sequence* of blocks `(nₖ, Nₖ)` applied one after the other. -/
def sequenceDamage (l : List (ℝ × ℝ)) : ℝ := (l.map fun p => p.1 / p.2).sum

/-- Damage is nonnegative for nonnegative cycle counts and positive lives. -/
theorem minerDamage_nonneg {s : Finset ι} {n N : ι → ℝ} (hn : ∀ i ∈ s, 0 ≤ n i)
    (hN : ∀ i ∈ s, 0 < N i) : 0 ≤ minerDamage s n N :=
  sum_nonneg fun i hi => div_nonneg (hn i hi) (hN i hi).le

/-- **Additivity over load blocks**: the damage of two disjoint groups of load levels is the
sum of their damages. -/
theorem minerDamage_union [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) (n N : ι → ℝ) :
    minerDamage (s ∪ t) n N = minerDamage s n N + minerDamage t n N :=
  sum_union h

/-- **Additivity in the cycle counts**: applying the spectra `n` and `n'` at the same levels
accumulates damage `D(n) + D(n')`. -/
theorem minerDamage_add (s : Finset ι) (n n' N : ι → ℝ) :
    minerDamage s (n + n') N = minerDamage s n N + minerDamage s n' N := by
  simp only [minerDamage, Pi.add_apply, add_div, sum_add_distrib]

/-- **Monotonicity**: applying more cycles at every level never decreases the damage. -/
theorem minerDamage_mono {s : Finset ι} {n n' N : ι → ℝ} (hN : ∀ i ∈ s, 0 < N i)
    (hn : ∀ i ∈ s, n i ≤ n' i) : minerDamage s n N ≤ minerDamage s n' N :=
  sum_le_sum fun i hi => div_le_div_of_nonneg_right (hn i hi) (hN i hi).le

/-- **Strict monotonicity in each `nᵢ`**: adding cycles at a single level `j` strictly
increases the damage. -/
theorem minerDamage_update_lt [DecidableEq ι] {s : Finset ι} {n N : ι → ℝ} {j : ι}
    (hj : j ∈ s) (hN : 0 < N j) {x : ℝ} (hx : n j < x) :
    minerDamage s n N < minerDamage s (Function.update n j x) N := by
  unfold minerDamage
  rw [← add_sum_erase s _ hj, ← add_sum_erase s _ hj, Function.update_self]
  have he : ∑ i ∈ s.erase j, Function.update n j x i / N i = ∑ i ∈ s.erase j, n i / N i :=
    sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [he]
  have := div_lt_div_of_pos_right hx hN
  linarith

/-- Damage of a concatenation of loading sequences is the sum of their damages. -/
theorem sequenceDamage_append (l₁ l₂ : List (ℝ × ℝ)) :
    sequenceDamage (l₁ ++ l₂) = sequenceDamage l₁ + sequenceDamage l₂ := by
  simp [sequenceDamage]

/-- **Load-sequence independence** (the known limitation of Miner's rule): reordering the
blocks of a loading sequence does not change the predicted damage, so high–low and low–high
sequences are predicted to be equally damaging. -/
theorem sequenceDamage_perm {l₁ l₂ : List (ℝ × ℝ)} (h : l₁.Perm l₂) :
    sequenceDamage l₁ = sequenceDamage l₂ :=
  (h.map _).sum_eq

/-- In particular high–low and low–high two-block sequences give the same damage. -/
theorem sequenceDamage_swap (p q : ℝ × ℝ) : sequenceDamage [p, q] = sequenceDamage [q, p] :=
  sequenceDamage_perm (List.Perm.swap q p [])

/-- Repeating a loading sequence `k` times multiplies its damage by `k`. -/
theorem sequenceDamage_replicate (k : ℕ) (l : List (ℝ × ℝ)) :
    sequenceDamage (List.replicate k l).flatten = k * sequenceDamage l := by
  induction k with
  | zero => simp [sequenceDamage]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, sequenceDamage_append, ih]
    push_cast
    ring

/-- The damage of the spectrum `n` applied `k` times is `k D`. -/
theorem minerDamage_smul (s : Finset ι) (k : ℝ) (n N : ι → ℝ) :
    minerDamage s (k • n) N = k * minerDamage s n N := by
  simp only [minerDamage, Pi.smul_apply, smul_eq_mul, mul_div_assoc, mul_sum]

/-- The number of repetitions of a load block of damage `D` to failure: `k* = 1 / D`. -/
def blocksToFailure (D : ℝ) : ℝ := 1 / D

/-- After `k* = 1 / D` repetitions of a block of damage `D > 0` the damage is exactly `1`. -/
theorem blocksToFailure_mul {D : ℝ} (hD : 0 < D) : blocksToFailure D * D = 1 := by
  unfold blocksToFailure; field_simp

/-- **Life under repeated blocks**: repeating a block of damage `D > 0` `k` times predicts
failure iff `k ≥ k* = 1 / D`. -/
theorem minerFails_mul_iff {D : ℝ} (hD : 0 < D) (k : ℝ) :
    MinerFails (k * D) ↔ blocksToFailure D ≤ k := by
  unfold MinerFails blocksToFailure
  rw [div_le_iff₀ hD]

/-- **Life under repeated blocks with Basquin lives**: repeating the spectrum `n` at
amplitudes `σ` (lives from Basquin's law) `k` times predicts failure iff `k ≥ 1 / D_block`. -/
theorem minerFails_basquin_iff {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ}
    (hD : 0 < minerDamage s n (fun i => basquinLife σf b (σ i))) (k : ℝ) :
    MinerFails (minerDamage s (k • n) (fun i => basquinLife σf b (σ i))) ↔
      blocksToFailure (minerDamage s n (fun i => basquinLife σf b (σ i))) ≤ k := by
  rw [minerDamage_smul]
  exact minerFails_mul_iff hD k

/-- The damage per cycle at amplitude `σ_a` under Basquin's law:
`1 / N(σ_a) = 2 (σ_a / σ_f')^{-1/b}`. -/
theorem div_basquinLife {σf b σa : ℝ} (hσf : 0 < σf) (hσa : 0 < σa) (x : ℝ) :
    x / basquinLife σf b σa = 2 * x * (σa / σf) ^ (-b⁻¹) := by
  have hp : 0 < (σa / σf) ^ b⁻¹ := by positivity
  unfold basquinLife
  rw [rpow_neg (by positivity)]
  field_simp

/-- **Miner damage with Basquin lives**: `D = 2 Σᵢ nᵢ (σᵢ / σ_f')^{-1/b}`. -/
theorem minerDamage_basquin {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ} (hσf : 0 < σf)
    (hσ : ∀ i ∈ s, 0 < σ i) :
    minerDamage s n (fun i => basquinLife σf b (σ i)) =
      2 * ∑ i ∈ s, n i * (σ i / σf) ^ (-b⁻¹) := by
  unfold minerDamage
  rw [mul_sum]
  exact sum_congr rfl fun i hi => by rw [div_basquinLife hσf (hσ i hi), mul_assoc]

/-- The **equivalent constant amplitude** `σ_eq` of a spectrum: the amplitude whose Basquin
life equals `Σ nᵢ / D`, so that `Σ nᵢ` cycles at `σ_eq` produce the same damage `D`. -/
def equivalentAmplitude (s : Finset ι) (n σ : ι → ℝ) (σf b : ℝ) : ℝ :=
  basquinAmplitude σf b ((∑ i ∈ s, n i) / minerDamage s n (fun i => basquinLife σf b (σ i)))

/-- The damage is positive for a nonempty spectrum of positive cycle counts and amplitudes. -/
theorem minerDamage_basquin_pos {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ} (hσf : 0 < σf)
    (hs : s.Nonempty) (hn : ∀ i ∈ s, 0 < n i) (hσ : ∀ i ∈ s, 0 < σ i) :
    0 < minerDamage s n (fun i => basquinLife σf b (σ i)) :=
  sum_pos (fun i hi => div_pos (hn i hi) (basquinLife_pos hσf (hσ i hi))) hs

/-- **Existence of the equivalent amplitude**: the Basquin life at `σ_eq` is `Σ nᵢ / D`. -/
theorem basquinLife_equivalentAmplitude {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ}
    (hσf : 0 < σf) (hb : b ≠ 0) (hs : s.Nonempty) (hn : ∀ i ∈ s, 0 < n i)
    (hσ : ∀ i ∈ s, 0 < σ i) :
    basquinLife σf b (equivalentAmplitude s n σ σf b) =
      (∑ i ∈ s, n i) / minerDamage s n (fun i => basquinLife σf b (σ i)) :=
  basquinLife_basquinAmplitude hσf hb
    (div_pos (sum_pos hn hs) (minerDamage_basquin_pos hσf hs hn hσ))

/-- **Damage equivalence**: `Σ nᵢ` cycles at the equivalent amplitude produce the damage `D`
of the original spectrum. -/
theorem damage_equivalentAmplitude {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ}
    (hσf : 0 < σf) (hb : b ≠ 0) (hs : s.Nonempty) (hn : ∀ i ∈ s, 0 < n i)
    (hσ : ∀ i ∈ s, 0 < σ i) :
    (∑ i ∈ s, n i) / basquinLife σf b (equivalentAmplitude s n σ σf b) =
      minerDamage s n (fun i => basquinLife σf b (σ i)) := by
  rw [basquinLife_equivalentAmplitude hσf hb hs hn hσ,
    div_div_cancel₀ (sum_pos hn hs).ne']

/-- **Explicit equivalent amplitude**:
`σ_eq = σ_f' (Σᵢ nᵢ (σᵢ / σ_f')^{-1/b} / Σᵢ nᵢ)^{-b}`, a weighted power mean of the
amplitudes with exponent `-1/b`. -/
theorem equivalentAmplitude_eq {s : Finset ι} {n σ : ι → ℝ} {σf b : ℝ}
    (hσf : 0 < σf) (hs : s.Nonempty) (hn : ∀ i ∈ s, 0 < n i) (hσ : ∀ i ∈ s, 0 < σ i) :
    equivalentAmplitude s n σ σf b =
      σf * ((∑ i ∈ s, n i * (σ i / σf) ^ (-b⁻¹)) / ∑ i ∈ s, n i) ^ (-b) := by
  have hT : 0 < ∑ i ∈ s, n i := sum_pos hn hs
  have hS : 0 < ∑ i ∈ s, n i * (σ i / σf) ^ (-b⁻¹) :=
    sum_pos (fun i hi => mul_pos (hn i hi) (by have := hσ i hi; positivity)) hs
  unfold equivalentAmplitude basquinAmplitude
  rw [minerDamage_basquin hσf hσ, rpow_neg (by positivity), ← inv_rpow (by positivity),
    inv_div]
  congr 2
  field_simp

end Miner

/-! ### Mean-stress corrections -/

section MeanStress

/-- **Goodman** allowable alternating amplitude at mean stress `σ_m`, endurance limit `σ_e`
and ultimate strength `σ_u`: `σ_a = σ_e (1 - σ_m / σ_u)`. -/
def goodmanAmplitude (σe σu σm : ℝ) : ℝ := σe * (1 - σm / σu)

/-- **Gerber** allowable alternating amplitude: `σ_a = σ_e (1 - (σ_m / σ_u)²)`. -/
def gerberAmplitude (σe σu σm : ℝ) : ℝ := σe * (1 - (σm / σu) ^ 2)

/-- **Soderberg** allowable alternating amplitude with yield strength `σ_y`:
`σ_a = σ_e (1 - σ_m / σ_y)`. -/
def soderbergAmplitude (σe σy σm : ℝ) : ℝ := σe * (1 - σm / σy)

/-- **Goodman equivalent fully reversed amplitude** `σ_ar = σ_a / (1 - σ_m / σ_u)`. -/
def goodmanEquivalent (σu σa σm : ℝ) : ℝ := σa / (1 - σm / σu)

/-- **Gerber equivalent fully reversed amplitude** `σ_ar = σ_a / (1 - (σ_m / σ_u)²)`. -/
def gerberEquivalent (σu σa σm : ℝ) : ℝ := σa / (1 - (σm / σu) ^ 2)

/-- **Soderberg equivalent fully reversed amplitude** `σ_ar = σ_a / (1 - σ_m / σ_y)`. -/
def soderbergEquivalent (σy σa σm : ℝ) : ℝ := σa / (1 - σm / σy)

/-- The Goodman amplitude lies on the Goodman line `σ_a / σ_e + σ_m / σ_u = 1`. -/
theorem goodman_line {σe σu : ℝ} (hσe : σe ≠ 0) (σm : ℝ) :
    goodmanAmplitude σe σu σm / σe + σm / σu = 1 := by
  unfold goodmanAmplitude; field_simp; ring

/-- The Gerber amplitude lies on the Gerber parabola `σ_a / σ_e + (σ_m / σ_u)² = 1`. -/
theorem gerber_parabola {σe σu : ℝ} (hσe : σe ≠ 0) (σm : ℝ) :
    gerberAmplitude σe σu σm / σe + (σm / σu) ^ 2 = 1 := by
  unfold gerberAmplitude; field_simp; ring

/-- The Soderberg amplitude lies on the Soderberg line `σ_a / σ_e + σ_m / σ_y = 1`. -/
theorem soderberg_line {σe σy : ℝ} (hσe : σe ≠ 0) (σm : ℝ) :
    soderbergAmplitude σe σy σm / σe + σm / σy = 1 := by
  unfold soderbergAmplitude; field_simp; ring

/-- On the Goodman line the equivalent fully reversed amplitude is the endurance limit. -/
theorem goodmanEquivalent_goodmanAmplitude {σe σu σm : ℝ} (hσm : σm ≠ σu) (hσu : σu ≠ 0) :
    goodmanEquivalent σu (goodmanAmplitude σe σu σm) σm = σe := by
  have : 1 - σm / σu ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq hσu]; exact hσm
  unfold goodmanEquivalent goodmanAmplitude; field_simp

/-- On the Gerber parabola the equivalent fully reversed amplitude is the endurance limit. -/
theorem gerberEquivalent_gerberAmplitude {σe σu σm : ℝ} (h : (σm / σu) ^ 2 ≠ 1) :
    gerberEquivalent σu (gerberAmplitude σe σu σm) σm = σe := by
  have : 1 - (σm / σu) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold gerberEquivalent gerberAmplitude
  rw [mul_div_assoc, div_self this, mul_one]

/-- On the Soderberg line the equivalent fully reversed amplitude is the endurance limit. -/
theorem soderbergEquivalent_soderbergAmplitude {σe σy σm : ℝ} (hσm : σm ≠ σy)
    (hσy : σy ≠ 0) : soderbergEquivalent σy (soderbergAmplitude σe σy σm) σm = σe := by
  have : 1 - σm / σy ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq hσy]; exact hσm
  unfold soderbergEquivalent soderbergAmplitude; field_simp

/-- **Gerber is less conservative than Goodman**: for `0 ≤ σ_m < σ_u` the Gerber allowable
amplitude is at least the Goodman one. -/
theorem goodmanAmplitude_le_gerberAmplitude {σe σu σm : ℝ} (hσe : 0 ≤ σe) (hm : 0 ≤ σm)
    (hmu : σm < σu) : goodmanAmplitude σe σu σm ≤ gerberAmplitude σe σu σm := by
  have hu : 0 < σu := hm.trans_lt hmu
  have h0 : 0 ≤ σm / σu := div_nonneg hm hu.le
  have h1 : σm / σu ≤ 1 := (div_le_one hu).mpr hmu.le
  unfold goodmanAmplitude gerberAmplitude
  apply mul_le_mul_of_nonneg_left _ hσe
  nlinarith

/-- **Goodman is less conservative than Soderberg**: for `0 ≤ σ_m` and `0 < σ_y ≤ σ_u` the
Goodman allowable amplitude is at least the Soderberg one. -/
theorem soderbergAmplitude_le_goodmanAmplitude {σe σy σu σm : ℝ} (hσe : 0 ≤ σe)
    (hm : 0 ≤ σm) (hy : 0 < σy) (hyu : σy ≤ σu) :
    soderbergAmplitude σe σy σm ≤ goodmanAmplitude σe σu σm := by
  unfold goodmanAmplitude soderbergAmplitude
  apply mul_le_mul_of_nonneg_left _ hσe
  have := div_le_div_of_nonneg_left hm hy hyu
  linarith

/-- **Conservatism ranking** of the classical mean-stress criteria: for `0 ≤ σ_m < σ_u` and
`0 < σ_y ≤ σ_u`, Soderberg ≤ Goodman ≤ Gerber for the allowable amplitude. -/
theorem meanStress_ranking {σe σy σu σm : ℝ} (hσe : 0 ≤ σe) (hm : 0 ≤ σm) (hmu : σm < σu)
    (hy : 0 < σy) (hyu : σy ≤ σu) :
    soderbergAmplitude σe σy σm ≤ goodmanAmplitude σe σu σm ∧
      goodmanAmplitude σe σu σm ≤ gerberAmplitude σe σu σm :=
  ⟨soderbergAmplitude_le_goodmanAmplitude hσe hm hy hyu,
    goodmanAmplitude_le_gerberAmplitude hσe hm hmu⟩

/-- **Ranking of equivalent amplitudes**: for `σ_a ≥ 0`, `0 ≤ σ_m < σ_y ≤ σ_u`, the equivalent
fully reversed amplitudes satisfy Gerber ≤ Goodman ≤ Soderberg. -/
theorem equivalent_ranking {σa σy σu σm : ℝ} (ha : 0 ≤ σa) (hm : 0 ≤ σm) (hmy : σm < σy)
    (hyu : σy ≤ σu) :
    gerberEquivalent σu σa σm ≤ goodmanEquivalent σu σa σm ∧
      goodmanEquivalent σu σa σm ≤ soderbergEquivalent σy σa σm := by
  have hy : 0 < σy := hm.trans_lt hmy
  have hu : 0 < σu := hy.trans_le hyu
  have hmu : σm < σu := hmy.trans_le hyu
  have h0 : 0 ≤ σm / σu := div_nonneg hm hu.le
  have h1 : σm / σu < 1 := (div_lt_one hu).mpr hmu
  have h2 : σm / σy < 1 := (div_lt_one hy).mpr hmy
  have h3 : σm / σu ≤ σm / σy := div_le_div_of_nonneg_left hm hy hyu
  unfold gerberEquivalent goodmanEquivalent soderbergEquivalent
  constructor
  · exact div_le_div_of_nonneg_left ha (by linarith) (by nlinarith)
  · exact div_le_div_of_nonneg_left ha (by linarith) (by linarith)

end MeanStress

/-! ### Paris law of fatigue crack growth -/

section Paris

/-- The **stress intensity factor range** `ΔK = Y Δσ √(π a)` of a crack of length `a` under
stress range `Δσ` with constant geometry factor `Y`. -/
def stressIntensityRange (Y Δσ a : ℝ) : ℝ := Y * Δσ * √(π * a)

/-- The **Paris law** crack growth rate `da/dN = C (ΔK)^m`. -/
def parisRate (C m Y Δσ a : ℝ) : ℝ := C * stressIntensityRange Y Δσ a ^ m

/-- The **Paris life**: the number of cycles to grow a crack from `a₀` to `a_f`,
`N_f = (a_f^{1-m/2} - a₀^{1-m/2}) / (C (Y Δσ √π)^m (1 - m/2))` for `m ≠ 2` and
`N_f = ln(a_f / a₀) / (C (Y Δσ)² π)` for `m = 2`. -/
def parisLife (C m Y Δσ a₀ af : ℝ) : ℝ :=
  if m = 2 then log (af / a₀) / (C * (Y * Δσ) ^ 2 * π)
  else (af ^ (1 - m / 2) - a₀ ^ (1 - m / 2)) / (C * (Y * Δσ * √π) ^ m * (1 - m / 2))

/-- The Paris life for `m ≠ 2`. -/
theorem parisLife_of_ne {C m Y Δσ a₀ af : ℝ} (hm : m ≠ 2) :
    parisLife C m Y Δσ a₀ af =
      (af ^ (1 - m / 2) - a₀ ^ (1 - m / 2)) / (C * (Y * Δσ * √π) ^ m * (1 - m / 2)) :=
  ite_eq_right_of_eq_false _ _ (eq_false hm)

/-- The Paris life for `m = 2`. -/
theorem parisLife_two (C Y Δσ a₀ af : ℝ) :
    parisLife C 2 Y Δσ a₀ af = log (af / a₀) / (C * (Y * Δσ) ^ 2 * π) :=
  ite_eq_left_of_eq_true _ _ (eq_true rfl)

/-- The Paris rate separates as `C (Y Δσ √π)^m a^{m/2}`. -/
theorem parisRate_eq {C m Y Δσ a : ℝ} (hY : 0 ≤ Y * Δσ) (ha : 0 ≤ a) :
    parisRate C m Y Δσ a = C * (Y * Δσ * √π) ^ m * a ^ (m / 2) := by
  unfold parisRate stressIntensityRange
  rw [sqrt_mul pi_pos.le, ← mul_assoc, mul_rpow (by positivity) (sqrt_nonneg a),
    sqrt_eq_rpow a, ← rpow_mul ha]
  ring_nf

/-- The constant `(Y Δσ √π)^2 = (Y Δσ)² π`. -/
theorem rpow_two_geom (Y Δσ : ℝ) : (Y * Δσ * √π) ^ (2 : ℝ) = (Y * Δσ) ^ 2 * π := by
  rw [rpow_two, mul_pow, sq_sqrt pi_pos.le]

/-- A function with constant derivative `c` on `[0, T]` satisfies `f T - f 0 = c T`. -/
theorem sub_eq_mul_of_hasDerivAt {f : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ N ∈ Icc 0 T, HasDerivAt f c N) : f T - f 0 = c * T := by
  have hg : ∀ N ∈ Icc 0 T, HasDerivAt (fun N => f N - c * N) 0 N := fun N hN => by
    have h := (hf N hN).sub ((hasDerivAt_id' N).const_mul c)
    simp only [mul_one, sub_self] at h
    exact h
  have := constant_of_has_deriv_right_zero (f := fun N => f N - c * N)
    (fun N hN => (hg N hN).continuousAt.continuousWithinAt)
    (fun N hN => (hg N (Ico_subset_Icc_self hN)).hasDerivWithinAt) T ⟨hT, le_rfl⟩
  simp only [mul_zero, sub_zero] at this
  linarith

/-- **Integration of the Paris law**: if a crack-length history `a(N) > 0` satisfies
`da/dN = C (ΔK)^m` on `[0, T]`, then the elapsed number of cycles `T` equals the Paris life
from `a(0)` to `a(T)`. -/
theorem paris_cycles_eq {C m Y Δσ T : ℝ} {a : ℝ → ℝ} (hC : 0 < C) (hY : 0 < Y)
    (hΔσ : 0 < Δσ) (hT : 0 ≤ T) (hpos : ∀ N ∈ Icc 0 T, 0 < a N)
    (hode : ∀ N ∈ Icc 0 T, HasDerivAt a (parisRate C m Y Δσ (a N)) N) :
    T = parisLife C m Y Δσ (a 0) (a T) := by
  have hYΔ : 0 < Y * Δσ := mul_pos hY hΔσ
  set K := (Y * Δσ * √π) ^ m with hK
  have hKpos : 0 < K := by positivity
  have hrate : ∀ N ∈ Icc 0 T, parisRate C m Y Δσ (a N) = C * K * a N ^ (m / 2) :=
    fun N hN => parisRate_eq hYΔ.le (hpos N hN).le
  have ha0 := hpos 0 ⟨le_rfl, hT⟩
  have haT := hpos T ⟨hT, le_rfl⟩
  by_cases hm : m = 2
  · subst hm
    rw [parisLife_two, show C * (Y * Δσ) ^ 2 * π = C * K by rw [hK, rpow_two_geom]; ring]
    have hd : ∀ N ∈ Icc 0 T, HasDerivAt (fun N => log (a N)) (C * K) N := fun N hN => by
      have h := (hode N hN).log (hpos N hN).ne'
      rw [hrate N hN, show (2 : ℝ) / 2 = 1 by norm_num, rpow_one] at h
      convert h using 1
      field_simp [(hpos N hN).ne']
    have := sub_eq_mul_of_hasDerivAt hT hd
    rw [log_div haT.ne' ha0.ne', this]
    field_simp
  · rw [parisLife_of_ne hm, ← hK]
    have hp : 1 - m / 2 ≠ 0 := by
      intro h; apply hm; linarith
    have hd : ∀ N ∈ Icc 0 T,
        HasDerivAt (fun N => a N ^ (1 - m / 2)) (C * K * (1 - m / 2)) N := fun N hN => by
      have h := (hode N hN).rpow_const (p := 1 - m / 2) (Or.inl (hpos N hN).ne')
      convert h using 1
      rw [hrate N hN]
      have hx : a N ^ (m / 2) * a N ^ (1 - m / 2 - 1) = 1 := by
        rw [← rpow_add (hpos N hN), show m / 2 + (1 - m / 2 - 1) = 0 by ring, rpow_zero]
      linear_combination (-(C * K * (1 - m / 2))) * hx
    rw [sub_eq_mul_of_hasDerivAt hT hd]
    field_simp

/-- The Paris life from `a₀` to itself is zero. -/
theorem parisLife_self (C m Y Δσ a₀ : ℝ) (ha₀ : 0 < a₀) : parisLife C m Y Δσ a₀ a₀ = 0 := by
  by_cases hm : m = 2
  · subst hm; rw [parisLife_two, div_self ha₀.ne', log_one, zero_div]
  · rw [parisLife_of_ne hm, sub_self, zero_div]

/-- **Monotonicity of the Paris life**: `N_f` is strictly increasing in the final crack
length `a_f > 0`. -/
theorem parisLife_strictMonoOn {C m Y Δσ a₀ : ℝ} (hC : 0 < C) (hY : 0 < Y) (hΔσ : 0 < Δσ)
    (ha₀ : 0 < a₀) : StrictMonoOn (parisLife C m Y Δσ a₀) (Ioi 0) := by
  intro x hx y _ hxy
  have hx : 0 < x := hx
  have hK : 0 < (Y * Δσ * √π) ^ m := by
    have : 0 < Y * Δσ * √π := by have := sqrt_pos.mpr pi_pos; positivity
    positivity
  by_cases hm : m = 2
  · subst hm
    simp only [parisLife_two]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact log_lt_log (div_pos hx ha₀) (div_lt_div_of_pos_right hxy ha₀)
  · simp only [parisLife_of_ne hm]
    rcases lt_or_gt_of_ne (show 1 - m / 2 ≠ 0 by intro h; apply hm; linarith) with hp | hp
    · have hden : C * (Y * Δσ * √π) ^ m * (1 - m / 2) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hC hK) hp
      rw [div_lt_div_right_of_neg hden]
      have := rpow_lt_rpow_of_neg hx hxy hp
      linarith
    · have hden : 0 < C * (Y * Δσ * √π) ^ m * (1 - m / 2) := by positivity
      apply div_lt_div_of_pos_right _ hden
      have := rpow_lt_rpow hx.le hxy hp
      linarith

/-- **Positivity of the Paris life**: growing a crack from `a₀ > 0` to `a_f > a₀` takes a
positive number of cycles. -/
theorem parisLife_pos {C m Y Δσ a₀ af : ℝ} (hC : 0 < C) (hY : 0 < Y) (hΔσ : 0 < Δσ)
    (ha₀ : 0 < a₀) (h : a₀ < af) : 0 < parisLife C m Y Δσ a₀ af := by
  rw [← parisLife_self C m Y Δσ a₀ ha₀]
  exact parisLife_strictMonoOn hC hY hΔσ ha₀ ha₀ (ha₀.trans h) h

/-- The **critical crack length** `a_c = (1/π) (K_IC / (Y σ_max))²` at which the maximum
stress intensity `Y σ_max √(π a)` reaches the fracture toughness `K_IC`. -/
def criticalCrackLength (KIC Y σmax : ℝ) : ℝ := (1 / π) * (KIC / (Y * σmax)) ^ 2

/-- At the critical crack length the maximum stress intensity equals the toughness. -/
theorem stressIntensity_criticalCrackLength {KIC Y σmax : ℝ} (hK : 0 ≤ KIC) (hY : 0 < Y)
    (hσ : 0 < σmax) : stressIntensityRange Y σmax (criticalCrackLength KIC Y σmax) = KIC := by
  unfold stressIntensityRange criticalCrackLength
  rw [← mul_assoc, mul_one_div_cancel pi_pos.ne', one_mul,
    sqrt_sq (div_nonneg hK (by positivity))]
  field_simp

/-- **Fracture criterion**: for `a ≥ 0`, the maximum stress intensity stays below `K_IC` iff
the crack is shorter than the critical length. -/
theorem stressIntensity_lt_iff {KIC Y σmax a : ℝ} (hK : 0 ≤ KIC) (hY : 0 < Y)
    (hσ : 0 < σmax) (ha : 0 ≤ a) :
    stressIntensityRange Y σmax a < KIC ↔ a < criticalCrackLength KIC Y σmax := by
  conv_lhs => rw [← stressIntensity_criticalCrackLength hK hY hσ]
  unfold stressIntensityRange
  rw [mul_lt_mul_iff_right₀ (by positivity), sqrt_lt_sqrt_iff (by positivity),
    mul_lt_mul_iff_right₀ pi_pos]

end Paris

end Fatigue

end ContinuumMechanics
