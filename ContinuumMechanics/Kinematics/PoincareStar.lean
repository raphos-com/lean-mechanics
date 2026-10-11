import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Poincaré lemma for 1-forms on star-shaped open sets

Mathlib proves the Poincaré lemma for closed 1-forms on convex sets
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`). Here we extend it to open sets that are
star-shaped with respect to a point `c` (`StarConvex ℝ c s`).

The primitive is the curve integral `f x = ∫ᶜ y in Path.segment c x, ω y` along the ray from the
center. To differentiate it at `x ∈ s`, pick a ball `B ⊆ s` around `x`; the cone
`StarConvex.cone c B` (the union of the segments from `c` to points of `B`) is convex, lies in
`s` by star-convexity, and is a neighbourhood of `x`. Mathlib's convex-case lemma
`Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric` applied to this
cone shows that `f` has derivative `ω x` at `x`.

## Main results

* `StarConvex.convex_cone`: the cone from a point over a convex set is convex.
* `StarConvex.cone_subset`: the cone over a subset of a star-shaped set stays in it.
* `StarConvex.hasFDerivAt_curveIntegral_segment_of_fderiv_symmetric`: the radial curve integral
  of a closed 1-form is a primitive.
* `StarConvex.exists_forall_hasFDerivAt_of_fderiv_symmetric`: a closed 1-form on an open
  star-shaped set is exact.

## References

* [Spivak1965] M. Spivak, *Calculus on Manifolds*, Theorem 4-11 (Poincaré lemma).
-/

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace StarConvex

variable {c : E} {s : Set E}

/-- The cone with apex `c` over a set `B`: the union of the segments from `c` to points of `B`,
parametrised as `c + t • (y - c)` with `t ∈ [0, 1]`, `y ∈ B`. -/
def cone (c : E) (B : Set E) : Set E :=
  {z | ∃ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ B, z = c + t • (y - c)}

/-- A set is contained in any cone over it. -/
theorem subset_cone (c : E) (B : Set E) : B ⊆ cone c B :=
  fun y hy => ⟨1, ⟨zero_le_one, le_rfl⟩, y, hy, by simp⟩

/-- The apex belongs to the cone over a nonempty set. -/
theorem apex_mem_cone {B : Set E} (hB : B.Nonempty) : c ∈ cone c B := by
  obtain ⟨y, hy⟩ := hB
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, y, hy, by simp⟩

/-- The cone from a point over a convex set is convex. -/
theorem convex_cone {B : Set E} (hB : Convex ℝ B) (hne : B.Nonempty) : Convex ℝ (cone c B) := by
  rintro _ ⟨t₁, ht₁, y₁, hy₁, rfl⟩ _ ⟨t₂, ht₂, y₂, hy₂, rfl⟩ a b ha hb hab
  set m := a * t₁ + b * t₂ with hm
  have hm0 : 0 ≤ m := by have := ht₁.1; have := ht₂.1; positivity
  have hm1 : m ≤ 1 := by nlinarith [ht₁.2, ht₂.2]
  rcases hm0.eq_or_lt with h0 | hpos
  · have e1 : a * t₁ = 0 := by nlinarith [ht₁.1, ht₂.1]
    have e2 : b * t₂ = 0 := by nlinarith [ht₁.1, ht₂.1]
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, hne.some, hne.some_mem, ?_⟩
    linear_combination (norm := module) hab • c + e1 • (y₁ - c) + e2 • (y₂ - c)
  · refine ⟨m, ⟨hm0, hm1⟩, (a * t₁ / m) • y₁ + (b * t₂ / m) • y₂, hB hy₁ hy₂
      (by have := ht₁.1; positivity) (by have := ht₂.1; positivity) ?_, ?_⟩
    · rw [← add_div, div_self hpos.ne']
    · have h1 : m * (a * t₁ / m) = a * t₁ := mul_div_cancel₀ _ hpos.ne'
      have h2 : m * (b * t₂ / m) = b * t₂ := mul_div_cancel₀ _ hpos.ne'
      linear_combination (norm := module) hab • c - h1 • y₁ - h2 • y₂ + hm • c

/-- If `s` is star-shaped about `c` and contains `B`, then the cone with apex `c` over `B`
is contained in `s`. -/
theorem cone_subset (hs : StarConvex ℝ c s) {B : Set E} (hB : B ⊆ s) : cone c B ⊆ s := by
  rintro _ ⟨t, ht, y, hy, rfl⟩
  have h := hs (hB hy) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  convert h using 1
  module

variable [CompleteSpace F] {ω : E → E →L[ℝ] F}

/-- **Poincaré lemma, pointwise form**: on an open set `s` star-shaped about `c`, if `ω` is a
closed 1-form (differentiable with symmetric derivative), then `x ↦ ∫ᶜ y in [c, x], ω y` has
derivative `ω x` at every `x ∈ s`. -/
theorem hasFDerivAt_curveIntegral_segment_of_fderiv_symmetric (hs : StarConvex ℝ c s)
    (hso : IsOpen s) (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ u v, fderiv ℝ ω a u v = fderiv ℝ ω a v u) {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∫ᶜ z in Path.segment c y, ω z) (ω x) x := by
  obtain ⟨r, hr, hB⟩ := isOpen_iff.mp hso x hx
  set T := cone c (ball x r)
  have hne : (ball x r).Nonempty := ⟨x, mem_ball_self hr⟩
  have hTs : T ⊆ s := hs.cone_subset hB
  have hTc : Convex ℝ T := convex_cone (convex_ball x r) hne
  have hBT : ball x r ⊆ T := subset_cone c _
  have hcT : c ∈ T := apex_mem_cone hne
  have hxT : x ∈ T := hBT (mem_ball_self hr)
  have hωT : ∀ y ∈ T, HasFDerivWithinAt ω (fderiv ℝ ω y) T y := fun y hy =>
    ((hω y (hTs hy)).differentiableAt (hso.mem_nhds (hTs hy))).hasFDerivAt.hasFDerivWithinAt
  have h := hTc.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hωT
    (fun a ha u _ v _ => hdω a (hTs ha) u v) hcT hxT
  exact h.hasFDerivAt (Filter.mem_of_superset (ball_mem_nhds x hr) hBT)

/-- **Poincaré lemma for star-shaped open sets**: a closed 1-form `ω` (differentiable on `s`
with symmetric derivative) on an open set `s` star-shaped about some point admits a primitive:
there is `f` with `Df = ω` on `s`. -/
theorem exists_forall_hasFDerivAt_of_fderiv_symmetric (hs : StarConvex ℝ c s)
    (hso : IsOpen s) (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ u v, fderiv ℝ ω a u v = fderiv ℝ ω a v u) :
    ∃ f : E → F, ∀ a ∈ s, HasFDerivAt f (ω a) a :=
  ⟨fun y => ∫ᶜ z in Path.segment c y, ω z, fun _ ha =>
    hs.hasFDerivAt_curveIntegral_segment_of_fderiv_symmetric hso hω hdω ha⟩

end StarConvex
