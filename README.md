# ContinuumMechanics

A Lean 4 library of continuum mechanics and structural theories built on
Mathlib: tensor algebra, kinematics, stress, constitutive theory, linear
elastostatics, beams and plates. No axioms; `main` is `sorry`-free.

* Design: [`ARCHITECTURE.md`](ARCHITECTURE.md)
* Plan: [`ROADMAP.md`](ROADMAP.md)
* Assumptions not yet provable from Mathlib: [`GAPS.md`](GAPS.md)

## Nexorade

[`Nexorade/`](Nexorade) is a separate library (built on `ContinuumMechanics`) formalizing
L. Greco, A. Lebée, C. Douthe, *Investigation of the elastic behavior of reciprocal systems using
homogenization techniques* (2013): the square nexorade homogenized as a degenerate
Kirchhoff–Love plate. See [`Nexorade.lean`](Nexorade.lean) for the section-by-section map.

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
scripts/check_no_sorry_axiom.sh
```
