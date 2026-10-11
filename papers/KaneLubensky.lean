import KaneLubensky.Chain
import KaneLubensky.Lattices

/-!
# Kane–Lubensky: topological boundary modes in isostatic lattices

Formalization of parts of C. L. Kane, T. C. Lubensky, *Topological boundary modes in isostatic
lattices*, Nature Physics 10 (2014), built on `DiscreteMechanics`:

* `KaneLubensky.Chain`: the one-dimensional Maxwell chain; its unique zero mode, the absence of
  self-stress, the winding number of the Bloch compatibility, and the bulk–edge correspondence.
* `KaneLubensky.Lattices`: the square lattice (lines of floppy modes) and the kagome lattice
  (Maxwell counting, self-stresses at `θ = 0`).
-/
