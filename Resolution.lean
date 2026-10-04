import Intersection
import Resolution.Paths
import Resolution.Computability
import Resolution.Lattice
import Resolution.LetterMap
import Resolution.LetterBound
import Resolution.GammaExists
import Resolution.Tower
import Resolution.Decide
import Resolution.APD
import Resolution.Final

/-!
The two theorems; prove one of them. Keep their names and statements. Put helper
definitions and lemmas in modules under `Resolution/` imported from here, or in this file.
-/

namespace Intersection

/-- Unifiability of intersection types is decidable: some algorithm decides, for every
problem, whether it has a unifier. -/
theorem decidable : ComputablePred Unifiable := by
  exact decidable_final

/-- Unifiability of intersection types is undecidable: no algorithm decides, for every
problem, whether it has a unifier. -/
theorem undecidable : ¬ ComputablePred Unifiable := by
  sorry

end Intersection
