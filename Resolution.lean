import Resolution.Final

/-!
# Intersection type unification is decidable

The main theorem: unifiability of intersection types with constants, modulo BCD subtyping
(`Intersection.Unifiable`, defined in `Intersection.Basic`), is a computable predicate. The
proof is assembled in `Resolution.Final`; this file states the result in the form in which it
is cited.

The modules under `Resolution/`, in dependency order:

* `Paths`: the path normal form and the verified subtyping decider `Ty.leb`.
* `Computability`: the decider and the constructors are primitive recursive.
* `Lattice`: the join of two types.
* `LetterMap`: letter maps and the transfer of unifiers along them.
* `LetterBound`: the selection lemma, the transfer lemma and the letter bound.
* `GammaData`, `GammaExists`: the finite letter set `Γ`.
* `MLP`, `Tower`: multi-level problems and their small-model theorem.
* `APDBase`, `APD`: the abstract problem, its completeness and its realisation.
* `Decide`: the bounded search and decidability from a bound.
* `Final`: the bound `bigBound` and the final assembly.
-/

namespace Intersection

/-- Unifiability of intersection types is decidable: some algorithm decides, for every
problem, whether it has a unifier. -/
theorem decidable : ComputablePred Unifiable := by
  exact decidable_final

end Intersection
