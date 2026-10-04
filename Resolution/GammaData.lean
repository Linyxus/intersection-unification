import Resolution.LetterBound

/-!
# The finite letter set Γ

The interface between the letter bound and the abstract problem. `GammaData P` packages a
solution `S` of `P` together with a finite list `Γ` of types that contains (up to `≡`) the
values of all letter-subterms of `P` under `S`, contains `ω`, is closed under `∩` and under
taking letters of depth-minimal representatives (all up to `≡`), and whose elements are
pairwise inequivalent. Its length is at most `2 ^ (4 ^ n + 1)`, where `n` is the number of
letter-subterms of `P`. Its existence for unifiable problems is proved in
`Resolution.GammaExists` from the letter bound of `Resolution.LetterBound`; the abstract
problem of `Resolution.APDBase` is built over it.
-/

namespace Intersection

/-- A solution of `P` together with a finite letter set containing its pins, closed under `∩`
and under taking letters, deduplicated up to `≡`. -/
structure GammaData (P : Problem) where
  /-- The letter set. -/
  Γ : List Ty
  /-- The solution. -/
  S : ℕ → Ty
  /-- `S` solves `P`. -/
  solves : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)
  /-- The elements of `Γ` are pairwise inequivalent. -/
  nodup : Γ.Pairwise (fun g h => ¬ Eqv g h)
  /-- `ω` is in `Γ` up to `≡`. -/
  omega_mem : ∃ g ∈ Γ, Eqv g Ty.omega
  /-- `Γ` is closed under `∩` up to `≡`. -/
  inter_mem : ∀ g ∈ Γ, ∀ h ∈ Γ, ∃ k ∈ Γ, Eqv (Ty.inter g h) k
  /-- The letters of the depth-minimal representative of an element of `Γ` are in `Γ` up to
  `≡`. -/
  rep_mem : ∀ g ∈ Γ, ∀ π ∈ (Ty.rep g).paths, ∀ k ∈ π.1, ∃ g' ∈ Γ, Eqv k g'
  /-- The pins, the values of the letter-subterms of `P` under `S`, are in `Γ` up to `≡`. -/
  pins_mem : ∀ σ ∈ P.letterSubterms, ∃ g ∈ Γ, Eqv (σ.subst S) g
  /-- The size bound. -/
  length_le : Γ.length ≤ 2 ^ (4 ^ P.letterSubterms.length + 1)

end Intersection
