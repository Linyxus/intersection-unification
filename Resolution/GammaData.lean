import Resolution.LetterBound

/-!
# The finite letter set Γ (interface)

`GammaData P` packages a solution `S` of `P` together with a finite list `Γ` of types that
contains (up to `≡`) the values of all letter-subterms of `P` under `S`, contains `ω`, is closed
under `∩` and under taking letters of depth-minimal representatives (all up to `≡`), and whose
elements are pairwise inequivalent. Its existence for unifiable problems is proved in
`Resolution.GammaExists` from the letter bound of `Resolution.LetterBound`.
-/

namespace Intersection

structure GammaData (P : Problem) where
  Γ : List Ty
  S : ℕ → Ty
  solves : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)
  nodup : Γ.Pairwise (fun g h => ¬ Eqv g h)
  omega_mem : ∃ g ∈ Γ, Eqv g Ty.omega
  inter_mem : ∀ g ∈ Γ, ∀ h ∈ Γ, ∃ k ∈ Γ, Eqv (Ty.inter g h) k
  rep_mem : ∀ g ∈ Γ, ∀ π ∈ (Ty.rep g).paths, ∀ k ∈ π.1, ∃ g' ∈ Γ, Eqv k g'
  pins_mem : ∀ σ ∈ P.letterSubterms, ∃ g ∈ Γ, Eqv (σ.subst S) g
  length_le : Γ.length ≤ 2 ^ (4 ^ P.letterSubterms.length + 1)

end Intersection
