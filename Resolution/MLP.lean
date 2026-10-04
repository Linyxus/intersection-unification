import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Multi-level problems

A *multi-level problem* consists of a finite alphabet `Γ`, `R` "lower levels" given by
projections `φ r : Γ → Γ` (for `r : Fin R`, level `r` lives on the words over the image of
`φ r`), finite label types `F r` for the lower levels, a finite state type `Q` for the top level
and a transition relation `Δ q ι children` for the top level, where `ι` gives the labels of the
lower levels *read through the projections*.

A solution consists of labellings `f r : List Γ → F r` and a top labelling `L : List Γ → Q` such
that at every word `w` the transition holds with input `fun r => f r (w.map (φ r))` and children
`fun h => L (h :: w)`, the root condition holds at `[]`, and everything is zero from depth `N` on.
Words are read from the end: the children of `w` are `h :: w`.

The abstract problem of `Resolution.APDBase` is an instance (`APD.mlp`). The small-model
theorem, which bounds the support of a solution independently of `N`, is proved in
`Resolution.Tower`.
-/

namespace Intersection

/-- A multi-level problem. -/
structure MLP where
  Γ : Type
  [instFintypeΓ : Fintype Γ]
  [instDecEqΓ : DecidableEq Γ]
  R : ℕ
  φ : Fin R → Γ → Γ
  F : Fin R → Type
  [instFintypeF : ∀ r, Fintype (F r)]
  [instDecEqF : ∀ r, DecidableEq (F r)]
  zF : ∀ r, F r
  Q : Type
  [instFintypeQ : Fintype Q]
  [instDecEqQ : DecidableEq Q]
  zQ : Q
  Δ : Q → (∀ r, F r) → (Γ → Q) → Prop
  root : Q → Prop
  φ_idem : ∀ r h, φ r (φ r h) = φ r h
  φ_comp : ∀ s r : Fin R, s ≤ r → ∀ h, φ s (φ r h) = φ s h
  φ_comp' : ∀ s r : Fin R, s ≤ r → ∀ h, φ r (φ s h) = φ s h
  Δ_zero : Δ zQ zF (fun _ => zQ)

attribute [instance] MLP.instFintypeΓ MLP.instDecEqΓ MLP.instFintypeF MLP.instDecEqF
  MLP.instFintypeQ MLP.instDecEqQ

/-- The input of the top level at the word `w`: the lower labels read through the projections. -/
def MLP.input (M : MLP) (f : ∀ r, List M.Γ → M.F r) (w : List M.Γ) : ∀ r, M.F r :=
  fun r => f r (w.map (M.φ r))

/-- A solution of `M` that is zero from depth `N` on. -/
structure MLP.Sol (M : MLP) (N : ℕ) where
  f : ∀ r, List M.Γ → M.F r
  L : List M.Γ → M.Q
  step : ∀ w, M.Δ (L w) (M.input f w) (fun h => L (h :: w))
  root : M.root (L [])
  supp : ∀ w, N ≤ w.length → L w = M.zQ ∧ ∀ r, f r w = M.zF r

end Intersection
