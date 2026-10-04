import Resolution.Paths

/-!
# Letter maps

The first step of the argument transforms an arbitrary unifier into one whose letters come
from a finite set. The transformation is a *letter map*: `T.mapLetters c` applies `c` to every
letter of every path of `T`. For monotone `c` this is monotone in `T` (`Ty.mapLetters_mono`),
and it commutes with substitution on the subterms of a problem provided `c` agrees with
`mapLetters c` on the substituted letters of the problem (`Problem.mapLetters_subst`). Hence
a unifier `S` composed letterwise with such a `c` is again a unifier
(`Problem.mapLetters_solves`). Which `c` to use is the business of the selection lemma and
the transfer lemma in `Resolution.LetterBound`.

The file also defines the subterms of a type and of a problem (`Ty.subterms`,
`Problem.IsSubterm`).
-/

namespace Intersection

/-- Apply `c` to every letter of every path. -/
def Ty.mapLetters (c : Ty → Ty) (T : Ty) : Ty :=
  Ty.interList (T.paths.map fun π => pathTy (π.1.map c, π.2))

/-- Monotonicity of a map on types. -/
def MonoMap (c : Ty → Ty) : Prop := ∀ θ θ', Le θ θ' → Le (c θ) (c θ')

/-- A monotone letter map is monotone on types. -/
theorem Ty.mapLetters_mono {c : Ty → Ty} (hc : MonoMap c) {T T' : Ty} (h : Le T T') :
    Le (T.mapLetters c) (T'.mapLetters c) := by
  rw [Ty.le_iff_leb, Ty.leb_iff] at h
  refine le_interList_iff.2 fun x hx => ?_
  obtain ⟨π', hπ', rfl⟩ := List.mem_map.1 hx
  obtain ⟨π, hπ, e, f⟩ := h π' hπ'
  refine (interList_le_of_mem (List.mem_map_of_mem (f := fun π => pathTy (π.1.map c, π.2))
    hπ)).trans ?_
  simp only [e]
  refine pathTy_le_pathTy _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact f.imp fun a b h => hc a b (Ty.le_of_leb h)

theorem Ty.mapLetters_eqv {c : Ty → Ty} (hc : MonoMap c) {T T' : Ty} (h : Eqv T T') :
    Eqv (T.mapLetters c) (T'.mapLetters c) :=
  ⟨Ty.mapLetters_mono hc h.1, Ty.mapLetters_mono hc h.2⟩

/-! ## Congruence helpers -/

/-- `Eqv` is a congruence for intersections. -/
theorem Eqv.inter {σ σ' τ τ' : Ty} (h₁ : Eqv σ σ') (h₂ : Eqv τ τ') :
    Eqv (.inter σ τ) (.inter σ' τ') :=
  ⟨Le.inter_glb ((Le.inter_left _ _).trans h₁.1) ((Le.inter_right _ _).trans h₂.1),
    Le.inter_glb ((Le.inter_left _ _).trans h₁.2) ((Le.inter_right _ _).trans h₂.2)⟩

/-- `Eqv` is a congruence for arrows. -/
theorem Eqv.arrow {σ σ' τ τ' : Ty} (h₁ : Eqv σ σ') (h₂ : Eqv τ τ') :
    Eqv (.arrow σ τ) (.arrow σ' τ') :=
  ⟨Le.arrow h₁.2 h₂.1, Le.arrow h₁.1 h₂.2⟩

/-- The intersection of an appended list is the intersection of the two intersections. -/
theorem interList_append (l₁ l₂ : List Ty) :
    Eqv (Ty.interList (l₁ ++ l₂)) (.inter (Ty.interList l₁) (Ty.interList l₂)) := by
  refine ⟨Le.inter_glb (le_interList_iff.2 fun x hx => interList_le_of_mem (by simp [hx]))
    (le_interList_iff.2 fun x hx => interList_le_of_mem (by simp [hx])), ?_⟩
  refine le_interList_iff.2 fun x hx => ?_
  rcases List.mem_append.1 hx with hx | hx
  · exact (Le.inter_left _ _).trans (interList_le_of_mem hx)
  · exact (Le.inter_right _ _).trans (interList_le_of_mem hx)

/-- Arrows with a common domain distribute over intersections. -/
theorem interList_map_arrow (ρ : Ty) (l : List Ty) :
    Eqv (Ty.interList (l.map (Ty.arrow ρ))) (Ty.arrow ρ (Ty.interList l)) := by
  refine ⟨interList_map_arrow_le ρ l, le_interList_iff.2 fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact Le.arrow (Le.refl _) (interList_le_of_mem hy)

/-! ## Structural lemmas -/

/-- `mapLetters` distributes over intersections. -/
theorem Ty.mapLetters_inter (c : Ty → Ty) (A B : Ty) :
    Eqv ((Ty.inter A B).mapLetters c) (.inter (A.mapLetters c) (B.mapLetters c)) := by
  unfold Ty.mapLetters
  rw [Ty.paths, List.map_append]
  exact interList_append _ _

/-- `mapLetters` applies `c` to the domain of an arrow and recurses into the codomain. -/
theorem Ty.mapLetters_arrow (c : Ty → Ty) (ρ τ : Ty) :
    Eqv ((Ty.arrow ρ τ).mapLetters c) (.arrow (c ρ) (τ.mapLetters c)) := by
  unfold Ty.mapLetters
  have : ((Ty.arrow ρ τ).paths.map fun π => pathTy (π.1.map c, π.2)) =
      (τ.paths.map fun π => pathTy (π.1.map c, π.2)).map (Ty.arrow (c ρ)) := by
    simp [Ty.paths, pathTy, Function.comp_def]
  rw [this]
  exact interList_map_arrow _ _

theorem Ty.mapLetters_const (c : Ty → Ty) (n : ℕ) : Eqv ((Ty.const n).mapLetters c) (.const n) :=
  ⟨Le.inter_left _ _, Le.inter_glb (Le.refl _) (Le.omega _)⟩

theorem Ty.mapLetters_var (c : Ty → Ty) (n : ℕ) : Eqv ((Ty.var n).mapLetters c) (.var n) :=
  ⟨Le.inter_left _ _, Le.inter_glb (Le.refl _) (Le.omega _)⟩

theorem Ty.mapLetters_omega (c : Ty → Ty) : (Ty.omega).mapLetters c = .omega := rfl

/-! ## Subterms -/

/-- All subterms of a type (including itself). -/
def Ty.subterms : Ty → List Ty
  | .const n => [.const n]
  | .var n => [.var n]
  | .omega => [.omega]
  | .arrow σ τ => .arrow σ τ :: (σ.subterms ++ τ.subterms)
  | .inter σ τ => .inter σ τ :: (σ.subterms ++ τ.subterms)

theorem Ty.mem_subterms_self (σ : Ty) : σ ∈ σ.subterms := by
  cases σ <;> simp [Ty.subterms]

/-- Being a subterm is transitive. -/
theorem Ty.mem_subterms_trans {ρ σ τ : Ty} (h₁ : ρ ∈ σ.subterms) (h₂ : σ ∈ τ.subterms) :
    ρ ∈ τ.subterms := by
  induction τ with
  | const n => simp [Ty.subterms] at h₂; subst h₂; exact h₁
  | var n => simp [Ty.subterms] at h₂; subst h₂; exact h₁
  | omega => simp [Ty.subterms] at h₂; subst h₂; exact h₁
  | arrow a b iha ihb =>
    simp only [Ty.subterms, List.mem_cons, List.mem_append] at h₂ ⊢
    rcases h₂ with rfl | h | h
    · simpa [Ty.subterms] using h₁
    · exact Or.inr (Or.inl (iha h))
    · exact Or.inr (Or.inr (ihb h))
  | inter a b iha ihb =>
    simp only [Ty.subterms, List.mem_cons, List.mem_append] at h₂ ⊢
    rcases h₂ with rfl | h | h
    · simpa [Ty.subterms] using h₁
    · exact Or.inr (Or.inl (iha h))
    · exact Or.inr (Or.inr (ihb h))

/-- The subterms of a problem: subterms of either side of some equation. -/
def Problem.IsSubterm (P : Problem) (σ : Ty) : Prop :=
  ∃ e ∈ P, σ ∈ e.1.subterms ∨ σ ∈ e.2.subterms

/-! ## Commutation with substitution -/

/-- Single-type commutation: if `c` agrees with `mapLetters c` on the substituted letters of
`T`, then `mapLetters c` commutes with substitution on `T`. -/
theorem Ty.mapLetters_subst (c : Ty → Ty) (S : ℕ → Ty) (T : Ty)
    (H : ∀ σ τ, Ty.arrow σ τ ∈ T.subterms →
      Eqv (c (σ.subst S)) ((σ.subst S).mapLetters c)) :
    Eqv ((T.subst S).mapLetters c) (T.subst fun x => (S x).mapLetters c) := by
  induction T with
  | const n => exact Ty.mapLetters_const c n
  | var n => exact Eqv.refl _
  | omega => exact Eqv.refl _
  | arrow σ τ ihσ ihτ =>
    have hσ := ihσ fun a b h => H a b (by simp [Ty.subterms, h])
    have hτ := ihτ fun a b h => H a b (by simp [Ty.subterms, h])
    have h₀ := H σ τ (Ty.mem_subterms_self _)
    exact (Ty.mapLetters_arrow c _ _).trans (Eqv.arrow (h₀.trans hσ) hτ)
  | inter σ τ ihσ ihτ =>
    have hσ := ihσ fun a b h => H a b (by simp [Ty.subterms, h])
    have hτ := ihτ fun a b h => H a b (by simp [Ty.subterms, h])
    exact (Ty.mapLetters_inter c _ _).trans (Eqv.inter hσ hτ)

/-- Main commutation theorem: on every subterm of `P`, `mapLetters c` commutes with `S`. -/
theorem Problem.mapLetters_subst (P : Problem) (S : ℕ → Ty) (c : Ty → Ty)
    (H : ∀ σ τ, P.IsSubterm (Ty.arrow σ τ) →
      Eqv (c (σ.subst S)) ((σ.subst S).mapLetters c))
    {σ : Ty} (hσ : P.IsSubterm σ) :
    Eqv ((σ.subst S).mapLetters c) (σ.subst fun x => (S x).mapLetters c) := by
  refine Ty.mapLetters_subst c S σ fun a b h => H a b ?_
  obtain ⟨e, he, h'⟩ := hσ
  exact ⟨e, he, h'.imp (Ty.mem_subterms_trans h) (Ty.mem_subterms_trans h)⟩

/-- The letter-mapped substitution is again a unifier. -/
theorem Problem.mapLetters_solves (P : Problem) (S : ℕ → Ty) {c : Ty → Ty} (hc : MonoMap c)
    (H : ∀ σ τ, P.IsSubterm (Ty.arrow σ τ) →
      Eqv (c (σ.subst S)) ((σ.subst S).mapLetters c))
    (hS : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) :
    ∀ e ∈ P, Eqv (e.1.subst fun x => (S x).mapLetters c)
      (e.2.subst fun x => (S x).mapLetters c) := by
  intro e he
  have h₁ := P.mapLetters_subst S c H (σ := e.1) ⟨e, he, Or.inl (Ty.mem_subterms_self _)⟩
  have h₂ := P.mapLetters_subst S c H (σ := e.2) ⟨e, he, Or.inr (Ty.mem_subterms_self _)⟩
  exact h₁.symm.trans ((Ty.mapLetters_eqv hc (hS e he)).trans h₂)

/-- Unifiability witnessed by a letter-mapped unifier. -/
theorem Problem.unifiable_of_mapLetters (P : Problem) (S : ℕ → Ty) {c : Ty → Ty}
    (hc : MonoMap c)
    (H : ∀ σ τ, P.IsSubterm (Ty.arrow σ τ) →
      Eqv (c (σ.subst S)) ((σ.subst S).mapLetters c))
    (hS : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) : Unifiable P :=
  ⟨_, P.mapLetters_solves S hc H hS⟩

end Intersection
