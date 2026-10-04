import Resolution.GammaData

/-!
# Existence of the finite letter set Γ

From the letter bound we obtain a solution `S` whose letters all lie in a finite list `L`.
`Γ` is a dedup (up to `≡`) of the meets of all sublists of `L`.
-/

namespace Intersection

open Classical

/-- Dedup a list up to `≡`: keep an element iff it is not `≡` to a later kept one. -/
noncomputable def dedupEqv : List Ty → List Ty
  | [] => []
  | x :: l => if ∃ y ∈ dedupEqv l, Eqv x y then dedupEqv l else x :: dedupEqv l

theorem dedupEqv_sublist : ∀ l : List Ty, (dedupEqv l).Sublist l
  | [] => by simp [dedupEqv]
  | x :: l => by
    rw [dedupEqv]
    split_ifs
    · exact (dedupEqv_sublist l).cons x
    · exact (dedupEqv_sublist l).cons_cons x

theorem dedupEqv_pairwise : ∀ l : List Ty, (dedupEqv l).Pairwise (fun g h => ¬ Eqv g h)
  | [] => by simp [dedupEqv]
  | x :: l => by
    rw [dedupEqv]
    split_ifs with h
    · exact dedupEqv_pairwise l
    · refine List.Pairwise.cons (fun y hy hxy => h ⟨y, hy, hxy⟩) (dedupEqv_pairwise l)

theorem dedupEqv_cover : ∀ l : List Ty, ∀ x ∈ l, ∃ y ∈ dedupEqv l, Eqv x y
  | [], x, hx => by simp at hx
  | z :: l, x, hx => by
    rw [dedupEqv]
    rcases List.mem_cons.1 hx with rfl | hx
    · split_ifs with h
      · exact h
      · exact ⟨x, by simp, Eqv.refl x⟩
    · obtain ⟨y, hy, e⟩ := dedupEqv_cover l x hx
      split_ifs
      · exact ⟨y, hy, e⟩
      · exact ⟨y, by simp [hy], e⟩

theorem interList_le_of_subset {l₁ l₂ : List Ty} (h : ∀ x ∈ l₁, x ∈ l₂) :
    Le (Ty.interList l₂) (Ty.interList l₁) :=
  le_interList_iff.2 fun x hx => interList_le_of_mem (h x hx)

theorem interList_map_eqv {f : Ty → Ty} : ∀ {s : List Ty}, (∀ x ∈ s, Eqv (f x) x) →
    Eqv (Ty.interList (s.map f)) (Ty.interList s)
  | [], _ => Eqv.refl _
  | x :: s, h => by
    simp only [List.map_cons, Ty.interList]
    exact Eqv.inter (h x (by simp)) (interList_map_eqv fun y hy => h y (by simp [hy]))

theorem eqv_interList_singleton (l : Ty) : Eqv l (Ty.interList [l]) :=
  ⟨Le.inter_glb (Le.refl _) (Le.omega _), Le.inter_left _ _⟩

theorem Problem.isSubterm_of_mem_letterSubterms {P : Problem} {σ : Ty}
    (h : σ ∈ P.letterSubterms) : ∃ τ, P.IsSubterm (.arrow σ τ) := by
  obtain ⟨t, ht, e⟩ := List.mem_filterMap.1 h
  obtain ⟨e', he', ht'⟩ := List.mem_flatMap.1 ht
  cases t with
  | arrow a b =>
    simp only [Option.some.injEq] at e
    subst e
    exact ⟨b, e', he', List.mem_append.1 ht'⟩
  | _ => simp at e

theorem Problem.isSubterm_of_arrow {P : Problem} {σ τ : Ty} (h : P.IsSubterm (.arrow σ τ)) :
    P.IsSubterm σ := by
  obtain ⟨e, he, h⟩ := h
  have hσ : σ ∈ (Ty.arrow σ τ).subterms := by simp [Ty.subterms, Ty.mem_subterms_self]
  exact ⟨e, he, h.imp (Ty.mem_subterms_trans hσ) (Ty.mem_subterms_trans hσ)⟩

theorem GammaData.exists (P : Problem) (h : Unifiable P) : Nonempty (GammaData P) := by
  obtain ⟨S₀, hS₀⟩ := h
  obtain ⟨hc, hsol, hcL, hLlen, -, hrepL, -⟩ := letter_bound_strong P S₀ hS₀
  set pins := P.pins S₀ with hpins
  set c := letterMap pins with hcdef
  set L := letterList pins with hLdef
  set S : ℕ → Ty := fun x => (S₀ x).mapLetters c with hSdef
  have hT := transfer (μ := Ty.sdepth) (rep := Ty.rep) (ψ := psel Ty.sdepth pins)
    Ty.rep_eqv rep_letter_lt (sdepth_psel_le pins) (psel_mono Ty.sdepth pins)
    (pins := pins) fun π hπ => psel_pin Ty.sdepth pins hπ
  have hpin : ∀ π ∈ pins, Eqv (c π) (π.mapLetters c) := hT.2
  set C := L.sublists.map Ty.interList with hCdef
  set Γ := dedupEqv C with hΓdef
  have hΓC : ∀ g ∈ Γ, ∃ s, s.Sublist L ∧ g = Ty.interList s := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ((dedupEqv_sublist C).subset hg)
    exact ⟨s, List.mem_sublists.1 hs, rfl⟩
  have hcov : ∀ s : List Ty, (∀ x ∈ s, x ∈ L) → ∃ g ∈ Γ, Eqv (Ty.interList s) g := by
    intro s hs
    have hmem : Ty.interList (L.filter (fun x => decide (x ∈ s))) ∈ C :=
      List.mem_map_of_mem (List.mem_sublists.2 List.filter_sublist)
    obtain ⟨g, hg, e⟩ := dedupEqv_cover C _ hmem
    refine ⟨g, hg, Eqv.trans ⟨?_, ?_⟩ e⟩
    · exact interList_le_of_subset fun x hx => by
        simp only [List.mem_filter, decide_eq_true_eq] at hx; exact hx.2
    · exact interList_le_of_subset fun x hx => by
        simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hs x hx, hx⟩
  have hcovL : ∀ l ∈ L, ∃ g ∈ Γ, Eqv l g := fun l hl => by
    obtain ⟨g, hg, e⟩ := hcov [l] (by simp [hl])
    exact ⟨g, hg, (eqv_interList_singleton l).trans e⟩
  refine ⟨⟨Γ, S, hsol, dedupEqv_pairwise C, ?_, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨g, hg, e⟩ := hcov [] (by simp)
    exact ⟨g, hg, e.symm⟩
  · intro g hg h hh
    obtain ⟨a, ha, rfl⟩ := hΓC g hg
    obtain ⟨b, hb, rfl⟩ := hΓC h hh
    obtain ⟨k, hk, e⟩ := hcov (a ++ b) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      exacts [ha.subset hx, hb.subset hx])
    exact ⟨k, hk, (interList_append a b).symm.trans e⟩
  · intro g hg π hπ k hk
    obtain ⟨s, hs, rfl⟩ := hΓC g hg
    have hy : Eqv (Ty.rep (Ty.interList s)) (Ty.interList (s.map Ty.rep)) :=
      (Ty.rep_eqv _).trans (interList_map_eqv fun x _ => Ty.rep_eqv x).symm
    obtain ⟨q, hq, -, f⟩ := (Ty.rep_reduced _).exists_path hy hπ
    obtain ⟨k', hk', hkk'⟩ := forall₂_exists_of_mem f k hk
    rw [Ty.paths_interList, List.flatMap_map] at hq
    obtain ⟨l, hl, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨l', hl', e⟩ := hrepL l (hs.subset hl) q hq k' hk'
    obtain ⟨g', hg', e'⟩ := hcovL l' hl'
    exact ⟨g', hg', hkk'.trans (e.trans e')⟩
  · intro σ hσ
    obtain ⟨τ, hστ⟩ := Problem.isSubterm_of_mem_letterSubterms hσ
    have H : ∀ σ τ, P.IsSubterm (Ty.arrow σ τ) →
        Eqv (c (σ.subst S₀)) ((σ.subst S₀).mapLetters c) := fun σ τ h =>
      hpin _ (List.mem_map_of_mem (Problem.mem_letterSubterms h))
    have e1 := P.mapLetters_subst S₀ c H (Problem.isSubterm_of_arrow hστ)
    have e2 := H σ τ hστ
    obtain ⟨g, hg, e⟩ := hcovL _ (hcL (σ.subst S₀))
    exact ⟨g, hg, e1.symm.trans (e2.symm.trans e)⟩
  · calc Γ.length ≤ C.length := (dedupEqv_sublist C).length_le
      _ = 2 ^ L.length := by simp [hCdef, List.length_sublists]
      _ ≤ 2 ^ (4 ^ P.letterSubterms.length) := Nat.pow_le_pow_right (by omega) hLlen
      _ ≤ 2 ^ (4 ^ P.letterSubterms.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)

end Intersection
