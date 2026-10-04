import Resolution.Lattice
import Resolution.LetterMap
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

/-!
# The letter bound

The first step of the argument: any unifier `S` of a problem `P` can be composed with a
monotone letter map that fixes the values of the letter-subterms of `P` (the *pins*) and does
not raise depth, so that the resulting unifier has at most `4 ^ n` letters, where `n` is the
number of letter-subterms of `P` (`letter_bound`, `letter_bound_strong`).

The argument has three parts.

* *Semantic depth.* `Ty.sdepth T` is the least syntactic letter depth `Ty.ldepth` of a type
  equivalent to `T`, and `Ty.rep T` is a depth-minimal representative with as few paths as
  possible. Such a representative is *reduced* (`Ty.rep_reduced`): no path dominates another,
  so every path of it is matched letterwise up to `≡` in any equivalent type
  (`Ty.Reduced.exists_path`). The letters of `Ty.rep T` have strictly smaller semantic depth
  than `T` (`Ty.sdepth_letter_lt`).
* *The selection lemma* (section `Selection`). Fix the pins and a measure `μ` that is
  subadditive for meets and joins. The *profile* of a type `x` is the pair (pins below `x`,
  pins above `x`). For a profile `q`, `g_q` (`gsel`) is the meet of measure-minimal
  representatives of the profiles `≥ q` with no greater minimal measure, and `c_q` (`csel`)
  is the join of the `g_r` over the profiles `r ≤ q` with no greater minimal measure. The
  selection map `ψ x := c_{p(x)}` (`psel`) is monotone (`psel_mono`), fixes the pins up to
  `≡` (`psel_pin`), does not increase the measure (`measure_psel_le`) and takes at most
  `4 ^ |pins|` values (`psel_image`).
* *The transfer lemma* (section `Transfer`). Given a selection `ψ`, `rebuild g` replaces, in
  the representative of `g`, every letter `k` by `rebuild (ψ k)`, recursively along the
  measure. The map `c := rebuild ∘ ψ` is monotone and commutes with `mapLetters c` on the
  pins (`transfer`), which is exactly what `Problem.mapLetters_solves` needs.

Instantiating the measure with the semantic depth gives the letter map `letterMap` and the
list `letterList` of its possible values, of length at most `4 ^ n`, closed under taking
letters, with the semantic depth strictly decreasing along letters.
-/

namespace Intersection

open Classical

/-! ## Syntactic letter depth -/

/-- Syntactic letter-nesting depth. -/
def Ty.ldepth : Ty → ℕ
  | .const _ => 0
  | .var _ => 0
  | .omega => 0
  | .inter σ τ => max σ.ldepth τ.ldepth
  | .arrow σ τ => max (σ.ldepth + 1) τ.ldepth

/-- The atom of a path is a constant or a variable. -/
theorem Ty.atom_of_mem_paths {T : Ty} {π : List Ty × Ty} (h : π ∈ T.paths) :
    π.2.paths = [([], π.2)] ∧ π.2.ldepth = 0 := by
  induction T generalizing π with
  | const n => simp [paths] at h; subst h; simp [paths, ldepth]
  | var n => simp [paths] at h; subst h; simp [paths, ldepth]
  | omega => simp [paths] at h
  | inter σ τ ihσ ihτ =>
    simp only [paths, List.mem_append] at h
    rcases h with h | h
    exacts [ihσ h, ihτ h]
  | arrow ρ τ _ ihτ =>
    simp only [paths, List.mem_map] at h
    obtain ⟨π', hπ', rfl⟩ := h
    simpa using ihτ hπ'

theorem Ty.ldepth_lt_of_mem_paths {T : Ty} {π : List Ty × Ty} (h : π ∈ T.paths) :
    ∀ k ∈ π.1, k.ldepth < T.ldepth := by
  induction T generalizing π with
  | const n => simp [paths] at h; subst h; simp
  | var n => simp [paths] at h; subst h; simp
  | omega => simp [paths] at h
  | inter σ τ ihσ ihτ =>
    simp only [paths, List.mem_append] at h
    rcases h with h | h
    · intro k hk; have := ihσ h k hk; simp [ldepth]; omega
    · intro k hk; have := ihτ h k hk; simp [ldepth]; omega
  | arrow ρ τ _ ihτ =>
    simp only [paths, List.mem_map] at h
    obtain ⟨π', hπ', rfl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [ldepth]
    · have := ihτ hπ' x hx; simp [ldepth]; omega

theorem Ty.ldepth_interList_le {l : List Ty} {n : ℕ} :
    (Ty.interList l).ldepth ≤ n ↔ ∀ x ∈ l, x.ldepth ≤ n := by
  induction l with
  | nil => simp [Ty.interList, ldepth]
  | cons x l ih => simp [Ty.interList, ldepth, ih]

theorem Ty.ldepth_pathTy_le {ls : List Ty} {a : Ty} (ha : a.ldepth = 0) {n : ℕ} :
    (pathTy (ls, a)).ldepth ≤ n ↔ ∀ k ∈ ls, k.ldepth + 1 ≤ n := by
  induction ls with
  | nil => simp [pathTy, ha]
  | cons k ls ih =>
    simp only [pathTy, List.foldr_cons] at ih ⊢
    simp [ldepth, ih]

theorem Ty.paths_interList (l : List Ty) : (Ty.interList l).paths = l.flatMap Ty.paths := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [Ty.interList, paths, ih]

theorem Ty.paths_pathTy {ls : List Ty} {a : Ty} (ha : a.paths = [([], a)]) :
    (pathTy (ls, a)).paths = [(ls, a)] := by
  induction ls with
  | nil => simpa [pathTy] using ha
  | cons k ls ih =>
    simp only [pathTy, List.foldr_cons] at ih ⊢
    simp [paths, ih]

/-- Paths of a letter-mapped type. -/
theorem Ty.mem_paths_mapLetters {f : Ty → Ty} {T : Ty} {π : List Ty × Ty}
    (h : π ∈ (T.mapLetters f).paths) : ∃ π₀ ∈ T.paths, π = (π₀.1.map f, π₀.2) := by
  rw [Ty.mapLetters, Ty.paths_interList] at h
  simp only [List.flatMap_map, List.mem_flatMap] at h
  obtain ⟨π₀, h₀, hπ⟩ := h
  rw [Ty.paths_pathTy (Ty.atom_of_mem_paths h₀).1] at hπ
  simp only [List.mem_singleton] at hπ
  exact ⟨π₀, h₀, hπ⟩

theorem Ty.mapLetters_congr {f f' : Ty → Ty} {T : Ty}
    (h : ∀ π ∈ T.paths, ∀ k ∈ π.1, f k = f' k) : T.mapLetters f = T.mapLetters f' := by
  unfold Ty.mapLetters
  congr 1
  refine List.map_congr_left fun π hπ => ?_
  rw [List.map_congr_left (h π hπ)]

/-- Monotonicity of `mapLetters` needing monotonicity of `c` only on the relevant letters. -/
theorem Ty.mapLetters_mono_of {c : Ty → Ty} {T T' : Ty} (h : Le T T')
    (hc : ∀ π ∈ T.paths, ∀ π' ∈ T'.paths, ∀ a ∈ π'.1, ∀ b ∈ π.1, Le a b → Le (c a) (c b)) :
    Le (T.mapLetters c) (T'.mapLetters c) := by
  refine le_interList_iff.2 fun x hx => ?_
  obtain ⟨π', hπ', rfl⟩ := List.mem_map.1 hx
  obtain ⟨π, hπ, e, f⟩ := le_iff_paths.1 h π' hπ'
  refine (interList_le_of_mem (List.mem_map_of_mem (f := fun π => pathTy (π.1.map c, π.2))
    hπ)).trans ?_
  simp only [e]
  refine pathTy_le_pathTy _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact forall₂_imp_mem f fun a ha b hb hab => hc π hπ π' hπ' a ha b hb hab

/-! ## Semantic depth and depth-minimal representatives -/

theorem Ty.exists_eqv_ldepth (T : Ty) : ∃ n, ∃ x, Eqv x T ∧ x.ldepth = n :=
  ⟨_, T, Eqv.refl T, rfl⟩

/-- Semantic depth: the least syntactic letter depth of an equivalent type. -/
noncomputable def Ty.sdepth (T : Ty) : ℕ := Nat.find T.exists_eqv_ldepth

theorem Ty.sdepth_le {x T : Ty} (h : Eqv x T) : T.sdepth ≤ x.ldepth :=
  Nat.find_min' T.exists_eqv_ldepth ⟨x, h, rfl⟩

theorem Ty.exists_rep (T : Ty) :
    ∃ m, ∃ x, Eqv x T ∧ x.ldepth = T.sdepth ∧ x.paths.length = m := by
  obtain ⟨x, hx, e⟩ := Nat.find_spec T.exists_eqv_ldepth
  exact ⟨_, x, hx, e, rfl⟩

/-- A representative of `T` of least letter depth, and among those, with fewest paths. -/
noncomputable def Ty.rep (T : Ty) : Ty := Classical.choose (Nat.find_spec T.exists_rep)

theorem Ty.rep_eqv (T : Ty) : Eqv T.rep T :=
  (Classical.choose_spec (Nat.find_spec T.exists_rep)).1

theorem Ty.ldepth_rep (T : Ty) : T.rep.ldepth = T.sdepth :=
  (Classical.choose_spec (Nat.find_spec T.exists_rep)).2.1

theorem Ty.rep_paths_length_le {x T : Ty} (h : Eqv x T) (hd : x.ldepth = T.sdepth) :
    T.rep.paths.length ≤ x.paths.length := by
  unfold Ty.rep; rw [(Classical.choose_spec (Nat.find_spec T.exists_rep)).2.2]
  exact Nat.find_min' T.exists_rep ⟨x, h, hd, rfl⟩

/-- Semantic depth is invariant under equivalence. -/
theorem Ty.sdepth_congr {T T' : Ty} (h : Eqv T T') : T.sdepth = T'.sdepth := by
  apply le_antisymm
  · rw [← Ty.ldepth_rep T']; exact Ty.sdepth_le ((Ty.rep_eqv T').trans h.symm)
  · rw [← Ty.ldepth_rep T]; exact Ty.sdepth_le ((Ty.rep_eqv T).trans h)

theorem Ty.sdepth_le_ldepth (T : Ty) : T.sdepth ≤ T.ldepth := Ty.sdepth_le (Eqv.refl T)

/-- Letters of the representative have strictly smaller semantic depth. -/
theorem Ty.sdepth_letter_lt {T : Ty} {π : List Ty × Ty} (h : π ∈ T.rep.paths) {k : Ty}
    (hk : k ∈ π.1) : k.sdepth < T.sdepth := by
  have := Ty.ldepth_lt_of_mem_paths h k hk
  have := Ty.sdepth_le_ldepth k
  rw [Ty.ldepth_rep] at *
  omega

/-- Meets do not increase the semantic depth. -/
theorem Ty.sdepth_inter_le (A B : Ty) :
    (Ty.inter A B).sdepth ≤ max A.sdepth B.sdepth := by
  have := Ty.sdepth_le (Eqv.inter (Ty.rep_eqv A) (Ty.rep_eqv B))
  simpa [Ty.ldepth, Ty.ldepth_rep] using this

/-- Joins do not increase the syntactic depth. -/
theorem Ty.ldepth_join_le (A B : Ty) : (A.join B).ldepth ≤ max A.ldepth B.ldepth := by
  refine Ty.ldepth_interList_le.2 fun x hx => ?_
  simp only [List.mem_map, Ty.joinPaths, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hx
  obtain ⟨_, ⟨p, hp, q, ⟨hq, -, -⟩, rfl⟩, rfl⟩ := hx
  refine (Ty.ldepth_pathTy_le (Ty.atom_of_mem_paths hp).2).2 fun k hk => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hk
  have hi' : i < min p.1.length q.1.length := by simpa using hi
  simp only [List.getElem_zipWith]
  have h1 := Ty.ldepth_lt_of_mem_paths hp _ (List.getElem_mem (l := p.1) (by omega : i < _))
  have h2 := Ty.ldepth_lt_of_mem_paths hq _ (List.getElem_mem (l := q.1) (by omega : i < _))
  simp only [Ty.ldepth]
  omega

theorem Ty.join_eqv {A A' B B' : Ty} (hA : Eqv A A') (hB : Eqv B B') :
    Eqv (A.join B) (A'.join B') :=
  ⟨Ty.join_mono hA.1 hB.1, Ty.join_mono hA.2 hB.2⟩

/-- Joins do not increase the semantic depth. -/
theorem Ty.sdepth_join_le (A B : Ty) : (A.join B).sdepth ≤ max A.sdepth B.sdepth := by
  have := Ty.sdepth_le (Ty.join_eqv (Ty.rep_eqv A) (Ty.rep_eqv B))
  have := Ty.ldepth_join_le A.rep B.rep
  rw [Ty.ldepth_rep, Ty.ldepth_rep] at this
  omega

/-! ## Reducedness of representatives -/

/-- Path `p'` lies below path `p` (as types). -/
def PathLe (p' p : List Ty × Ty) : Prop :=
  p'.2 = p.2 ∧ List.Forall₂ (fun a b => Le a b) p.1 p'.1

/-- No path is dominated by a different path. -/
def Ty.Reduced (x : Ty) : Prop := ∀ p ∈ x.paths, ∀ p' ∈ x.paths, PathLe p' p → p' = p

/-- Depth-minimal representatives with fewest paths are reduced. -/
theorem Ty.rep_reduced (T : Ty) : T.rep.Reduced := by
  intro p hp p' hp' hle
  by_contra hne
  set l := T.rep.paths.filter (fun π => decide (π ≠ p)) with hl
  set y := Ty.interList (l.map pathTy) with hy
  have hyp : y.paths = l := by
    rw [hy, Ty.paths_interList, List.flatMap_map]
    conv_rhs => rw [← List.flatMap_singleton' l]
    refine List.flatMap_congr fun π hπ => ?_
    exact Ty.paths_pathTy (Ty.atom_of_mem_paths (List.mem_filter.1 hπ).1).1
  have hmem : ∀ {π}, π ∈ l ↔ π ∈ T.rep.paths ∧ π ≠ p := by
    intro π; simp [hl]
  have heq : Eqv y T.rep := by
    constructor
    · rw [le_iff_paths]
      intro π hπ
      by_cases e : π = p
      · subst e
        exact ⟨p', by rw [hyp]; exact hmem.2 ⟨hp', hne⟩, hle⟩
      · exact ⟨π, by rw [hyp]; exact hmem.2 ⟨hπ, e⟩, rfl,
          List.forall₂_same.2 fun x _ => Le.refl x⟩
    · refine le_interList_iff.2 fun x hx => ?_
      obtain ⟨π, hπ, rfl⟩ := List.mem_map.1 hx
      exact le_pathTy (hmem.1 hπ).1
  have hyd : y.ldepth ≤ T.rep.ldepth := by
    refine Ty.ldepth_interList_le.2 fun x hx => ?_
    obtain ⟨π, hπ, rfl⟩ := List.mem_map.1 hx
    have hπ' := (hmem.1 hπ).1
    obtain ⟨l', a⟩ := π
    exact (Ty.ldepth_pathTy_le (Ty.atom_of_mem_paths hπ').2).2 fun k hk =>
      Ty.ldepth_lt_of_mem_paths hπ' k hk
  have hyT := heq.trans (Ty.rep_eqv T)
  have h1 := Ty.sdepth_le hyT
  rw [Ty.ldepth_rep] at hyd
  have h2 := Ty.rep_paths_length_le hyT (by omega)
  rw [hyp] at h2
  have h3 : l.length < T.rep.paths.length := by
    rw [hl, List.length_filter_lt_length_iff_exists]
    exact ⟨p, hp, by simp⟩
  omega

theorem forall₂_and_of_swap {α : Type*} {R S : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₁ →
      List.Forall₂ (fun a b => R a b ∧ S b a) l₁ l₂
  | [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => .cons ⟨h₁, h₂⟩ (forall₂_and_of_swap t₁ t₂)

theorem forall₂_exists_of_mem {α : Type*} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | [], [], .nil, _, h => by simp at h
  | _ :: _, _ :: _, .cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, by simp, h⟩
    · obtain ⟨b, hb, e⟩ := forall₂_exists_of_mem t a ha
      exact ⟨b, by simp [hb], e⟩

/-- In a reduced type, every path is matched in any equivalent type by a path with
equivalent letters. -/
theorem Ty.Reduced.exists_path {x y : Ty} (hx : x.Reduced) (h : Eqv x y) {p : List Ty × Ty}
    (hp : p ∈ x.paths) : ∃ q ∈ y.paths, q.2 = p.2 ∧
      List.Forall₂ (fun a b => Eqv a b) p.1 q.1 := by
  obtain ⟨q, hq, e₁, f₁⟩ := le_iff_paths.1 h.2 p hp
  obtain ⟨p', hp', e₂, f₂⟩ := le_iff_paths.1 h.1 q hq
  have : p' = p := hx p hp p' hp' ⟨e₂.trans e₁, forall₂_comp f₁ f₂
    fun a _ b _ c _ hab hbc => hab.trans hbc⟩
  subst this
  refine ⟨q, hq, e₁, (forall₂_and_of_swap f₁ f₂).imp fun a b h => ?_⟩
  exact h

/-! ## Folds of meets and joins -/

theorem le_foldr_inter_iff {z b : Ty} {l : List Ty} :
    Le z (l.foldr Ty.inter b) ↔ Le z b ∧ ∀ x ∈ l, Le z x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldr_cons, le_inter_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem foldr_join_le_iff {z b : Ty} {l : List Ty} :
    Le (l.foldr Ty.join b) z ↔ Le b z ∧ ∀ x ∈ l, Le x z := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldr_cons, Ty.join_le_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem measure_foldr_le (μ : Ty → ℕ) {op : Ty → Ty → Ty}
    (hop : ∀ A B, μ (op A B) ≤ max (μ A) (μ B)) {b : Ty} {l : List Ty} {n : ℕ}
    (hb : μ b ≤ n) (hl : ∀ x ∈ l, μ x ≤ n) : μ (l.foldr op b) ≤ n := by
  induction l with
  | nil => simpa using hb
  | cons y l ih =>
    simp only [List.foldr_cons]
    have := hop y (l.foldr op b)
    have := hl y (by simp)
    have := ih fun x hx => hl x (by simp [hx])
    omega

/-! ## The selection lemma

Fix a list of pins and a measure `μ` with `μ (A ∩ B) ≤ max (μ A) (μ B)` and
`μ (A ⊔ B) ≤ max (μ A) (μ B)`. -/

section Selection

variable (μ : Ty → ℕ) (pins : List Ty)

/-- Profiles: (indices of pins below, indices of pins above). -/
abbrev Profile (n : ℕ) := Finset (Fin n) × Finset (Fin n)

/-- The profile of a type with respect to the pins. -/
noncomputable def profile (x : Ty) : Profile pins.length :=
  (Finset.univ.filter fun i => Le (pins.get i) x, Finset.univ.filter fun i => Le x (pins.get i))

/-- Order on profiles: more pins below, fewer pins above. -/
def PLe {n : ℕ} (q q' : Profile n) : Prop := q.1 ⊆ q'.1 ∧ q'.2 ⊆ q.2

theorem PLe.refl {n : ℕ} (q : Profile n) : PLe q q := ⟨subset_refl _, subset_refl _⟩

theorem PLe.trans {n : ℕ} {q q' q'' : Profile n} (h : PLe q q') (h' : PLe q' q'') :
    PLe q q'' := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- The interval `I(q)`: types above the `Lo` pins and below the `Hi` pins of `q`. -/
def InI (q : Profile pins.length) (x : Ty) : Prop :=
  (∀ i ∈ q.1, Le (pins.get i) x) ∧ ∀ i ∈ q.2, Le x (pins.get i)

/-- The interval is nonempty. -/
def NE (q : Profile pins.length) : Prop := ∃ x, InI pins q x

/-- Least measure over the interval (`0` if empty). -/
noncomputable def dmin (q : Profile pins.length) : ℕ := sInf (μ '' {x | InI pins q x})

theorem dmin_le {q : Profile pins.length} {x : Ty} (h : InI pins q x) : dmin μ pins q ≤ μ x :=
  Nat.sInf_le ⟨x, h, rfl⟩

theorem exists_dmin {q : Profile pins.length} (h : NE pins q) :
    ∃ x, InI pins q x ∧ μ x = dmin μ pins q := by
  obtain ⟨x, hx⟩ := h
  have := Nat.sInf_mem (s := μ '' {x | InI pins q x}) ⟨_, x, hx, rfl⟩
  obtain ⟨y, hy, e⟩ := this
  exact ⟨y, hy, e⟩

/-- A measure-minimal element of the interval. -/
noncomputable def xmin (q : Profile pins.length) : Ty :=
  if h : NE pins q then Classical.choose (exists_dmin μ pins h) else .omega

theorem xmin_spec {q : Profile pins.length} (h : NE pins q) :
    InI pins q (xmin μ pins q) ∧ μ (xmin μ pins q) = dmin μ pins q := by
  simp only [xmin, h, ↓reduceDIte]
  exact Classical.choose_spec (exists_dmin μ pins h)

/-- `g_q`: meet of the minimal representatives of the profiles above `q` of no greater
`d`. -/
noncomputable def gsel (q : Profile pins.length) : Ty :=
  ((Finset.univ.filter fun s => NE pins s ∧ PLe q s ∧ dmin μ pins s ≤ dmin μ pins q).toList.map
    (xmin μ pins)).foldr Ty.inter (xmin μ pins q)

/-- `c_q`: join of the `g_r` for profiles below `q` of no greater `d`. -/
noncomputable def csel (q : Profile pins.length) : Ty :=
  ((Finset.univ.filter fun r => NE pins r ∧ PLe r q ∧ dmin μ pins r ≤ dmin μ pins q).toList.map
    (gsel μ pins)).foldr Ty.join (gsel μ pins q)

/-- The selection map `ψ x := c_{p(x)}`. -/
noncomputable def psel (x : Ty) : Ty := csel μ pins (profile pins x)

theorem le_gsel_iff {q : Profile pins.length} {z : Ty} :
    Le z (gsel μ pins q) ↔ Le z (xmin μ pins q) ∧ ∀ s, NE pins s → PLe q s →
      dmin μ pins s ≤ dmin μ pins q → Le z (xmin μ pins s) := by
  rw [gsel, le_foldr_inter_iff]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    forall_exists_index, and_imp]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun s h1 h2 h3 => h₂ _ s h1 h2 h3 rfl⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun x s h1 h2 h3 e => e ▸ h₂ s h1 h2 h3⟩

theorem csel_le_iff {q : Profile pins.length} {z : Ty} :
    Le (csel μ pins q) z ↔ Le (gsel μ pins q) z ∧ ∀ r, NE pins r → PLe r q →
      dmin μ pins r ≤ dmin μ pins q → Le (gsel μ pins r) z := by
  rw [csel, foldr_join_le_iff]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    forall_exists_index, and_imp]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun s h1 h2 h3 => h₂ _ s h1 h2 h3 rfl⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun x s h1 h2 h3 e => e ▸ h₂ s h1 h2 h3⟩

theorem gsel_le_xmin (q : Profile pins.length) : Le (gsel μ pins q) (xmin μ pins q) :=
  ((le_gsel_iff μ pins).1 (Le.refl _)).1

theorem gsel_le_csel (q : Profile pins.length) : Le (gsel μ pins q) (csel μ pins q) :=
  ((csel_le_iff μ pins).1 (Le.refl _)).1

/-- `g_q` lies in the interval of `q`. -/
theorem gsel_mem {q : Profile pins.length} (hq : NE pins q) : InI pins q (gsel μ pins q) := by
  refine ⟨fun i hi => (le_gsel_iff μ pins).2 ⟨(xmin_spec μ pins hq).1.1 i hi,
    fun s hs hqs _ => (xmin_spec μ pins hs).1.1 i (hqs.1 hi)⟩, fun i hi => ?_⟩
  exact (gsel_le_xmin μ pins q).trans ((xmin_spec μ pins hq).1.2 i hi)

/-- `c_q` lies in the interval of `q`. -/
theorem csel_mem {q : Profile pins.length} (hq : NE pins q) : InI pins q (csel μ pins q) := by
  refine ⟨fun i hi => ((gsel_mem μ pins hq).1 i hi).trans (gsel_le_csel μ pins q),
    fun i hi => (csel_le_iff μ pins).2 ⟨(gsel_mem μ pins hq).2 i hi,
      fun r hr hrq _ => (gsel_mem μ pins hr).2 i (hrq.2 hi)⟩⟩

variable {μ} in
theorem measure_gsel_le (hinter : ∀ A B, μ (Ty.inter A B) ≤ max (μ A) (μ B))
    {q : Profile pins.length} (hq : NE pins q) : μ (gsel μ pins q) ≤ dmin μ pins q := by
  refine measure_foldr_le μ hinter (xmin_spec μ pins hq).2.le fun x hx => ?_
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  obtain ⟨s, ⟨hs, -, hd⟩, rfl⟩ := hx
  exact (xmin_spec μ pins hs).2.le.trans hd

variable {μ} in
/-- The measure of `c_q` is the least measure over the interval of `q`. -/
theorem measure_csel (hinter : ∀ A B, μ (Ty.inter A B) ≤ max (μ A) (μ B))
    (hjoin : ∀ A B, μ (Ty.join A B) ≤ max (μ A) (μ B))
    {q : Profile pins.length} (hq : NE pins q) : μ (csel μ pins q) = dmin μ pins q := by
  refine le_antisymm ?_ (dmin_le μ pins (csel_mem μ pins hq))
  refine measure_foldr_le μ hjoin (measure_gsel_le pins hinter hq) fun x hx => ?_
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  obtain ⟨r, ⟨hr, -, hd⟩, rfl⟩ := hx
  exact (measure_gsel_le pins hinter hr).trans hd

theorem gsel_le_gsel {r q : Profile pins.length} (hq : NE pins q) (hrq : PLe r q)
    (hd : dmin μ pins q ≤ dmin μ pins r) : Le (gsel μ pins r) (gsel μ pins q) := by
  have key := (le_gsel_iff μ pins).1 (Le.refl (gsel μ pins r))
  refine (le_gsel_iff μ pins).2 ⟨key.2 q hq hrq hd, fun s hs hqs hds => ?_⟩
  exact key.2 s hs (hrq.trans hqs) (hds.trans hd)

/-- `c` is monotone in the profile. -/
theorem csel_mono {q q' : Profile pins.length} (hq : NE pins q) (hq' : NE pins q')
    (h : PLe q q') :
    Le (csel μ pins q) (csel μ pins q') := by
  have key := (csel_le_iff μ pins).1 (Le.refl (csel μ pins q'))
  have H : ∀ r, NE pins r → PLe r q → dmin μ pins r ≤ dmin μ pins q →
      Le (gsel μ pins r) (csel μ pins q') := by
    intro r hr hrq _
    by_cases hd : dmin μ pins r ≤ dmin μ pins q'
    · exact key.2 r hr (hrq.trans h) hd
    · exact (gsel_le_gsel μ pins hq' (hrq.trans h) (by omega)).trans key.1
  exact (csel_le_iff μ pins).2 ⟨H q hq (PLe.refl q) le_rfl, H⟩

theorem profile_mem (x : Ty) : InI pins (profile pins x) x := by
  constructor <;> intro i hi <;> simpa [profile] using hi

theorem profile_ne (x : Ty) : NE pins (profile pins x) := ⟨x, profile_mem pins x⟩

theorem profile_mono {x x' : Ty} (h : Le x x') : PLe (profile pins x) (profile pins x') := by
  constructor <;> intro i hi <;> simp only [profile, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  exacts [hi.trans h, h.trans hi]

/-- The selection map `ψ` is monotone. -/
theorem psel_mono : MonoMap (psel μ pins) := fun _ _ h =>
  csel_mono μ pins (profile_ne pins _) (profile_ne pins _) (profile_mono pins h)

/-- The selection map `ψ` fixes the pins up to equivalence. -/
theorem psel_pin {π : Ty} (hπ : π ∈ pins) : Eqv (psel μ pins π) π := by
  obtain ⟨i, rfl⟩ := List.get_of_mem hπ
  have hm := csel_mem μ pins (profile_ne pins (pins.get i))
  have h1 : i ∈ (profile pins (pins.get i)).1 := by simp [profile, Le.refl]
  have h2 : i ∈ (profile pins (pins.get i)).2 := by simp [profile, Le.refl]
  exact ⟨hm.2 i h2, hm.1 i h1⟩

variable {μ} in
/-- The selection map `ψ` does not increase the measure. -/
theorem measure_psel_le (hinter : ∀ A B, μ (Ty.inter A B) ≤ max (μ A) (μ B))
    (hjoin : ∀ A B, μ (Ty.join A B) ≤ max (μ A) (μ B)) (k : Ty) :
    μ (psel μ pins k) ≤ μ k := by
  rw [psel, measure_csel pins hinter hjoin (profile_ne pins k)]
  exact dmin_le μ pins (profile_mem pins k)

/-- The realised (nonempty) profiles, as a list. -/
noncomputable def neProfiles : List (Profile pins.length) :=
  (Finset.univ.filter fun q => NE pins q).toList

theorem neProfiles_length : (neProfiles pins).length ≤ 4 ^ pins.length := by
  rw [neProfiles, Finset.length_toList]
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, ← mul_pow]
  rfl

theorem profile_mem_neProfiles (x : Ty) : profile pins x ∈ neProfiles pins := by
  simp [neProfiles, profile_ne]

/-- The image of `ψ` lies in a list of length `≤ 4 ^ |pins|`. -/
theorem psel_image (x : Ty) : psel μ pins x ∈ (neProfiles pins).map (csel μ pins) :=
  List.mem_map_of_mem (profile_mem_neProfiles pins x)

end Selection

/-! ## The transfer lemma

Abstract setting: a measure `μ`, a representative function `rep` with `Eqv (rep T) T` whose
letters have smaller measure, and a selection `ψ` that does not increase the measure. -/

section Transfer

variable (μ : Ty → ℕ) (rep : Ty → Ty) (ψ : Ty → Ty)

/-- The rebuild of `g`: the representative of `g` with each letter `k` replaced by the rebuild
of `ψ k`. (The guard is always satisfied under the hypotheses of the lemmas below; it makes
the recursion terminate along `μ`.) -/
noncomputable def rebuild (g : Ty) : Ty :=
  Ty.interList ((rep g).paths.map fun π =>
    pathTy (π.1.map fun k => if _h : μ (ψ k) < μ g then rebuild (ψ k) else .omega, π.2))
termination_by μ g

variable {μ rep ψ}

/-- The recursive equation of the rebuild. -/
theorem rebuild_eq (hrep : ∀ T, ∀ π ∈ (rep T).paths, ∀ k ∈ π.1, μ k < μ T)
    (hψ : ∀ k, μ (ψ k) ≤ μ k) (g : Ty) :
    rebuild μ rep ψ g = (rep g).mapLetters fun k => rebuild μ rep ψ (ψ k) := by
  rw [rebuild]
  change Ty.mapLetters _ (rep g) = _
  refine Ty.mapLetters_congr fun π hπ k hk => ?_
  have := hrep g π hπ k hk
  have := hψ k
  simp only [show μ (ψ k) < μ g by omega, ↓reduceDIte]

/-- The rebuild is monotone. -/
theorem rebuild_mono (hrepE : ∀ T, Eqv (rep T) T)
    (hrep : ∀ T, ∀ π ∈ (rep T).paths, ∀ k ∈ π.1, μ k < μ T)
    (hψ : ∀ k, μ (ψ k) ≤ μ k) (hψm : MonoMap ψ) :
    MonoMap (rebuild μ rep ψ) := by
  suffices H : ∀ n g g', μ g + μ g' < n → Le g g' →
      Le (rebuild μ rep ψ g) (rebuild μ rep ψ g') from
    fun g g' h => H _ g g' (Nat.lt_succ_self _) h
  intro n
  induction n with
  | zero => intro g g' h; omega
  | succ n ih =>
    intro g g' hn hle
    rw [rebuild_eq hrep hψ g, rebuild_eq hrep hψ g']
    refine Ty.mapLetters_mono_of (((hrepE g).1.trans hle).trans (hrepE g').2) ?_
    intro π hπ π' hπ' a ha b hb hab
    have := hrep g π hπ b hb
    have := hrep g' π' hπ' a ha
    have := hψ a
    have := hψ b
    exact ih _ _ (by omega) (hψm a b hab)

/-- **The transfer lemma.** `c := rebuild ∘ ψ` is monotone and commutes with `mapLetters c` on
the pins. -/
theorem transfer (hrepE : ∀ T, Eqv (rep T) T)
    (hrep : ∀ T, ∀ π ∈ (rep T).paths, ∀ k ∈ π.1, μ k < μ T)
    (hψ : ∀ k, μ (ψ k) ≤ μ k) (hψm : MonoMap ψ) {pins : List Ty}
    (hpin : ∀ π ∈ pins, Eqv (ψ π) π) :
    MonoMap (fun θ => rebuild μ rep ψ (ψ θ)) ∧
      ∀ π ∈ pins, Eqv (rebuild μ rep ψ (ψ π)) (π.mapLetters fun θ => rebuild μ rep ψ (ψ θ)) := by
  have hc : MonoMap (fun θ => rebuild μ rep ψ (ψ θ)) := fun θ θ' h =>
    rebuild_mono hrepE hrep hψ hψm _ _ (hψm θ θ' h)
  refine ⟨hc, fun π hπ => ?_⟩
  rw [rebuild_eq hrep hψ]
  exact Ty.mapLetters_eqv hc ((hrepE _).trans (hpin π hπ))

/-- The letters of the (syntactic) paths of the rebuild of `g` are rebuilds of some `ψ k`. -/
theorem rebuild_letters (hrep : ∀ T, ∀ π ∈ (rep T).paths, ∀ k ∈ π.1, μ k < μ T)
    (hψ : ∀ k, μ (ψ k) ≤ μ k) {g : Ty} {π : List Ty × Ty}
    (hπ : π ∈ (rebuild μ rep ψ g).paths) {k : Ty} (hk : k ∈ π.1) :
    ∃ π₀ ∈ (rep g).paths, ∃ k₀ ∈ π₀.1, k = rebuild μ rep ψ (ψ k₀) := by
  rw [rebuild_eq hrep hψ] at hπ
  obtain ⟨π₀, h₀, rfl⟩ := Ty.mem_paths_mapLetters hπ
  obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.1 hk
  exact ⟨π₀, h₀, k₀, hk₀, rfl⟩

end Transfer

/-! ## The letter bound -/

/-- Letter-subterms of a problem: the `σ` such that `σ → τ` is a subterm of `P`. -/
def Problem.letterSubterms (P : Problem) : List Ty :=
  (P.flatMap fun e => e.1.subterms ++ e.2.subterms).filterMap fun t =>
    match t with
    | .arrow σ _ => some σ
    | _ => none

theorem Problem.mem_letterSubterms {P : Problem} {σ τ : Ty} (h : P.IsSubterm (.arrow σ τ)) :
    σ ∈ P.letterSubterms := by
  obtain ⟨e, he, h⟩ := h
  refine List.mem_filterMap.2 ⟨.arrow σ τ, ?_, rfl⟩
  exact List.mem_flatMap.2 ⟨e, he, List.mem_append.2 h⟩

/-- The pins of a solution: values of the letter-subterms. -/
def Problem.pins (P : Problem) (S : ℕ → Ty) : List Ty := P.letterSubterms.map (·.subst S)

/-- The letter map: the transfer lemma applied to the selection lemma, with the semantic depth
as the measure. -/
noncomputable def letterMap (pins : List Ty) (θ : Ty) : Ty :=
  rebuild Ty.sdepth Ty.rep (psel Ty.sdepth pins) (psel Ty.sdepth pins θ)

/-- The list of values of `letterMap`. -/
noncomputable def letterList (pins : List Ty) : List Ty :=
  ((neProfiles pins).map (csel Ty.sdepth pins)).map
    (rebuild Ty.sdepth Ty.rep (psel Ty.sdepth pins))

/-- The semantic depth strictly decreases along the letters of a representative. -/
theorem rep_letter_lt : ∀ T, ∀ π ∈ (Ty.rep T).paths, ∀ k ∈ π.1, k.sdepth < T.sdepth :=
  fun _ _ hπ _ hk => Ty.sdepth_letter_lt hπ hk

/-- The selection map does not increase the semantic depth. -/
theorem sdepth_psel_le (pins : List Ty) (k : Ty) :
    (psel Ty.sdepth pins k).sdepth ≤ k.sdepth :=
  measure_psel_le pins Ty.sdepth_inter_le Ty.sdepth_join_le k

/-- **The letter bound**, strong form: the letter map `c` is monotone, `S` composed with `c` is
again a unifier, the values of `c` lie in the list `L` of at most `4 ^ n` types, `L` is
closed under taking letters (literally, and up to `≡` for the depth-minimal
representatives), and the semantic depth strictly decreases along letters. -/
theorem letter_bound_strong (P : Problem) (S : ℕ → Ty)
    (hS : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) :
    let c := letterMap (P.pins S)
    let L := letterList (P.pins S)
    MonoMap c ∧
      (∀ e ∈ P, Eqv (e.1.subst fun x => (S x).mapLetters c)
        (e.2.subst fun x => (S x).mapLetters c)) ∧
      (∀ θ, c θ ∈ L) ∧
      L.length ≤ 4 ^ P.letterSubterms.length ∧
      -- literal closure: the syntactic letters of the elements of `L` are in `L`
      (∀ l ∈ L, ∀ π ∈ l.paths, ∀ k ∈ π.1, k ∈ L) ∧
      -- closure up to `≡` for the depth-minimal representatives
      (∀ l ∈ L, ∀ π ∈ (Ty.rep l).paths, ∀ k ∈ π.1, ∃ l' ∈ L, Eqv k l') ∧
      (∀ l ∈ L, ∀ π ∈ (Ty.rep l).paths, ∀ k ∈ π.1, k.sdepth < l.sdepth) := by
  intro c L
  set pins := P.pins S
  have hT := transfer (μ := Ty.sdepth) (rep := Ty.rep) (ψ := psel Ty.sdepth pins)
    Ty.rep_eqv rep_letter_lt (sdepth_psel_le pins) (psel_mono Ty.sdepth pins)
    (pins := pins) fun π hπ => psel_pin Ty.sdepth pins hπ
  have hcL : ∀ θ, c θ ∈ L := fun θ =>
    List.mem_map_of_mem (psel_image Ty.sdepth pins θ)
  have hlit : ∀ l ∈ L, ∀ π ∈ l.paths, ∀ k ∈ π.1, k ∈ L := by
    intro l hl π hπ k hk
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hl
    obtain ⟨-, -, k₀, -, rfl⟩ := rebuild_letters rep_letter_lt (sdepth_psel_le pins) hπ hk
    exact hcL k₀
  refine ⟨hT.1, ?_, hcL, ?_, hlit, ?_, fun l _ => rep_letter_lt l⟩
  · refine P.mapLetters_solves S hT.1 (fun σ τ h => ?_) hS
    exact hT.2 _ (List.mem_map_of_mem (Problem.mem_letterSubterms h))
  · simp only [L, letterList, List.length_map]
    have := neProfiles_length pins
    simpa [pins, Problem.pins] using this
  · intro l hl π hπ k hk
    obtain ⟨q, hq, e, f⟩ := (Ty.rep_reduced l).exists_path (Ty.rep_eqv l) hπ
    obtain ⟨k', hk', hkk'⟩ := forall₂_exists_of_mem f k hk
    exact ⟨k', hlit l hl q hq k' hk', hkk'⟩

/-- **The letter bound.** Any solution `S` of `P` can be transformed by a monotone letter map
`c` into a solution whose letters all lie (up to `≡`) in a letter-closed list `L` of at
most `4 ^ n` types (`n` the number of letter-subterms of `P`), along whose letters the
semantic depth strictly decreases. -/
theorem letter_bound (P : Problem) (S : ℕ → Ty)
    (hS : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) :
    ∃ (c : Ty → Ty) (L : List Ty), MonoMap c ∧
      (∀ e ∈ P, Eqv (e.1.subst fun x => (S x).mapLetters c)
        (e.2.subst fun x => (S x).mapLetters c)) ∧
      (∀ θ, ∃ l ∈ L, Eqv (c θ) l) ∧
      L.length ≤ 4 ^ P.letterSubterms.length ∧
      (∀ l ∈ L, ∀ π ∈ (Ty.rep l).paths, ∀ k ∈ π.1, ∃ l' ∈ L, Eqv k l') ∧
      (∀ l ∈ L, ∀ π ∈ (Ty.rep l).paths, ∀ k ∈ π.1, k.sdepth < l.sdepth) := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := letter_bound_strong P S hS
  exact ⟨_, _, h1, h2, fun θ => ⟨_, h3 θ, Eqv.refl _⟩, h4, h6, h7⟩

end Intersection
