import Resolution.GammaData
import Resolution.MLP
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

/-!
# The abstract problem: base definitions

Given `D : GammaData P`, this file sets up the data over which the abstract problem is posed
and shows that the problem is an instance of the multi-level problems of `Resolution.MLP`.

* The letters of `D.Γ` are indexed by `Fin D.m`, and the *rank* `D.rk i` of a letter is its
  semantic depth. Ranks are below the number of letters (`GammaData.rk_lt`), because the
  letter set is closed under taking letters and the depth decreases along them.
* The *upgrade maps* `D.phi r` send a letter to the least letter of rank `≤ r` above it. They
  are idempotent and compatible (`phi_idem`, `phi_phi`, `phi_phi'`); a letter of rank `r + 1`
  lies below a word iff it lies below the upgrade of the word to rank `r`
  (`le_path_phi_iff`), and a letter of rank `0` lies below no nonempty word
  (`eq_nil_of_rk_zero`). The upgrade maps are the projections of the multi-level problem.
* The abstract problem labels every *entity* (subterm of `P`) and every letter, at every word
  `w` over the letters, with a set of constants: the constants `a` with `S(e) ≤ (w; a)`. The
  labels must satisfy node conditions `APD.NV`, parent–child conditions `APD.CV` and root
  conditions `APD.RV`, which mirror the path characterisation of subtyping. The multi-level
  problem `APD.mlp D` has one lower level per rank, carrying the labels of the letters of
  that rank, read through the upgrade maps.

The file also collects general path lemmas used by the completeness and the realisation in
`Resolution.APD`.
-/

namespace Intersection

open Classical

/-! ## Constants and entities of a problem -/

/-- The constants occurring in a type (with repetitions). -/
def Ty.consts (T : Ty) : List ℕ :=
  T.subterms.filterMap fun t => match t with
    | .const c => some c
    | _ => none

/-- The constants occurring in a problem (without repetitions). -/
def Problem.consts (P : Problem) : List ℕ :=
  (P.flatMap fun e => e.1.consts ++ e.2.consts).dedup

/-- The entities of a problem: all subterms of all equation sides (without repetitions). -/
def Problem.entities (P : Problem) : List Ty :=
  (P.flatMap fun e => e.1.subterms ++ e.2.subterms).dedup

theorem Problem.consts_nodup (P : Problem) : P.consts.Nodup := List.nodup_dedup _

theorem Problem.entities_nodup (P : Problem) : P.entities.Nodup := List.nodup_dedup _

theorem Problem.mem_entities {P : Problem} {σ : Ty} : σ ∈ P.entities ↔ P.IsSubterm σ := by
  simp [Problem.entities, Problem.IsSubterm, List.mem_dedup, List.mem_flatMap]

theorem Problem.IsSubterm.trans {P : Problem} {σ τ : Ty} (h : σ ∈ τ.subterms)
    (hτ : P.IsSubterm τ) : P.IsSubterm σ := by
  obtain ⟨e, he, h'⟩ := hτ
  exact ⟨e, he, h'.imp (Ty.mem_subterms_trans h) (Ty.mem_subterms_trans h)⟩

theorem Problem.const_mem_consts {P : Problem} {c : ℕ} (h : P.IsSubterm (.const c)) :
    c ∈ P.consts := by
  obtain ⟨e, he, h'⟩ := h
  simp only [Problem.consts, List.mem_dedup, List.mem_flatMap, List.mem_append]
  refine ⟨e, he, ?_⟩
  rcases h' with h' | h'
  · exact Or.inl (List.mem_filterMap.2 ⟨_, h', rfl⟩)
  · exact Or.inr (List.mem_filterMap.2 ⟨_, h', rfl⟩)

theorem Problem.entities_left {P : Problem} {σ τ : Ty} (h : Ty.arrow σ τ ∈ P.entities ∨
    Ty.inter σ τ ∈ P.entities) : σ ∈ P.entities := by
  rcases h with h | h <;>
  exact Problem.mem_entities.2 ((Problem.mem_entities.1 h).trans (by simp [Ty.subterms,
    Ty.mem_subterms_self]))

theorem Problem.entities_right {P : Problem} {σ τ : Ty} (h : Ty.arrow σ τ ∈ P.entities ∨
    Ty.inter σ τ ∈ P.entities) : τ ∈ P.entities := by
  rcases h with h | h <;>
  exact Problem.mem_entities.2 ((Problem.mem_entities.1 h).trans (by simp [Ty.subterms,
    Ty.mem_subterms_self]))

/-! ## General path lemmas -/

theorem paths_pathTy_const (ls : List Ty) (c : ℕ) :
    (pathTy (ls, .const c)).paths = [(ls, .const c)] := Ty.paths_pathTy rfl

/-- The path criterion against a single path. -/
theorem le_pathTy_const_iff {T : Ty} {ls : List Ty} {c : ℕ} :
    Le T (pathTy (ls, .const c)) ↔
      ∃ π ∈ T.paths, π.2 = .const c ∧ List.Forall₂ (fun a b => Le a b) ls π.1 := by
  rw [le_iff_paths, paths_pathTy_const]
  simp

theorem length_of_le_pathTy {T : Ty} {ls : List Ty} {c : ℕ}
    (h : Le T (pathTy (ls, .const c))) : ∃ π ∈ T.paths, π.1.length = ls.length := by
  obtain ⟨π, hπ, -, f⟩ := le_pathTy_const_iff.1 h
  exact ⟨π, hπ, f.length_eq.symm⟩

theorem pathTy_cons (k : Ty) (ls : List Ty) (a : Ty) :
    pathTy (k :: ls, a) = .arrow k (pathTy (ls, a)) := rfl

theorem not_omega_le_pathTy (ls : List Ty) (c : ℕ) : ¬ Le .omega (pathTy (ls, .const c)) := by
  rw [omega_le_iff, paths_pathTy_const]; simp

theorem le_inter_pathTy_iff {X Y : Ty} {ls : List Ty} {c : ℕ} :
    Le (.inter X Y) (pathTy (ls, .const c)) ↔
      Le X (pathTy (ls, .const c)) ∨ Le Y (pathTy (ls, .const c)) := by
  simp only [le_pathTy_const_iff, Ty.paths, List.mem_append]
  constructor
  · rintro ⟨π, hπ | hπ, h⟩
    exacts [Or.inl ⟨π, hπ, h⟩, Or.inr ⟨π, hπ, h⟩]
  · rintro (⟨π, hπ, h⟩ | ⟨π, hπ, h⟩)
    exacts [⟨π, Or.inl hπ, h⟩, ⟨π, Or.inr hπ, h⟩]

theorem le_arrow_pathTy_iff {X Y H : Ty} {ls : List Ty} {c : ℕ} :
    Le (.arrow X Y) (pathTy (H :: ls, .const c)) ↔ Le H X ∧ Le Y (pathTy (ls, .const c)) := by
  rw [pathTy_cons]
  refine ⟨fun h => Le.arrow_inv h (by simp [paths_pathTy_const]), fun h => Le.arrow h.1 h.2⟩

theorem not_arrow_le_const {X Y : Ty} {c : ℕ} : ¬ Le (.arrow X Y) (pathTy ([], .const c)) := by
  intro h
  obtain ⟨π, hπ, e⟩ := length_of_le_pathTy h
  simp only [Ty.paths, List.mem_map] at hπ
  obtain ⟨π', -, rfl⟩ := hπ
  simp at e

theorem not_const_le_cons {c c' : ℕ} {H : Ty} {ls : List Ty} :
    ¬ Le (.const c) (pathTy (H :: ls, .const c')) := by
  intro h
  obtain ⟨π, hπ, e⟩ := length_of_le_pathTy h
  simp only [Ty.paths, List.mem_singleton] at hπ
  subst hπ
  simp at e

theorem const_le_const_iff {c c' : ℕ} : Le (.const c) (pathTy ([], .const c')) ↔ c = c' := by
  change Le (.const c) (.const c') ↔ _
  rw [le_const_iff_mem]
  simp [Ty.paths, eq_comm]

theorem forall₂_imp_mem' {α β : Type*} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a ∈ l₁, ∀ b ∈ l₂, R a b → S a b) → List.Forall₂ S l₁ l₂
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h t, H =>
    .cons (H _ (by simp) _ (by simp) h)
      (forall₂_imp_mem' t fun a ha b hb => H a (by simp [ha]) b (by simp [hb]))

theorem interList_congr {α : Type*} {f g : α → Ty} :
    ∀ {l : List α}, (∀ x ∈ l, Eqv (f x) (g x)) →
      Eqv (Ty.interList (l.map f)) (Ty.interList (l.map g))
  | [], _ => Eqv.refl _
  | x :: l, h => by
    simp only [List.map_cons, Ty.interList]
    exact Eqv.inter (h x (by simp)) (interList_congr fun y hy => h y (by simp [hy]))

theorem eqv_of_forall_le_iff {A B : Ty} (h : ∀ X, Le X A ↔ Le X B) : Eqv A B :=
  ⟨(h A).1 (Le.refl A), (h B).2 (Le.refl B)⟩

theorem sdepth_omega : Ty.omega.sdepth = 0 := by
  have := Ty.sdepth_le_ldepth Ty.omega
  simp [Ty.ldepth] at this
  exact this

/-- A type of positive semantic depth has a letter (of its representative) of depth one
less. -/
theorem Ty.exists_letter_sdepth {T : Ty} {d : ℕ} (hT : T.sdepth = d + 1) :
    ∃ π ∈ T.rep.paths, ∃ k ∈ π.1, k.sdepth = d := by
  by_contra hne
  push Not at hne
  have hlt : ∀ π ∈ T.rep.paths, ∀ k ∈ π.1, k.sdepth + 1 ≤ d := by
    intro π hπ k hk
    have h2 := Ty.sdepth_letter_lt hπ hk
    have h3 := hne π hπ k hk
    omega
  set x := Ty.interList (T.rep.paths.map fun π => pathTy (π.1.map Ty.rep, π.2))
  have hx : Eqv x T := by
    refine (interList_congr (g := pathTy) fun π _ => ?_).trans
      ((eqv_interList_paths T.rep).symm.trans (Ty.rep_eqv T))
    obtain ⟨l, a⟩ := π
    constructor
    · refine pathTy_le_pathTy a ?_
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.2 fun k _ => (Ty.rep_eqv k).2
    · refine pathTy_le_pathTy a ?_
      rw [List.forall₂_map_left_iff]
      exact List.forall₂_same.2 fun k _ => (Ty.rep_eqv k).1
  have hd : x.ldepth ≤ d := by
    refine Ty.ldepth_interList_le.2 fun y hy => ?_
    obtain ⟨π, hπ, rfl⟩ := List.mem_map.1 hy
    refine (Ty.ldepth_pathTy_le (Ty.atom_of_mem_paths hπ).2).2 fun k hk => ?_
    obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.1 hk
    rw [Ty.ldepth_rep]
    exact hlt π hπ k₀ hk₀
  have := Ty.sdepth_le hx
  omega

/-! ## Indexing the letter set -/

namespace GammaData

variable {P : Problem} (D : GammaData P)

/-- The number of letters. -/
abbrev m : ℕ := D.Γ.length

/-- The letter with index `i`. -/
def G (i : Fin D.m) : Ty := D.Γ.get i

/-- The rank of a letter: its semantic depth. -/
noncomputable def rk (i : Fin D.m) : ℕ := (D.G i).sdepth

theorem G_mem (i : Fin D.m) : D.G i ∈ D.Γ := List.get_mem _ _

theorem exists_G {g : Ty} (h : g ∈ D.Γ) : ∃ i, D.G i = g := List.get_of_mem h

/-- Equivalent letters are equal, since `Γ` is deduplicated. -/
theorem eq_of_eqv {i j : Fin D.m} (h : Eqv (D.G i) (D.G j)) : i = j := by
  have hp := List.pairwise_iff_get.1 D.nodup
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (hp i j hij)
  · exact hij
  · exact absurd h.symm (hp j i hij)

theorem exists_eqv_G {g : Ty} (h : g ∈ D.Γ) {T : Ty} (hT : Eqv T g) : ∃ i, Eqv T (D.G i) := by
  obtain ⟨i, rfl⟩ := D.exists_G h
  exact ⟨i, hT⟩

/-- Meets of letters are letters (up to `≡`). -/
theorem exists_eqv_interList (l : List (Fin D.m)) :
    ∃ j, Eqv (Ty.interList (l.map D.G)) (D.G j) := by
  induction l with
  | nil =>
    obtain ⟨g, hg, e⟩ := D.omega_mem
    exact D.exists_eqv_G hg e.symm
  | cons i l ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hk, e⟩ := D.inter_mem _ (D.G_mem i) _ (D.G_mem j)
    obtain ⟨k', hk'⟩ := D.exists_eqv_G hk e
    exact ⟨k', (Eqv.inter (Eqv.refl _) hj).trans hk'⟩

theorem sdepth_interList_le {l : List Ty} {r : ℕ} (h : ∀ x ∈ l, x.sdepth ≤ r) :
    (Ty.interList l).sdepth ≤ r := by
  induction l with
  | nil => simp [Ty.interList, sdepth_omega]
  | cons x l ih =>
    have := Ty.sdepth_inter_le x (Ty.interList l)
    have := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    simp only [Ty.interList]
    omega

/-! ## Ranks are below the number of letters -/

/-- Every rank below the rank of a letter is the rank of some letter. -/
theorem exists_rk_of_le {i : Fin D.m} : ∀ d, d ≤ D.rk i → ∃ j, D.rk j = d := by
  suffices H : ∀ k, k ≤ D.rk i → ∃ j, D.rk j = D.rk i - k by
    intro d hd
    obtain ⟨j, hj⟩ := H (D.rk i - d) (Nat.sub_le _ _)
    exact ⟨j, by rw [hj]; omega⟩
  intro k
  induction k with
  | zero => exact fun _ => ⟨i, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨j, hj⟩ := ih (by omega)
    have hj' : (D.G j).sdepth = (D.rk i - (k + 1)) + 1 := by
      rw [← rk, hj]; omega
    obtain ⟨π, hπ, l, hl, e⟩ := Ty.exists_letter_sdepth hj'
    obtain ⟨g', hg', e'⟩ := D.rep_mem _ (D.G_mem j) π hπ l hl
    obtain ⟨j', hj''⟩ := D.exists_eqv_G hg' e'
    exact ⟨j', by rw [rk, ← Ty.sdepth_congr hj'', e]⟩

/-- Every rank is smaller than the number of letters. -/
theorem rk_lt (i : Fin D.m) : D.rk i < D.m := by
  have H : ∀ d : Fin (D.rk i + 1), ∃ j, D.rk j = d.val := fun d =>
    D.exists_rk_of_le (i := i) d.val (by omega)
  choose f hf using H
  have hinj : Function.Injective f := fun d d' e => Fin.ext (by rw [← hf d, ← hf d', e])
  have := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin, Fintype.card_fin] at this
  omega

/-! ## The upgrade maps -/

/-- The defining property of `phi r i`: the least letter of rank `≤ r` above `G i`. -/
def PhiSpec (r : ℕ) (i j : Fin D.m) : Prop :=
  D.rk j ≤ r ∧ Le (D.G i) (D.G j) ∧ ∀ k, D.rk k ≤ r → Le (D.G i) (D.G k) → Le (D.G j) (D.G k)

theorem exists_phi (r : ℕ) (i : Fin D.m) : ∃ j, D.PhiSpec r i j := by
  set l := (List.finRange D.m).filter fun k => decide (D.rk k ≤ r ∧ Le (D.G i) (D.G k))
  have hl : ∀ {k}, k ∈ l ↔ D.rk k ≤ r ∧ Le (D.G i) (D.G k) := by
    intro k; simp [l]
  obtain ⟨j, hj⟩ := D.exists_eqv_interList l
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [rk, ← Ty.sdepth_congr hj]
    refine sdepth_interList_le fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact (hl.1 hk).1
  · refine Le.trans (le_interList_iff.2 fun x hx => ?_) hj.1
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact (hl.1 hk).2
  · intro k hk hik
    exact hj.2.trans (interList_le_of_mem (List.mem_map_of_mem (hl.2 ⟨hk, hik⟩)))

theorem PhiSpec.unique {r : ℕ} {i j j' : Fin D.m} (h : D.PhiSpec r i j)
    (h' : D.PhiSpec r i j') : j = j' :=
  D.eq_of_eqv ⟨h.2.2 j' h'.1 h'.2.1, h'.2.2 j h.1 h.2.1⟩

/-- The upgrade map to rank `≤ r`: the least letter of rank `≤ r` above `G i`. -/
noncomputable def phi (r : ℕ) (i : Fin D.m) : Fin D.m := Classical.choose (D.exists_phi r i)

theorem phi_spec (r : ℕ) (i : Fin D.m) : D.PhiSpec r i (D.phi r i) :=
  Classical.choose_spec (D.exists_phi r i)

theorem le_phi (r : ℕ) (i : Fin D.m) : Le (D.G i) (D.G (D.phi r i)) := (D.phi_spec r i).2.1

theorem rk_phi_le (r : ℕ) (i : Fin D.m) : D.rk (D.phi r i) ≤ r := (D.phi_spec r i).1

theorem phi_le {r : ℕ} {i k : Fin D.m} (hk : D.rk k ≤ r) (h : Le (D.G i) (D.G k)) :
    Le (D.G (D.phi r i)) (D.G k) := (D.phi_spec r i).2.2 k hk h

theorem phi_of_rk_le {r : ℕ} {i : Fin D.m} (h : D.rk i ≤ r) : D.phi r i = i :=
  PhiSpec.unique D (D.phi_spec r i) ⟨h, Le.refl _, fun _ _ hk => hk⟩

theorem phi_idem (r : ℕ) (i : Fin D.m) : D.phi r (D.phi r i) = D.phi r i :=
  D.phi_of_rk_le (D.rk_phi_le r i)

/-- Upgrading to rank `s ≤ r` after upgrading to rank `r` is upgrading to rank `s`. -/
theorem phi_phi {s r : ℕ} (hsr : s ≤ r) (i : Fin D.m) : D.phi s (D.phi r i) = D.phi s i := by
  refine PhiSpec.unique D ⟨D.rk_phi_le s _, (D.le_phi r i).trans (D.le_phi s _),
    fun k hk hik => ?_⟩ (D.phi_spec s i)
  exact D.phi_le hk (D.phi_le (by omega) hik)

/-- Upgrading to rank `r ≥ s` after upgrading to rank `s` does nothing. -/
theorem phi_phi' {s r : ℕ} (hsr : s ≤ r) (i : Fin D.m) : D.phi r (D.phi s i) = D.phi s i :=
  D.phi_of_rk_le ((D.rk_phi_le s i).trans hsr)

/-- A letter of rank `r + 1` lies below a word iff it lies below the upgrade of the word to
rank `r`. -/
theorem le_path_phi_iff {g : Fin D.m} {r : ℕ} (hg : D.rk g = r + 1) (w : List (Fin D.m))
    (c : ℕ) : Le (D.G g) (pathTy (w.map D.G, .const c)) ↔
      Le (D.G g) (pathTy ((w.map (D.phi r)).map D.G, .const c)) := by
  constructor
  · intro h
    have h' := (Ty.rep_eqv (D.G g)).1.trans h
    obtain ⟨π, hπ, e, f⟩ := le_pathTy_const_iff.1 h'
    refine (Ty.rep_eqv (D.G g)).2.trans (le_pathTy_const_iff.2 ⟨π, hπ, e, ?_⟩)
    rw [List.map_map, List.forall₂_map_left_iff]
    rw [List.forall₂_map_left_iff] at f
    refine forall₂_imp_mem' f fun x _ k hk hxk => ?_
    obtain ⟨g', hg', e'⟩ := D.rep_mem _ (D.G_mem g) π hπ k hk
    obtain ⟨j, hj⟩ := D.exists_eqv_G hg' e'
    have hlt := Ty.sdepth_letter_lt hπ hk
    have hrk : D.rk j ≤ r := by
      rw [rk, ← Ty.sdepth_congr hj]; rw [rk] at hg; omega
    exact (D.phi_le hrk (hxk.trans hj.1)).trans hj.2
  · intro h
    refine h.trans (pathTy_le_pathTy _ ?_)
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun x _ => D.le_phi r x

/-- A letter of rank `0` lies below no nonempty word. -/
theorem eq_nil_of_rk_zero {g : Fin D.m} (hg : D.rk g = 0) {w : List (Fin D.m)} {c : ℕ}
    (h : Le (D.G g) (pathTy (w.map D.G, .const c))) : w = [] := by
  have h' := (Ty.rep_eqv (D.G g)).1.trans h
  obtain ⟨π, hπ, -, f⟩ := le_pathTy_const_iff.1 h'
  cases hl : π.1 with
  | nil => rw [hl] at f; simpa using f.length_eq
  | cons k l =>
    have := Ty.sdepth_letter_lt hπ (k := k) (by rw [hl]; simp)
    rw [rk] at hg
    omega

end GammaData

/-! ## The multi-level problem -/

namespace APD

variable {P : Problem} (D : GammaData P)

/-- Label sets: sets of (indices of) constants of `P`. -/
abbrev Lab (P : Problem) := Finset (Fin P.consts.length)

/-- Top-level states: labels of all entities and all letters. -/
abbrev State (D : GammaData P) := Fin P.entities.length ⊕ Fin D.m → Lab P

/-- Node conditions at a word: the label of an intersection is the union of the labels of its
parts, `ω` has the empty label, the two sides of an equation have equal labels, the domain of
an arrow has the label of the letter equivalent to its value, labels are antitone in the
letters, and the labels of the letters of rank `r + 1` are read from level `r`. -/
def NV (q : State D) (ι : Fin D.m → Fin D.m → Lab P) : Prop :=
  (∀ e e₁ e₂, P.entities.get e = .inter (P.entities.get e₁) (P.entities.get e₂) →
      q (.inl e) = q (.inl e₁) ∪ q (.inl e₂)) ∧
  (∀ e, P.entities.get e = .omega → q (.inl e) = ∅) ∧
  (∀ p ∈ P, ∀ e₁ e₂, P.entities.get e₁ = p.1 → P.entities.get e₂ = p.2 →
      q (.inl e₁) = q (.inl e₂)) ∧
  (∀ e e₁ e₂ j, P.entities.get e = .arrow (P.entities.get e₁) (P.entities.get e₂) →
      Eqv ((P.entities.get e₁).subst D.S) (D.G j) → q (.inl e₁) = q (.inr j)) ∧
  (∀ i j, Le (D.G i) (D.G j) → q (.inr j) ⊆ q (.inr i)) ∧
  (∀ (r : Fin D.m) i, D.rk i = r.val + 1 → q (.inr i) = ι r i) ∧
  (∀ (r : Fin D.m) i, D.rk i ≠ r.val + 1 → ι r i = ∅)

/-- Parent–child conditions (`q` at `w`, `q'` at `h :: w`): the label of an arrow `σ → τ` at
`h :: w` is the label of `τ` at `w` if `h` is below the letter of `σ`, and empty otherwise;
constants and letters of rank `0` have empty labels at nonempty words. -/
def CV (q : State D) (h : Fin D.m) (q' : State D) : Prop :=
  (∀ e e₁ e₂ j, P.entities.get e = .arrow (P.entities.get e₁) (P.entities.get e₂) →
      Eqv ((P.entities.get e₁).subst D.S) (D.G j) →
      q' (.inl e) = if Le (D.G h) (D.G j) then q (.inl e₂) else ∅) ∧
  (∀ e c, P.entities.get e = .const c → q' (.inl e) = ∅) ∧
  (∀ i, D.rk i = 0 → q' (.inr i) = ∅)

/-- Root conditions: arrows have empty labels at the empty word, and a constant is labelled by
itself. -/
def RV (q : State D) : Prop :=
  (∀ e σ τ, P.entities.get e = .arrow σ τ → q (.inl e) = ∅) ∧
  (∀ e k, P.entities.get e = .const (P.consts.get k) → q (.inl e) = {k})

/-- The abstract problem as a multi-level problem: the alphabet is the letters, there is one
lower level per rank, the projections are the upgrade maps, and the top states are the
labellings of the entities and the letters. -/
noncomputable def mlp : MLP where
  Γ := Fin D.m
  R := D.m
  φ r := D.phi r.val
  F _ := Fin D.m → Lab P
  zF _ := fun _ => ∅
  Q := State D
  zQ := fun _ => ∅
  Δ q ι ch := NV D q ι ∧ ∀ h, CV D q h (ch h)
  root q := RV D q
  φ_idem r h := D.phi_idem r.val h
  φ_comp s r hsr h := D.phi_phi (Fin.le_def.1 hsr) h
  φ_comp' s r hsr h := D.phi_phi' (Fin.le_def.1 hsr) h
  Δ_zero := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => ⟨?_, ?_, ?_⟩⟩ <;> intros <;> simp

end APD

end Intersection
