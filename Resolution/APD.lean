import Resolution.APDBase
import Mathlib.Tactic.GCongr

/-!
# The abstract problem: completeness and realisation

The two directions of the correspondence between unifiers and solutions of the abstract
problem `APD.mlp D`.

* *Completeness of the abstract problem* (`APD.complete`). From the unifier `D.S` packaged in
  `D : GammaData P`, the canonical labelling `APD.lab T w` (the constants `a` with
  `T ≤ (w; a)`) of all entities and letters is a solution of `APD.mlp D`, zero beyond the
  total path length `APD.compN D`.
* *The realisation* (`APD.realize`). Conversely, a solution of `APD.mlp D` of support `N`
  yields a ground unifier of `P` over the constants of `P`. The realised letters `APD.T` are
  defined by recursion on the rank as the meet (`meetOf`) of the paths `(w; a)` over the words
  `w` of lower rank and the stored labels `a`; the realised entities `APD.U` are the same meet
  over all words; and the realised substitution `APD.Sr` sends a variable to the realised
  entity of that variable. The realised letters are monotone in the letters (`APD.T_mono`),
  and the realised substitution agrees with the realised entities on every entity
  (`APD.subst_eqv_U`). All values have size at most `realizeBound N |Γ| |consts|`.

The size bound `realizeBound` and the generic tools (`Ty.GroundOver`, `words`, `meetOf`) are
defined in between.
-/

namespace Intersection

open Classical

namespace APD

variable {P : Problem} (D : GammaData P)

/-! ## Completeness -/

/-- The label of a type at a word: the constants `c` with `T ≤ (w; c)`. -/
noncomputable def lab (T : Ty) (w : List (Fin D.m)) : Lab P :=
  Finset.univ.filter fun k => Le T (pathTy (w.map D.G, .const (P.consts.get k)))

/-- The type of an entity or letter under `D.S`. -/
def ent : Fin P.entities.length ⊕ Fin D.m → Ty
  | .inl e => (P.entities.get e).subst D.S
  | .inr i => D.G i

theorem mem_lab {T : Ty} {w : List (Fin D.m)} {k : Fin P.consts.length} :
    k ∈ lab D T w ↔ Le T (pathTy (w.map D.G, .const (P.consts.get k))) := by
  simp [lab]

theorem lab_congr {T T' : Ty} (h : Eqv T T') (w : List (Fin D.m)) : lab D T w = lab D T' w := by
  ext k; rw [mem_lab, mem_lab]
  exact ⟨fun h' => h.2.trans h', fun h' => h.1.trans h'⟩

theorem lab_inter (X Y : Ty) (w : List (Fin D.m)) :
    lab D (.inter X Y) w = lab D X w ∪ lab D Y w := by
  ext k; rw [Finset.mem_union, mem_lab, mem_lab, mem_lab, le_inter_pathTy_iff]

theorem lab_omega (w : List (Fin D.m)) : lab D .omega w = ∅ := by
  ext k; rw [mem_lab]; simp [not_omega_le_pathTy]

theorem lab_arrow_cons {X Y : Ty} {j : Fin D.m} (hX : Eqv X (D.G j)) (h : Fin D.m)
    (w : List (Fin D.m)) :
    lab D (.arrow X Y) (h :: w) = if Le (D.G h) (D.G j) then lab D Y w else ∅ := by
  ext k
  rw [mem_lab, List.map_cons, le_arrow_pathTy_iff]
  split_ifs with hh
  · rw [mem_lab]; exact ⟨fun h' => h'.2, fun h' => ⟨hh.trans hX.2, h'⟩⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    exact fun h' => absurd (h'.trans hX.1) hh

theorem lab_arrow_nil (X Y : Ty) : lab D (.arrow X Y) [] = ∅ := by
  ext k; rw [mem_lab]; simp [not_arrow_le_const]

theorem lab_const_cons (c : ℕ) (h : Fin D.m) (w : List (Fin D.m)) :
    lab D (.const c) (h :: w) = ∅ := by
  ext k; rw [mem_lab, List.map_cons]; simp [not_const_le_cons]

theorem lab_const_nil (k : Fin P.consts.length) : lab D (.const (P.consts.get k)) [] = {k} := by
  ext k'
  rw [mem_lab, List.map_nil, const_le_const_iff, Finset.mem_singleton,
    P.consts_nodup.get_inj_iff, eq_comm]

/-- The sum of the lengths of the paths of a type. -/
def plen (T : Ty) : ℕ := (T.paths.map fun π => π.1.length).sum

theorem le_sum_of_mem' {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp; omega

/-- Labels vanish beyond the total path length. -/
theorem lab_eq_empty {T : Ty} {w : List (Fin D.m)} (hw : plen T < w.length) :
    lab D T w = ∅ := by
  ext k
  simp only [mem_lab, Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨π, hπ, e⟩ := length_of_le_pathTy h
  have := le_sum_of_mem' (List.mem_map_of_mem (f := fun π : List Ty × Ty => π.1.length) hπ)
  simp only [List.length_map] at e
  rw [plen] at hw
  omega

/-- The support bound used for the canonical solution. -/
noncomputable def compN : ℕ :=
  ((P.entities.map (·.subst D.S) ++ D.Γ).map plen).sum + 1

theorem ent_mem (x : Fin P.entities.length ⊕ Fin D.m) :
    ent D x ∈ P.entities.map (·.subst D.S) ++ D.Γ := by
  cases x with
  | inl e => exact List.mem_append_left _ (List.mem_map_of_mem (List.get_mem _ _))
  | inr i => exact List.mem_append_right _ (D.G_mem i)

/-- The canonical top labelling. -/
noncomputable def canonL (w : List (Fin D.m)) : State D := fun x => lab D (ent D x) w

/-- The canonical lower labellings. -/
noncomputable def canonF (r : Fin D.m) (w : List (Fin D.m)) : Fin D.m → Lab P :=
  fun i => if D.rk i = r.val + 1 then lab D (D.G i) w else ∅

/-- The canonical labelling satisfies the node conditions. -/
theorem canon_nv (w : List (Fin D.m)) :
    NV D (canonL D w) (fun r => canonF D r (w.map (D.phi r.val))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e e₁ e₂ he
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_inter]
  · intro e he
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_omega]
  · intro p hp e₁ e₂ h₁ h₂
    simp only [canonL, ent]
    rw [h₁, h₂]
    exact lab_congr D (D.solves p hp) w
  · intro e e₁ e₂ j _ hj
    exact lab_congr D hj w
  · intro i j hij k hk
    exact (mem_lab D).2 (hij.trans ((mem_lab D).1 hk))
  · intro r i hi
    simp only [canonL, canonF, ent, hi, ↓reduceIte]
    ext k
    rw [mem_lab, mem_lab, D.le_path_phi_iff hi]
  · intro r i hi
    simp only [canonF, hi, ↓reduceIte]

/-- The canonical labelling satisfies the parent–child conditions. -/
theorem canon_cv (w : List (Fin D.m)) (h : Fin D.m) :
    CV D (canonL D w) h (canonL D (h :: w)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e e₁ e₂ j he hj
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_arrow_cons D hj]
  · intro e c he
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_const_cons]
  · intro i hi
    ext k
    simp only [canonL, ent, Finset.notMem_empty, iff_false]
    rw [mem_lab]
    intro h'
    exact List.cons_ne_nil _ _ (D.eq_nil_of_rk_zero hi h')

/-- The canonical labelling satisfies the root conditions. -/
theorem canon_rv : RV D (canonL D []) := by
  refine ⟨?_, ?_⟩
  · intro e σ τ he
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_arrow_nil]
  · intro e k he
    simp only [canonL, ent]
    rw [he, Ty.subst, lab_const_nil]

theorem canon_supp (w : List (Fin D.m)) (hw : compN D ≤ w.length) :
    canonL D w = (fun _ => ∅) ∧ ∀ r, canonF D r w = fun _ => ∅ := by
  have H : ∀ x, plen (ent D x) < w.length := fun x => by
    have := le_sum_of_mem' (List.mem_map_of_mem (f := plen) (ent_mem D x))
    rw [compN] at hw
    omega
  refine ⟨funext fun x => lab_eq_empty D (H x), fun r => funext fun i => ?_⟩
  simp only [canonF]
  split_ifs
  · exact lab_eq_empty D (H (.inr i))
  · rfl

/-- The canonical solution. -/
noncomputable def canon : (mlp D).Sol (compN D) where
  f := canonF D
  L := canonL D
  step w := ⟨canon_nv D w, canon_cv D w⟩
  root := canon_rv D
  supp w hw := canon_supp D w hw

/-- **Completeness of the abstract problem.** The abstract problem of a `GammaData` has a
solution. -/
theorem complete (D : GammaData P) : ∃ N, Nonempty ((mlp D).Sol N) :=
  ⟨_, ⟨canon D⟩⟩
end APD

/-! ## Generic tools for the realisation -/

/-- Ground types over a list of constants: no variables, all constants in `A`. -/
def Ty.GroundOver (A : List ℕ) : Ty → Prop
  | .const c => c ∈ A
  | .var _ => False
  | .omega => True
  | .arrow σ τ => σ.GroundOver A ∧ τ.GroundOver A
  | .inter σ τ => σ.GroundOver A ∧ τ.GroundOver A

theorem groundOver_interList {A : List ℕ} : ∀ {l : List Ty}, (∀ x ∈ l, x.GroundOver A) →
    (Ty.interList l).GroundOver A
  | [], _ => trivial
  | x :: l, h => ⟨h x (by simp), groundOver_interList fun y hy => h y (by simp [hy])⟩

theorem groundOver_pathTy {A : List ℕ} {c : ℕ} (hc : c ∈ A) : ∀ {ls : List Ty},
    (∀ x ∈ ls, x.GroundOver A) → (pathTy (ls, .const c)).GroundOver A
  | [], _ => hc
  | x :: ls, h => by
    rw [pathTy_cons]
    exact ⟨h x (by simp), groundOver_pathTy hc fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem size_interList_le {B : ℕ} : ∀ {l : List Ty}, (∀ x ∈ l, x.size ≤ B) →
    (Ty.interList l).size ≤ l.length * (B + 1) + 1
  | [], _ => by simp [Ty.interList, Ty.size]
  | x :: l, h => by
    have h1 := h x (by simp)
    have h2 := size_interList_le (l := l) fun y hy => h y (by simp [hy])
    simp only [Ty.interList, Ty.size, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem size_pathTy_le {M c : ℕ} : ∀ {ls : List Ty}, (∀ x ∈ ls, x.size ≤ M) →
    (pathTy (ls, .const c)).size ≤ ls.length * (M + 1) + 1
  | [], _ => by simp [pathTy, Ty.size]
  | x :: ls, h => by
    have h1 := h x (by simp)
    have h2 := size_pathTy_le (c := c) (ls := ls) fun y hy => h y (by simp [hy])
    rw [pathTy_cons]
    simp only [Ty.size, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem length_flatMap_le {α β : Type*} {f : α → List β} {b : ℕ} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).length ≤ b) → (l.flatMap f).length ≤ l.length * b
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x (by simp)
    have h2 := length_flatMap_le (l := l) fun y hy => h y (by simp [hy])
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

/-- All words of length `< n` over the letters `L`. -/
def words {α : Type*} (L : List α) : ℕ → List (List α)
  | 0 => []
  | n + 1 => [] :: L.flatMap fun h => (words L n).map (h :: ·)

theorem mem_words {α : Type*} {L : List α} : ∀ {n : ℕ} {w : List α},
    w ∈ words L n ↔ w.length < n ∧ ∀ x ∈ w, x ∈ L
  | 0, w => by simp [words]
  | n + 1, [] => by simp [words]
  | n + 1, h :: w => by
    simp only [words, List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_map,
      List.cons.injEq, false_or, List.length_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h', hh', w', hw', rfl, rfl⟩
      have := (mem_words (n := n)).1 hw'
      exact ⟨by omega, hh', this.2⟩
    · rintro ⟨hl, hh, hw⟩
      exact ⟨h, hh, w, (mem_words (n := n)).2 ⟨by omega, hw⟩, rfl, rfl⟩

theorem length_words_le {α : Type*} (L : List α) : ∀ n, (words L n).length ≤ (L.length + 1) ^ n
  | 0 => by simp [words]
  | n + 1 => by
    have ih := length_words_le L n
    have h1 : (L.flatMap fun h => (words L n).map (h :: ·)).length ≤
        L.length * (L.length + 1) ^ n :=
      length_flatMap_le fun x _ => by simpa using ih
    have h2 : 1 ≤ (L.length + 1) ^ n := Nat.one_le_pow _ _ (by omega)
    simp only [words, List.length_cons]
    rw [pow_succ, Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_comm] at h1
    omega

/-- The meet of the paths `(w.map T; c)` over the words `w ∈ ws` and labels `c ∈ lab w`. -/
def meetOf {α : Type*} (A : List ℕ) (ws : List (List α)) (lab : List α → Finset (Fin A.length))
    (T : α → Ty) : Ty :=
  Ty.interList (ws.flatMap fun w =>
    ((List.finRange A.length).filter fun c => decide (c ∈ lab w)).map
      fun c => pathTy (w.map T, .const (A.get c)))

section meetOf

variable {α : Type*} {A : List ℕ} {ws : List (List α)} {lab : List α → Finset (Fin A.length)}
  {T : α → Ty}

theorem mem_meetOf_list {y : Ty} : y ∈ (ws.flatMap fun w =>
    ((List.finRange A.length).filter fun c => decide (c ∈ lab w)).map
      fun c => pathTy (w.map T, .const (A.get c))) ↔
    ∃ w ∈ ws, ∃ c ∈ lab w, y = pathTy (w.map T, .const (A.get c)) := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, c, hc, rfl⟩; exact ⟨w, hw, c, hc, rfl⟩
  · rintro ⟨w, hw, c, hc, rfl⟩; exact ⟨w, hw, c, hc, rfl⟩

theorem le_meetOf_iff {X : Ty} : Le X (meetOf A ws lab T) ↔
    ∀ w ∈ ws, ∀ c ∈ lab w, Le X (pathTy (w.map T, .const (A.get c))) := by
  rw [meetOf, le_interList_iff]
  constructor
  · intro h w hw c hc
    exact h _ (mem_meetOf_list.2 ⟨w, hw, c, hc, rfl⟩)
  · intro h y hy
    obtain ⟨w, hw, c, hc, rfl⟩ := mem_meetOf_list.1 hy
    exact h w hw c hc

theorem meetOf_le {w : List α} (hw : w ∈ ws) {c : Fin A.length} (hc : c ∈ lab w) :
    Le (meetOf A ws lab T) (pathTy (w.map T, .const (A.get c))) :=
  le_meetOf_iff.1 (Le.refl _) w hw c hc

theorem le_arrow_meetOf {X ρ : Ty}
    (h : ∀ w ∈ ws, ∀ c ∈ lab w, Le X (.arrow ρ (pathTy (w.map T, .const (A.get c))))) :
    Le X (.arrow ρ (meetOf A ws lab T)) := by
  refine Le.trans (le_interList_iff.2 fun y hy => ?_) (interList_map_arrow_le ρ _)
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  obtain ⟨w, hw, c, hc, rfl⟩ := mem_meetOf_list.1 hy'
  exact h w hw c hc

theorem meetOf_congr {lab' : List α → Finset (Fin A.length)} {T' : α → Ty}
    (hl : ∀ w ∈ ws, lab w = lab' w) (hT : ∀ w ∈ ws, ∀ x ∈ w, T x = T' x) :
    meetOf A ws lab T = meetOf A ws lab' T' := by
  unfold meetOf
  congr 1
  refine List.flatMap_congr fun w hw => ?_
  rw [hl w hw, List.map_congr_left (hT w hw)]

theorem groundOver_meetOf (hT : ∀ w ∈ ws, ∀ x ∈ w, (T x).GroundOver A) :
    (meetOf A ws lab T).GroundOver A := by
  refine groundOver_interList fun y hy => ?_
  obtain ⟨w, hw, c, -, rfl⟩ := mem_meetOf_list.1 hy
  refine groundOver_pathTy (List.get_mem _ _) fun x hx => ?_
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
  exact hT w hw x' hx'

theorem size_meetOf_le {N M W : ℕ} (hN : ∀ w ∈ ws, w.length < N)
    (hT : ∀ w ∈ ws, ∀ x ∈ w, (T x).size ≤ M) (hW : ws.length ≤ W) :
    (meetOf A ws lab T).size ≤ W * A.length * (N * (M + 1) + 2) + 1 := by
  have hl : (ws.flatMap fun w => ((List.finRange A.length).filter fun c => decide (c ∈ lab w)).map
      fun c => pathTy (w.map T, .const (A.get c))).length ≤ W * A.length := by
    refine (length_flatMap_le (b := A.length) fun w _ => ?_).trans
      (Nat.mul_le_mul_right _ hW)
    simpa using (List.length_filter_le _ _).trans (List.length_finRange).le
  have hs : ∀ y ∈ (ws.flatMap fun w =>
      ((List.finRange A.length).filter fun c => decide (c ∈ lab w)).map
        fun c => pathTy (w.map T, .const (A.get c))), y.size ≤ N * (M + 1) + 1 := by
    intro y hy
    obtain ⟨w, hw, c, -, rfl⟩ := mem_meetOf_list.1 hy
    refine (size_pathTy_le (M := M) fun x hx => ?_).trans ?_
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
      exact hT w hw x' hx'
    · have := hN w hw
      rw [List.length_map]
      have := Nat.mul_le_mul_right (M + 1) this.le
      omega
  have h3 := size_interList_le hs
  rw [show N * (M + 1) + 1 + 1 = N * (M + 1) + 2 from rfl] at h3
  have := Nat.mul_le_mul_right (N * (M + 1) + 2) hl
  unfold meetOf
  omega

end meetOf

/-! ## The size bound -/

/-- Size bound for the realised letters of rank `< d`. -/
def tbAux (N m a : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => (m + 1) ^ N * a * (N * (tbAux N m a d + 1) + 2) + 1

/-- The size bound of the realisation (`N` support, `m` letters, `a` constants). -/
def realizeBound (N m a : ℕ) : ℕ := tbAux N m a (m + 1)

theorem tbAux_succ_le (N m a d : ℕ) : tbAux N m a d ≤ tbAux N m a (d + 1) := by
  induction d with
  | zero => simp [tbAux]
  | succ d ih =>
    show (m + 1) ^ N * a * (N * (tbAux N m a d + 1) + 2) + 1 ≤
      (m + 1) ^ N * a * (N * (tbAux N m a (d + 1) + 1) + 2) + 1
    gcongr

theorem tbAux_mono_d {N m a d d' : ℕ} (h : d ≤ d') : tbAux N m a d ≤ tbAux N m a d' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (tbAux_succ_le _ _ _ _)

theorem tbAux_mono {N m a N' m' a' : ℕ} (hN : N ≤ N') (hm : m ≤ m') (ha : a ≤ a') (d : ℕ) :
    tbAux N m a d ≤ tbAux N' m' a' d := by
  induction d with
  | zero => simp [tbAux]
  | succ d ih =>
    show (m + 1) ^ N * a * (N * (tbAux N m a d + 1) + 2) + 1 ≤
      (m' + 1) ^ N' * a' * (N' * (tbAux N' m' a' d + 1) + 2) + 1
    have : (m + 1) ^ N ≤ (m' + 1) ^ N' :=
      (Nat.pow_le_pow_left (by omega) N).trans (Nat.pow_le_pow_right (by omega) hN)
    gcongr

/-- `realizeBound` is monotone in each argument. -/
theorem realizeBound_mono {N m a N' m' a' : ℕ} (hN : N ≤ N') (hm : m ≤ m') (ha : a ≤ a') :
    realizeBound N m a ≤ realizeBound N' m' a' :=
  (tbAux_mono hN hm ha _).trans (tbAux_mono_d (by omega))

namespace APD

variable {P : Problem} (D : GammaData P)

/-! ## The realisation -/

section Realize

variable {N : ℕ} (s : (mlp D).Sol N)

/-- The stored top labels. -/
def SL (w : List (Fin D.m)) (x : Fin P.entities.length ⊕ Fin D.m) : Lab P := s.L w x

/-- The stored lower labels. -/
def SF (r : Fin D.m) (w : List (Fin D.m)) (i : Fin D.m) : Lab P := s.f r w i

theorem sl_nv (w : List (Fin D.m)) :
    NV D (SL D s w) (fun r => SF D s r (w.map (D.phi r.val))) := (s.step w).1

theorem sl_cv (w : List (Fin D.m)) (h : Fin D.m) : CV D (SL D s w) h (SL D s (h :: w)) :=
  (s.step w).2 h

theorem sl_rv : RV D (SL D s []) := s.root

theorem sl_supp {w : List (Fin D.m)} (hw : N ≤ w.length) (x) : SL D s w x = ∅ :=
  congrFun (s.supp w hw).1 x

variable {D s}

theorem lt_of_mem_sl {w : List (Fin D.m)} {x} {c : Fin P.consts.length} (hc : c ∈ SL D s w x) :
    w.length < N := by
  by_contra h
  rw [sl_supp D s (by omega)] at hc
  simp at hc

theorem eq_nil_of_mem_sl {i : Fin D.m} (hi : D.rk i = 0) {w : List (Fin D.m)}
    {c : Fin P.consts.length} (hc : c ∈ SL D s w (.inr i)) : w = [] := by
  cases w with
  | nil => rfl
  | cons h w =>
    rw [(sl_cv D s w h).2.2 i hi] at hc
    simp at hc

theorem sl_read {i : Fin D.m} {r : ℕ} (hi : D.rk i = r + 1) (w : List (Fin D.m)) :
    SL D s w (.inr i) = SL D s (w.map (D.phi r)) (.inr i) := by
  have hr : r < D.m := by have := D.rk_lt i; omega
  have h1 := (sl_nv D s w).2.2.2.2.2.1 ⟨r, hr⟩ i hi
  have h2 := (sl_nv D s (w.map (D.phi r))).2.2.2.2.2.1 ⟨r, hr⟩ i hi
  simp only at h1 h2
  rw [h1, h2, List.map_map]
  congr 2
  exact funext fun x => (D.phi_idem r x).symm

theorem sl_cons {i j : Fin D.m} (h : Le (D.G i) (D.G j)) (w : List (Fin D.m)) :
    SL D s w (.inr j) ⊆ SL D s w (.inr i) :=
  (sl_nv D s w).2.2.2.2.1 i j h

variable (D)

/-- The letters of smaller rank. -/
noncomputable def low (i : Fin D.m) : List (Fin D.m) :=
  (List.finRange D.m).filter fun j => decide (D.rk j < D.rk i)

variable {D} in
theorem mem_low {i j : Fin D.m} : j ∈ low D i ↔ D.rk j < D.rk i := by
  simp [low]

theorem length_low_le (i : Fin D.m) : (low D i).length ≤ D.m :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

variable (s)

/-- Approximations of the realised letters, by recursion on the rank. -/
noncomputable def Tlev : ℕ → Fin D.m → Ty
  | 0 => fun _ => .omega
  | n + 1 => fun i => meetOf P.consts (words (low D i) N) (fun w => SL D s w (.inr i)) (Tlev n)

/-- The realised letters `T i`. -/
noncomputable def T (i : Fin D.m) : Ty := Tlev D s (D.rk i + 1) i

theorem Tlev_succ (n : ℕ) (i : Fin D.m) : Tlev D s (n + 1) i =
    meetOf P.consts (words (low D i) N) (fun w => SL D s w (.inr i)) (Tlev D s n) := rfl

theorem Tlev_stable : ∀ n i, D.rk i < n → Tlev D s n i = T D s i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [T, Tlev_succ, Tlev_succ]
    refine meetOf_congr (fun _ _ => rfl) fun w hw x hx => ?_
    have hx' := mem_low.1 ((mem_words.1 hw).2 x hx)
    rw [ih n' (by omega) x (by omega), ih (D.rk i) (by omega) x hx']

/-- The recursive equation of the realised letters. -/
theorem T_eq (i : Fin D.m) :
    T D s i = meetOf P.consts (words (low D i) N) (fun w => SL D s w (.inr i)) (T D s) := by
  rw [T, Tlev_succ]
  refine meetOf_congr (fun _ _ => rfl) fun w hw x hx => ?_
  exact Tlev_stable D s _ x (mem_low.1 ((mem_words.1 hw).2 x hx))

variable {D s}

theorem T_le_meetand {i : Fin D.m} {w : List (Fin D.m)} (hw : w ∈ words (low D i) N)
    {c : Fin P.consts.length} (hc : c ∈ SL D s w (.inr i)) :
    Le (T D s i) (pathTy (w.map (T D s), .const (P.consts.get c))) := by
  rw [T_eq D s i]
  exact meetOf_le hw hc

theorem nil_mem_words {i : Fin D.m} {w : List (Fin D.m)} (hw : w.length < N) :
    [] ∈ words (low D i) N :=
  mem_words.2 ⟨by simp; omega, by simp⟩

theorem map_phi_mem_words {i : Fin D.m} {r : ℕ} (hi : D.rk i = r + 1) {w : List (Fin D.m)}
    (hw : w.length < N) : w.map (D.phi r) ∈ words (low D i) N := by
  refine mem_words.2 ⟨by simpa using hw, fun x hx => ?_⟩
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  have := D.rk_phi_le r y
  exact mem_low.2 (by omega)

theorem path_phi_le {r : ℕ} {w : List (Fin D.m)}
    (H : ∀ x ∈ w, Le (T D s x) (T D s (D.phi r x))) (a : Ty) :
    Le (pathTy ((w.map (D.phi r)).map (T D s), a)) (pathTy (w.map (T D s), a)) := by
  refine pathTy_le_pathTy _ ?_
  rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 H

theorem T_mono_aux : ∀ n (i j : Fin D.m), D.rk i + D.rk j < n → Le (D.G i) (D.G j) →
    Le (T D s i) (T D s j) := by
  intro n
  induction n with
  | zero => intro i j h; omega
  | succ n ih =>
    intro i j hn hij
    rw [T_eq D s j]
    refine le_meetOf_iff.2 fun w hw c hc => ?_
    have hw' := mem_words.1 hw
    have hc' := sl_cons hij w hc
    rcases hrk : D.rk i with _ | r
    · obtain rfl := eq_nil_of_mem_sl hrk hc'
      exact T_le_meetand (nil_mem_words hw'.1) hc'
    · rw [sl_read hrk] at hc'
      refine (T_le_meetand (map_phi_mem_words hrk hw'.1) hc').trans (path_phi_le ?_ _)
      intro x hx
      have h1 := mem_low.1 (hw'.2 x hx)
      have h2 := D.rk_phi_le r x
      exact ih x _ (by omega) (D.le_phi r x)

/-- The realised letters are monotone in the letters. -/
theorem T_mono {i j : Fin D.m} (h : Le (D.G i) (D.G j)) : Le (T D s i) (T D s j) :=
  T_mono_aux _ i j (Nat.lt_succ_self _) h

theorem T_le_path {i : Fin D.m} {w : List (Fin D.m)} {c : Fin P.consts.length}
    (hc : c ∈ SL D s w (.inr i)) :
    Le (T D s i) (pathTy (w.map (T D s), .const (P.consts.get c))) := by
  have hw := lt_of_mem_sl hc
  rcases hrk : D.rk i with _ | r
  · obtain rfl := eq_nil_of_mem_sl hrk hc
    exact T_le_meetand (nil_mem_words hw) hc
  · rw [sl_read hrk] at hc
    exact (T_le_meetand (map_phi_mem_words hrk hw) hc).trans
      (path_phi_le (fun x _ => T_mono (D.le_phi r x)) _)

variable (D s)

/-- The realised entities. -/
noncomputable def U (x : Fin P.entities.length ⊕ Fin D.m) : Ty :=
  meetOf P.consts (words (List.finRange D.m) N) (fun w => SL D s w x) (T D s)

variable {D s}

theorem U_le_path {x} {w : List (Fin D.m)} {c : Fin P.consts.length} (hc : c ∈ SL D s w x) :
    Le (U D s x) (pathTy (w.map (T D s), .const (P.consts.get c))) :=
  meetOf_le (mem_words.2 ⟨lt_of_mem_sl hc, fun y _ => List.mem_finRange y⟩) hc

theorem le_U_iff {X : Ty} {x} : Le X (U D s x) ↔
    ∀ w c, c ∈ SL D s w x → Le X (pathTy (w.map (T D s), .const (P.consts.get c))) := by
  rw [U, le_meetOf_iff]
  exact ⟨fun h w c hc => h w (mem_words.2 ⟨lt_of_mem_sl hc, fun y _ => List.mem_finRange y⟩) c hc,
    fun h w _ c hc => h w c hc⟩

/-- The realised entity of a letter is the realised letter. -/
theorem U_inr (i : Fin D.m) : Eqv (U D s (.inr i)) (T D s i) := by
  constructor
  · rw [T_eq D s i]
    exact le_meetOf_iff.2 fun w _ c hc => U_le_path hc
  · exact le_U_iff.2 fun w c hc => T_le_path hc

theorem U_congr {x y} (h : ∀ w, SL D s w x = SL D s w y) : U D s x = U D s y :=
  meetOf_congr (fun w _ => h w) fun _ _ _ _ => rfl

variable (D s)

/-- The realised substitution. -/
noncomputable def Sr (x : ℕ) : Ty :=
  if h : ∃ e, P.entities.get e = .var x then U D s (.inl (Classical.choose h)) else .omega

variable {D s}

theorem exists_idx {σ : Ty} (h : σ ∈ P.entities) : ∃ e, P.entities.get e = σ :=
  List.get_of_mem h

/-- The realised substitution agrees with the realised entities on every entity. -/
theorem subst_eqv_U : ∀ (σ : Ty) (e : Fin P.entities.length), P.entities.get e = σ →
    Eqv (σ.subst (Sr D s)) (U D s (.inl e)) := by
  intro σ
  induction σ with
  | const c =>
    intro e he
    have hmem : P.IsSubterm (.const c) :=
      Problem.mem_entities.1 (he ▸ List.get_mem _ _)
    obtain ⟨k, hk⟩ := List.get_of_mem (Problem.const_mem_consts hmem)
    have hroot := (sl_rv D s).2 e k (by rw [he, hk])
    constructor
    · refine le_U_iff.2 fun w c' hc' => ?_
      cases w with
      | nil =>
        rw [hroot, Finset.mem_singleton] at hc'
        subst hc'
        show Le (Ty.const c) (Ty.const (P.consts.get c'))
        rw [hk]; exact Le.refl _
      | cons h w =>
        rw [(sl_cv D s w h).2.1 e c he] at hc'
        simp at hc'
    · have := U_le_path (s := s) (x := .inl e) (w := []) (c := k) (by rw [hroot]; simp)
      rw [hk] at this
      exact this
  | var x =>
    intro e he
    have hex : ∃ e, P.entities.get e = .var x := ⟨e, he⟩
    have hc : Classical.choose hex = e :=
      P.entities_nodup.get_inj_iff.1 ((Classical.choose_spec hex).trans he.symm)
    simp only [Ty.subst, Sr, hex, ↓reduceDIte, hc]
    exact Eqv.refl _
  | omega =>
    intro e he
    refine ⟨le_U_iff.2 fun w c hc => ?_, Le.omega _⟩
    rw [(sl_nv D s w).2.1 e he] at hc
    simp at hc
  | arrow σ τ ihσ ihτ =>
    intro e he
    have hmem : Ty.arrow σ τ ∈ P.entities := he ▸ List.get_mem _ _
    obtain ⟨e₁, he₁⟩ := exists_idx (Problem.entities_left (Or.inl hmem))
    obtain ⟨e₂, he₂⟩ := exists_idx (Problem.entities_right (Or.inl hmem))
    have hls := Problem.mem_letterSubterms (Problem.mem_entities.1 hmem)
    obtain ⟨g, hg, eg⟩ := D.pins_mem σ hls
    obtain ⟨j, hj⟩ := D.exists_eqv_G hg eg
    have he' : P.entities.get e = .arrow (P.entities.get e₁) (P.entities.get e₂) := by
      rw [he, he₁, he₂]
    have hj' : Eqv ((P.entities.get e₁).subst D.S) (D.G j) := by rw [he₁]; exact hj
    have htie : U D s (.inl e₁) = U D s (.inr j) :=
      U_congr fun w => (sl_nv D s w).2.2.2.1 e e₁ e₂ j he' hj'
    have hcv := fun w h => (sl_cv D s w h).1 e e₁ e₂ j he' hj'
    have key : Eqv (U D s (.inl e)) (.arrow (T D s j) (U D s (.inl e₂))) := by
      constructor
      · refine le_arrow_meetOf fun w _ c hc => ?_
        have : c ∈ SL D s (j :: w) (.inl e) := by
          rw [hcv w j]
          simpa only [show Le (D.G j) (D.G j) from Le.refl _, ↓reduceIte] using hc
        exact U_le_path this
      · refine le_U_iff.2 fun w c hc => ?_
        cases w with
        | nil =>
          rw [(sl_rv D s).1 e _ _ he'] at hc
          simp at hc
        | cons h w =>
          rw [hcv w h] at hc
          split_ifs at hc with hh
          · exact Le.arrow (T_mono hh) (U_le_path hc)
          · simp at hc
    have h1 := ihσ e₁ he₁
    rw [htie] at h1
    exact (Eqv.arrow (h1.trans (U_inr j)) (ihτ e₂ he₂)).trans key.symm
  | inter σ τ ihσ ihτ =>
    intro e he
    have hmem : Ty.inter σ τ ∈ P.entities := he ▸ List.get_mem _ _
    obtain ⟨e₁, he₁⟩ := exists_idx (Problem.entities_left (Or.inr hmem))
    obtain ⟨e₂, he₂⟩ := exists_idx (Problem.entities_right (Or.inr hmem))
    have he' : P.entities.get e = .inter (P.entities.get e₁) (P.entities.get e₂) := by
      rw [he, he₁, he₂]
    have hnv := fun w => (sl_nv D s w).1 e e₁ e₂ he'
    have key : Eqv (U D s (.inl e)) (.inter (U D s (.inl e₁)) (U D s (.inl e₂))) := by
      refine eqv_of_forall_le_iff fun X => ?_
      rw [le_inter_iff, le_U_iff, le_U_iff, le_U_iff]
      simp only [hnv, Finset.mem_union]
      constructor
      · intro h
        exact ⟨fun w c hc => h w c (Or.inl hc), fun w c hc => h w c (Or.inr hc)⟩
      · rintro ⟨h1, h2⟩ w c (hc | hc)
        exacts [h1 w c hc, h2 w c hc]
    exact (Eqv.inter (ihσ e₁ he₁) (ihτ e₂ he₂)).trans key.symm

/-- The realised substitution is a unifier. -/
theorem Sr_solves : ∀ p ∈ P, Eqv (p.1.subst (Sr D s)) (p.2.subst (Sr D s)) := by
  intro p hp
  obtain ⟨e₁, he₁⟩ := exists_idx (Problem.mem_entities.2 ⟨p, hp, Or.inl (Ty.mem_subterms_self _)⟩)
  obtain ⟨e₂, he₂⟩ := exists_idx (Problem.mem_entities.2 ⟨p, hp, Or.inr (Ty.mem_subterms_self _)⟩)
  have : U D s (.inl e₁) = U D s (.inl e₂) :=
    U_congr fun w => (sl_nv D s w).2.2.1 p hp e₁ e₂ he₁ he₂
  refine (subst_eqv_U _ e₁ he₁).trans ?_
  rw [this]
  exact (subst_eqv_U _ e₂ he₂).symm

/-! ### Groundness and size -/

/-- The realised letters are ground over the constants of `P`. -/
theorem T_ground (i : Fin D.m) : (T D s i).GroundOver P.consts := by
  induction hn : D.rk i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    rw [T_eq D s i]
    refine groundOver_meetOf fun w hw x hx => ?_
    exact ih _ (hn ▸ mem_low.1 ((mem_words.1 hw).2 x hx)) x rfl

/-- The size of a realised letter is bounded in terms of its rank. -/
theorem T_size (i : Fin D.m) :
    (T D s i).size ≤ tbAux N D.m P.consts.length (D.rk i + 1) := by
  induction hn : D.rk i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    rw [T_eq D s i]
    refine (size_meetOf_le (N := N) (M := tbAux N D.m P.consts.length n)
      (W := (D.m + 1) ^ N) (fun w hw => (mem_words.1 hw).1) (fun w hw x hx => ?_) ?_).trans
      le_rfl
    · have hx := hn ▸ mem_low.1 ((mem_words.1 hw).2 x hx)
      exact (ih _ hx x rfl).trans (tbAux_mono_d (by omega))
    · exact (length_words_le _ _).trans (Nat.pow_le_pow_left (by
        have := length_low_le D i; omega) _)

theorem U_ground (x) : (U D s x).GroundOver P.consts :=
  groundOver_meetOf fun _ _ y _ => T_ground y

theorem U_size (x) : (U D s x).size ≤ realizeBound N D.m P.consts.length := by
  refine (size_meetOf_le (N := N) (M := tbAux N D.m P.consts.length D.m)
    (W := (D.m + 1) ^ N) (fun w hw => (mem_words.1 hw).1) (fun w _ y _ => ?_) ?_).trans le_rfl
  · exact (T_size y).trans (tbAux_mono_d (by have := D.rk_lt y; omega))
  · simpa using length_words_le (List.finRange D.m) N

theorem Sr_spec (x : ℕ) : (Sr D s x).size ≤ realizeBound N D.m P.consts.length ∧
    (Sr D s x).GroundOver P.consts := by
  unfold Sr
  split_ifs
  · exact ⟨U_size _, U_ground _⟩
  · refine ⟨?_, trivial⟩
    simp only [Ty.size, realizeBound, tbAux]
    omega

end Realize

/-- **The realisation**, with size bounds: a solution of the abstract problem with support `N`
yields a ground solution of `P` over the constants of `P` whose values have size at most
`realizeBound N |Γ| |consts P|`. -/
theorem realize (D : GammaData P) {N : ℕ} (s : (mlp D).Sol N) :
    ∃ S' : ℕ → Ty, (∀ e ∈ P, Eqv (e.1.subst S') (e.2.subst S')) ∧
      ∀ x, (S' x).size ≤ realizeBound N D.Γ.length P.consts.length ∧
        (S' x).GroundOver P.consts :=
  ⟨Sr D s, Sr_solves, Sr_spec⟩

end APD

end Intersection
