import Resolution.MLP
import Mathlib

/-!
# Small model theorem for multi-level problems
-/

namespace Intersection

open Classical

/-- The tower bound. -/
def towerBound (fmax : ℕ) : ℕ → ℕ → ℕ
  | 0, q => q
  | R + 1, q => towerBound fmax R (fmax * 2 ^ q) + q + 1

theorem towerBound_mono (fmax : ℕ) : ∀ R, Monotone (towerBound fmax R)
  | 0 => fun _ _ h => h
  | R + 1 => fun q q' h => by
      simp only [towerBound]
      have := towerBound_mono fmax R
        (Nat.mul_le_mul_left fmax (Nat.pow_le_pow_right (by norm_num : 2 > 0) h))
      omega

namespace MLP

/-- Solutions are monotone in the depth bound. -/
def Sol.mono {M : MLP} {N N' : ℕ} (s : M.Sol N) (h : N ≤ N') : M.Sol N' where
  f := s.f
  L := s.L
  step := s.step
  root := s.root
  supp w hw := s.supp w (le_trans h hw)

/-! ### Zero-input acceptance of the top level -/

section Zero

variable (M : MLP)

noncomputable def accStep (S : Finset M.Q) : Finset M.Q :=
  S ∪ Finset.univ.filter (fun q => ∃ ch : M.Γ → M.Q, (∀ x, ch x ∈ S) ∧ M.Δ q M.zF ch)

noncomputable def Kset : ℕ → Finset M.Q
  | 0 => {M.zQ}
  | j + 1 => M.accStep (Kset j)

noncomputable def Acc : Finset M.Q := M.Kset (Fintype.card M.Q)

lemma Kset_succ_sub (j : ℕ) : M.Kset j ⊆ M.Kset (j+1) := Finset.subset_union_left

lemma Kset_mono : Monotone M.Kset := monotone_nat_of_le_succ M.Kset_succ_sub

lemma Kset_stable {j : ℕ} (h : M.Kset j = M.Kset (j+1)) : ∀ i, M.Kset (j + i) = M.Kset j
  | 0 => rfl
  | i + 1 => by
    have ih := Kset_stable h i
    show M.accStep (M.Kset (j+i)) = M.Kset j
    rw [ih]; exact h.symm

lemma Kset_card_or (n : ℕ) :
    n + 1 ≤ (M.Kset n).card ∨ ∃ j, j < n ∧ M.Kset j = M.Kset (j+1) := by
  induction n with
  | zero => left; simp [Kset]
  | succ n ih =>
    rcases ih with h | ⟨j, hj, hj'⟩
    · by_cases he : M.Kset n = M.Kset (n+1)
      · right; exact ⟨n, by omega, he⟩
      · left
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨M.Kset_succ_sub n, he⟩)
        omega
    · right; exact ⟨j, by omega, hj'⟩

lemma Kset_sub_Acc (m : ℕ) : M.Kset m ⊆ M.Acc := by
  rcases M.Kset_card_or (Fintype.card M.Q) with h | ⟨j, hj, hj'⟩
  · have := Finset.card_le_univ (M.Kset (Fintype.card M.Q)); omega
  · by_cases hm : m ≤ Fintype.card M.Q
    · exact M.Kset_mono hm
    · obtain ⟨i, rfl⟩ : ∃ i, m = j + i := ⟨m - j, by omega⟩
      rw [M.Kset_stable hj' i]
      exact M.Kset_mono hj.le

noncomputable def lvl (p : M.Q) : ℕ := sInf {j | p ∈ M.Kset j}

lemma lvl_le {p : M.Q} {j : ℕ} (h : p ∈ M.Kset j) : M.lvl p ≤ j := Nat.sInf_le h

lemma mem_Kset_lvl {p : M.Q} {j : ℕ} (h : p ∈ M.Kset j) : p ∈ M.Kset (M.lvl p) :=
  Nat.sInf_mem (s := {j | p ∈ M.Kset j}) ⟨j, h⟩

lemma eq_zQ_of_lvl {p : M.Q} {j : ℕ} (h : p ∈ M.Kset j) (h0 : M.lvl p = 0) : p = M.zQ := by
  have := M.mem_Kset_lvl h
  rw [h0] at this
  simpa [Kset] using this

/-- A choice of children decreasing the level. -/
noncomputable def next (p : M.Q) : M.Γ → M.Q :=
  if h : ∃ ch : M.Γ → M.Q, (∀ x, ch x ∈ M.Kset (M.lvl p - 1)) ∧ M.Δ p M.zF ch
  then h.choose else fun _ => M.zQ

lemma next_spec {p : M.Q} {j : ℕ} (hp : p ∈ M.Kset j) :
    M.Δ p M.zF (M.next p) ∧ ∀ x, M.next p x ∈ M.Kset (M.lvl p - 1) := by
  have hex : ∃ ch : M.Γ → M.Q, (∀ x, ch x ∈ M.Kset (M.lvl p - 1)) ∧ M.Δ p M.zF ch := by
    rcases hl : M.lvl p with _ | m
    · have := M.eq_zQ_of_lvl hp hl
      subst this
      exact ⟨fun _ => M.zQ, fun _ => by simp [Kset], M.Δ_zero⟩
    · have h1 := M.mem_Kset_lvl hp
      rw [hl] at h1
      have h2 : p ∉ M.Kset m := fun h => by have := M.lvl_le h; omega
      simp only [Kset, accStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at h1
      rcases h1 with h1 | ⟨ch, hch, hΔ⟩
      · exact absurd h1 h2
      · exact ⟨ch, by simpa using hch, hΔ⟩
  unfold next
  split
  · rename_i h
    exact ⟨h.choose_spec.2, h.choose_spec.1⟩
  · exact absurd hex ‹_›

lemma next_spec_acc {p : M.Q} (hp : p ∈ M.Acc) :
    M.Δ p M.zF (M.next p) ∧ ∀ x, M.next p x ∈ M.Kset (M.lvl p - 1) :=
  M.next_spec (j := Fintype.card M.Q) hp

lemma next_mem_Acc {p : M.Q} (hp : p ∈ M.Acc) (x : M.Γ) : M.next p x ∈ M.Acc :=
  M.Kset_sub_Acc _ ((M.next_spec_acc hp).2 x)

lemma lvl_next_le {p : M.Q} (hp : p ∈ M.Acc) (x : M.Γ) :
    M.lvl (M.next p x) ≤ M.lvl p - 1 :=
  M.lvl_le ((M.next_spec_acc hp).2 x)

/-- Depth control: following `next` from depth `n` on reaches `zQ` after `card Q` steps. -/
lemma depth_bound (G : List M.Γ → M.Q) (n : ℕ)
    (hG : ∀ w, n ≤ w.length → G w ∈ M.Acc ∧ ∀ x, G (x :: w) = M.next (G w) x) :
    ∀ w, n + Fintype.card M.Q ≤ w.length → G w = M.zQ := by
  have key : ∀ k w, w.length = n + k → M.lvl (G w) ≤ Fintype.card M.Q - k := by
    intro k
    induction k with
    | zero => intro w hw; exact M.lvl_le (hG w (by omega)).1
    | succ k ih =>
      intro w hw
      cases w with
      | nil => simp at hw
      | cons x w =>
        simp only [List.length_cons] at hw
        have h1 := hG w (by omega)
        rw [h1.2 x]
        have := M.lvl_next_le h1.1 x
        have := ih w (by omega)
        omega
  intro w hw
  have h0 := key (w.length - n) w (by omega)
  exact M.eq_zQ_of_lvl (hG w (by omega)).1 (by omega)

noncomputable def nextRun (p : M.Q) : List M.Γ → M.Q
  | [] => p
  | x :: w => M.next (nextRun p w) x

lemma nextRun_mem {p : M.Q} (hp : p ∈ M.Acc) : ∀ w, M.nextRun p w ∈ M.Acc
  | [] => hp
  | x :: w => M.next_mem_Acc (nextRun_mem hp w) x

lemma nextRun_step {p : M.Q} (hp : p ∈ M.Acc) (w : List M.Γ) :
    M.Δ (M.nextRun p w) M.zF (fun x => M.nextRun p (x :: w)) :=
  (M.next_spec_acc (M.nextRun_mem hp w)).1

lemma nextRun_zero {p : M.Q} (hp : p ∈ M.Acc) (w : List M.Γ)
    (hw : Fintype.card M.Q ≤ w.length) : M.nextRun p w = M.zQ :=
  M.depth_bound _ 0 (fun w _ => ⟨M.nextRun_mem hp w, fun _ => rfl⟩) w (by omega)

lemma acc_of_run (σ : List M.Γ → M.Q) (hσ : ∀ u, M.Δ (σ u) M.zF (fun x => σ (x :: u)))
    (K : ℕ) (hK : ∀ u, K ≤ u.length → σ u = M.zQ) : σ [] ∈ M.Acc := by
  have : ∀ j u, K ≤ u.length + j → σ u ∈ M.Kset j := by
    intro j
    induction j with
    | zero => intro u hu; rw [hK u (by omega)]; simp [Kset]
    | succ j ih =>
      intro u hu
      show σ u ∈ M.accStep (M.Kset j)
      simp only [accStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      right
      exact ⟨fun x => σ (x :: u), fun x => ih _ (by simp; omega), hσ u⟩
  exact M.Kset_sub_Acc K (this K [] (by simp))

/-- Base case: no lower levels. -/
theorem base (hR : M.R = 0) {N : ℕ} (s : M.Sol N) : Nonempty (M.Sol (Fintype.card M.Q)) := by
  have hin : ∀ f w, M.input f w = M.zF := fun f w => funext fun r => absurd r.2 (by omega)
  have hp : s.L [] ∈ M.Acc :=
    M.acc_of_run s.L (fun u => by rw [← hin s.f u]; exact s.step u) N
      (fun u hu => (s.supp u hu).1)
  exact ⟨{ f := fun r _ => M.zF r
           L := M.nextRun (s.L [])
           step := fun w => by rw [hin]; exact M.nextRun_step hp w
           root := s.root
           supp := fun w hw => ⟨M.nextRun_zero hp w hw, fun r => rfl⟩ }⟩

end Zero

/-! ### Elimination of the last lower level -/

section Elim

variable (M : MLP) (R : ℕ) (hR : R + 1 = M.R)

/-- The last lower level. -/
def lst : Fin M.R := ⟨R, by omega⟩

/-- The embedding of the remaining lower levels. -/
def emb (r : Fin R) : Fin M.R := ⟨r.1, by have := r.2; omega⟩

lemma emb_le_lst (r : Fin R) : M.emb R hR r ≤ M.lst R hR := by
  rw [Fin.le_def]; simp only [emb, lst]; have := r.2; omega

lemma le_lst (r : Fin M.R) : r ≤ M.lst R hR := by
  rw [Fin.le_def]; simp only [lst]; have := r.2; omega

lemma fin_cases (r : Fin M.R) : (∃ r', r = M.emb R hR r') ∨ r = M.lst R hR := by
  by_cases h : r.1 < R
  · left; exact ⟨⟨r.1, h⟩, rfl⟩
  · right; ext; simp only [lst]; have := r.2; omega

/-- The new alphabet: letters fixed by the last projection. -/
abbrev EΓ : Type := {h : M.Γ // M.φ (M.lst R hR) h = h}

def proj (x : M.Γ) : M.EΓ R hR := ⟨M.φ (M.lst R hR) x, M.φ_idem _ _⟩

def combine (ι : ∀ r : Fin R, M.F (M.emb R hR r)) (F : M.F (M.lst R hR)) : ∀ r, M.F r :=
  fun r => if h : r.1 < R then ι ⟨r.1, h⟩ else
    cast (congrArg M.F (Fin.ext (by simp only [lst]; have := r.2; omega))) F

@[simp] lemma combine_emb (ι : ∀ r : Fin R, M.F (M.emb R hR r)) (F : M.F (M.lst R hR))
    (r : Fin R) : M.combine R hR ι F (M.emb R hR r) = ι r :=
  dite_eq_left (show (M.emb R hR r).1 < R from r.2)

@[simp] lemma combine_lst (ι : ∀ r : Fin R, M.F (M.emb R hR r)) (F : M.F (M.lst R hR)) :
    M.combine R hR ι F (M.lst R hR) = F :=
  (dite_eq_right (show ¬ (M.lst R hR).1 < R from by simp [lst])).trans (cast_eq _ _)

lemma combine_zero :
    M.combine R hR (fun r => M.zF (M.emb R hR r)) (M.zF (M.lst R hR)) = M.zF := by
  funext r
  rcases M.fin_cases R hR r with ⟨r', rfl⟩ | rfl <;> simp

def elimφ (r : Fin R) (x : M.EΓ R hR) : M.EΓ R hR :=
  ⟨M.φ (M.emb R hR r) x.1, M.φ_comp' _ _ (M.emb_le_lst R hR r) _⟩

def elimΔ (X : M.F (M.lst R hR) × Finset M.Q) (ι : ∀ r : Fin R, M.F (M.emb R hR r))
    (ch : M.EΓ R hR → M.F (M.lst R hR) × Finset M.Q) : Prop :=
  ∀ p ∈ X.2, ∃ pl : M.Γ → M.Q, (∀ x, pl x ∈ (ch (M.proj R hR x)).2) ∧
    M.Δ p (M.combine R hR ι X.1) pl

lemma emb_le_emb {s r : Fin R} (h : s ≤ r) : M.emb R hR s ≤ M.emb R hR r := by
  rw [Fin.le_def] at h ⊢; exact h

/-- The eliminated problem with `R` lower levels. -/
noncomputable abbrev elim : MLP where
  Γ := M.EΓ R hR
  R := R
  φ := M.elimφ R hR
  F r := M.F (M.emb R hR r)
  zF r := M.zF _
  Q := M.F (M.lst R hR) × Finset M.Q
  zQ := (M.zF _, M.Acc)
  Δ := M.elimΔ R hR
  root X := ∃ p ∈ X.2, M.root p
  φ_idem r x := Subtype.ext (M.φ_idem _ _)
  φ_comp s r hsr x := Subtype.ext (M.φ_comp _ _ (M.emb_le_emb R hR hsr) _)
  φ_comp' s r hsr x := Subtype.ext (M.φ_comp' _ _ (M.emb_le_emb R hR hsr) _)
  Δ_zero := by
    intro p hp
    refine ⟨M.next p, fun x => M.next_mem_Acc hp x, ?_⟩
    rw [M.combine_zero R hR]
    exact (M.next_spec_acc hp).1

lemma card_elim_Q :
    Fintype.card (M.elim R hR).Q = Fintype.card (M.F (M.lst R hR)) * 2 ^ Fintype.card M.Q := by
  show Fintype.card (M.F (M.lst R hR) × Finset M.Q) = _
  rw [Fintype.card_prod, Fintype.card_finset]

end Elim
/-! ### Completeness -/

section Complete

variable (M : MLP) (R : ℕ) (hR : R + 1 = M.R)

lemma input_proj_inv (f : ∀ r, List M.Γ → M.F r) {s1 s2 : List M.Γ}
    (h : s1.map (M.φ (M.lst R hR)) = s2.map (M.φ (M.lst R hR))) (u : List M.Γ) :
    M.input f (u ++ s1) = M.input f (u ++ s2) := by
  funext r
  have key : ∀ s : List M.Γ, s.map (M.φ r) = (s.map (M.φ (M.lst R hR))).map (M.φ r) := by
    intro s
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => (M.φ_comp r _ (M.le_lst R hR r) x).symm)
  simp only [input, List.map_append]
  rw [key s1, key s2, h]

lemma input_zero_of_len {N : ℕ} (s : M.Sol N) (w : List M.Γ) (hw : N ≤ w.length) :
    M.input s.f w = M.zF :=
  funext fun r => (s.supp _ (by simpa using hw)).2 r

/-- Subtree runs at `s0` from `p`. -/
def IsRun {N : ℕ} (s : M.Sol N) (s0 : List M.Γ) (p : M.Q) : Prop :=
  ∃ σ : List M.Γ → M.Q, σ [] = p ∧
    (∀ u, M.Δ (σ u) (M.input s.f (u ++ s0)) (fun x => σ (x :: u))) ∧
    ∃ K, ∀ u, K ≤ u.length → σ u = M.zQ

lemma isRun_child {N : ℕ} (s : M.Sol N) (t : List (M.EΓ R hR)) {σ : List M.Γ → M.Q}
    (hσ : ∀ u, M.Δ (σ u) (M.input s.f (u ++ t.map Subtype.val)) (fun x => σ (x :: u)))
    (K : ℕ) (hK : ∀ u, K ≤ u.length → σ u = M.zQ) (x : M.Γ) :
    M.IsRun s ((M.proj R hR x :: t).map Subtype.val) (σ [x]) := by
  refine ⟨fun u => σ (u ++ [x]), rfl, fun u => ?_, K, fun u hu => hK _ (by simp; omega)⟩
  have e : M.input s.f (u ++ (M.proj R hR x :: t).map Subtype.val) =
      M.input s.f ((u ++ [x]) ++ t.map Subtype.val) := by
    rw [List.append_assoc]
    apply M.input_proj_inv R hR
    simp only [List.map_cons, List.singleton_append, proj, M.φ_idem]
  rw [e]
  exact hσ _

lemma isRun_iff_acc {N : ℕ} (s : M.Sol N) (s0 : List M.Γ) (hs0 : N ≤ s0.length) (p : M.Q) :
    M.IsRun s s0 p ↔ p ∈ M.Acc := by
  have hz : ∀ u, M.input s.f (u ++ s0) = M.zF :=
    fun u => M.input_zero_of_len s _ (by simp; omega)
  constructor
  · rintro ⟨σ, rfl, hσ, K, hK⟩
    exact M.acc_of_run σ (fun u => by rw [← hz u]; exact hσ u) K hK
  · intro hp
    exact ⟨M.nextRun p, rfl, fun u => by rw [hz u]; exact M.nextRun_step hp u,
      Fintype.card M.Q, fun u hu => M.nextRun_zero hp u hu⟩

lemma input_complete {N : ℕ} (s : M.Sol N) (t : List (M.EΓ R hR)) :
    M.input s.f (t.map Subtype.val) =
      M.combine R hR (fun r => s.f (M.emb R hR r) ((t.map (M.elimφ R hR r)).map Subtype.val))
        (s.f (M.lst R hR) (t.map Subtype.val)) := by
  funext r
  rcases M.fin_cases R hR r with ⟨r', rfl⟩ | rfl
  · rw [combine_emb]
    simp only [input, List.map_map]
    rfl
  · rw [combine_lst]
    simp only [input, List.map_map]
    congr 1
    exact List.map_congr_left (fun x _ => x.2)

lemma isRun_root {N : ℕ} (s : M.Sol N) : M.IsRun s [] (s.L []) :=
  ⟨s.L, rfl, fun u => by simpa using s.step u, N, fun u hu => (s.supp u hu).1⟩

/-- Completeness: a solution of `M` gives a solution of the eliminated problem. -/
noncomputable def complete {N : ℕ} (s : M.Sol N) : (M.elim R hR).Sol N where
  f r t := s.f (M.emb R hR r) (List.map (fun x : M.EΓ R hR => x.1) t)
  L t := (s.f (M.lst R hR) (List.map (fun x : M.EΓ R hR => x.1) t),
    Finset.univ.filter (fun p => M.IsRun s (List.map (fun x : M.EΓ R hR => x.1) t) p))
  step t := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨σ, rfl, hσ, K, hK⟩ := hp
    refine ⟨fun x => σ [x], fun x => ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact M.isRun_child R hR s t (by simpa using hσ) K hK x
    · have h0 := hσ []
      simp only [List.nil_append] at h0
      rw [M.input_complete R hR s t] at h0
      exact h0
  root := by
    refine ⟨s.L [], ?_, s.root⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact M.isRun_root s
  supp t ht := by
    refine ⟨Prod.ext ?_ ?_, fun r => (s.supp _ (ht.trans_eq (List.length_map ..).symm)).2 _⟩
    · exact (s.supp _ (ht.trans_eq (List.length_map ..).symm)).2 _
    · ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact M.isRun_iff_acc s _ (ht.trans_eq (List.length_map ..).symm) p

end Complete
/-! ### Soundness with depth control -/

section Sound

variable (M : MLP) (R : ℕ) (hR : R + 1 = M.R) {N' : ℕ} (s' : (M.elim R hR).Sol N')

/-- Good children at `t` from `p`. -/
def Good (t : List (M.EΓ R hR)) (p : M.Q) (pl : M.Γ → M.Q) : Prop :=
  (∀ x, pl x ∈ (s'.L (M.proj R hR x :: t)).2) ∧
    M.Δ p (M.combine R hR ((M.elim R hR).input s'.f t) (s'.L t).1) pl

noncomputable def pick (t : List (M.EΓ R hR)) (p : M.Q) : M.Γ → M.Q :=
  if N' ≤ t.length ∧ p ∈ M.Acc then M.next p else
  if h : ∃ pl, M.Good R hR s' t p pl then h.choose else fun _ => M.zQ

lemma sol_zero (t : List (M.EΓ R hR)) (ht : N' ≤ t.length) :
    (s'.L t).1 = M.zF (M.lst R hR) ∧ (s'.L t).2 = M.Acc ∧
      (M.elim R hR).input s'.f t = fun r => M.zF (M.emb R hR r) := by
  have h := s'.supp t ht
  refine ⟨congrArg Prod.fst h.1, congrArg Prod.snd h.1, funext fun r => ?_⟩
  exact (s'.supp _ (ht.trans_eq (List.length_map ..).symm)).2 r

lemma pick_good (t : List (M.EΓ R hR)) (p : M.Q) (hp : p ∈ (s'.L t).2) :
    M.Good R hR s' t p (M.pick R hR s' t p) := by
  unfold pick
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := M.sol_zero R hR s' t h.1
    refine ⟨fun x => ?_, ?_⟩
    · rw [(M.sol_zero R hR s' (M.proj R hR x :: t) (by simp; omega)).2.1]
      exact M.next_mem_Acc h.2 x
    · rw [h1, h3, M.combine_zero R hR]
      exact (M.next_spec_acc h.2).1
  · have hex : ∃ pl, M.Good R hR s' t p pl := s'.step t p hp
    rw [dite_eq_left hex]
    exact hex.choose_spec

lemma root_ex : ∃ p, p ∈ (s'.L []).2 ∧ M.root p := s'.root

noncomputable def Lfun : List M.Γ → M.Q
  | [] => (M.root_ex R hR s').choose
  | x :: w => M.pick R hR s' (w.map (M.proj R hR)) (Lfun w) x

lemma Lfun_mem : ∀ w, M.Lfun R hR s' w ∈ (s'.L (w.map (M.proj R hR))).2
  | [] => (M.root_ex R hR s').choose_spec.1
  | x :: w => (M.pick_good R hR s' _ _ (Lfun_mem w)).1 x

noncomputable def sfun (r : Fin M.R) (w : List M.Γ) : M.F r :=
  M.combine R hR (fun r' => s'.f r' (w.map (M.proj R hR))) (s'.L (w.map (M.proj R hR))).1 r

lemma sfun_input (w : List M.Γ) :
    M.input (M.sfun R hR s') w =
      M.combine R hR ((M.elim R hR).input s'.f (w.map (M.proj R hR)))
        (s'.L (w.map (M.proj R hR))).1 := by
  funext r
  rcases M.fin_cases R hR r with ⟨r', rfl⟩ | rfl
  · simp only [input, sfun, combine_emb]
    congr 1
    simp only [List.map_map]
    refine List.map_congr_left (fun x _ => Subtype.ext ?_)
    show M.φ (M.lst R hR) (M.φ (M.emb R hR r') x) = M.φ (M.emb R hR r') (M.φ (M.lst R hR) x)
    rw [M.φ_comp' _ _ (M.emb_le_lst R hR r'), M.φ_comp _ _ (M.emb_le_lst R hR r')]
  · simp only [input, sfun, combine_lst]
    have e : (w.map (M.φ (M.lst R hR))).map (M.proj R hR) = w.map (M.proj R hR) := by
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => Subtype.ext (M.φ_idem _ x))
    rw [e]

/-- Soundness: a solution of the eliminated problem gives a solution of `M` with depth
`N' + card Q`. -/
noncomputable def sound : M.Sol (N' + Fintype.card M.Q) where
  f := M.sfun R hR s'
  L := M.Lfun R hR s'
  step w := by
    rw [M.sfun_input R hR s' w]
    exact (M.pick_good R hR s' _ _ (M.Lfun_mem R hR s' w)).2
  root := (M.root_ex R hR s').choose_spec.2
  supp w hw := by
    have hlen : N' ≤ (w.map (M.proj R hR)).length := by simp; omega
    obtain ⟨h1, h2, h3⟩ := M.sol_zero R hR s' _ hlen
    refine ⟨M.depth_bound (M.Lfun R hR s') N' (fun w hw => ?_) w hw, fun r => ?_⟩
    · have hlen : N' ≤ (w.map (M.proj R hR)).length := by simp; omega
      have hm : M.Lfun R hR s' w ∈ M.Acc := by
        rw [← (M.sol_zero R hR s' _ hlen).2.1]; exact M.Lfun_mem R hR s' w
      refine ⟨hm, fun x => ?_⟩
      show M.pick R hR s' _ _ x = _
      unfold pick
      rw [ite_eq_left ⟨hlen, hm⟩]
    · have : (fun r' => s'.f r' (w.map (M.proj R hR))) = fun r => M.zF (M.emb R hR r) :=
        funext fun r' => (s'.supp _ hlen).2 r'
      show M.combine R hR _ _ r = _
      rw [this, h1, M.combine_zero R hR]

end Sound
/-! ### The small model theorem -/

theorem small_model_aux : ∀ (R : ℕ) (M : MLP), M.R = R → ∀ {N : ℕ}, M.Sol N →
    ∀ fmax : ℕ, (∀ r, Fintype.card (M.F r) ≤ fmax) →
      Nonempty (M.Sol (towerBound fmax R (Fintype.card M.Q)))
  | 0, M, hR, _, s, _, _ => M.base hR s
  | R + 1, M, hR, _, s, fmax, hf => by
    obtain ⟨s'⟩ := small_model_aux R (M.elim R hR.symm) rfl (M.complete R hR.symm s) fmax
      (fun r => hf _)
    refine ⟨(M.sound R hR.symm s').mono ?_⟩
    have hc : Fintype.card (M.elim R hR.symm).Q ≤ fmax * 2 ^ Fintype.card M.Q := by
      rw [card_elim_Q]
      exact Nat.mul_le_mul_right _ (hf _)
    have := towerBound_mono fmax R hc
    show _ ≤ towerBound fmax R (fmax * 2 ^ Fintype.card M.Q) + Fintype.card M.Q + 1
    omega

/-- The small model theorem. -/
theorem small_model (M : MLP) {N : ℕ} (s : M.Sol N) (fmax : ℕ)
    (hf : ∀ r, Fintype.card (M.F r) ≤ fmax) :
    Nonempty (M.Sol (towerBound fmax M.R (Fintype.card M.Q))) :=
  small_model_aux M.R M rfl s fmax hf

end MLP
end Intersection
