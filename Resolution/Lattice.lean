import Resolution.Paths

namespace Intersection

/-!
# Joins of intersection types

The join of `A` and `B` is the intersection of the letterwise intersections of all pairs of
same-shape paths (same atom, same length) of `A` and `B`. It is the least upper bound of `A`
and `B` for BCD subtyping.
-/

/-- Path characterization of subtyping, with `Le` on letters. -/
theorem le_iff_paths {σ τ : Ty} : Le σ τ ↔ ∀ π' ∈ τ.paths, ∃ π ∈ σ.paths,
    π.2 = π'.2 ∧ List.Forall₂ (fun a b => Le a b) π'.1 π.1 := by
  rw [Ty.le_iff_leb, Ty.leb_iff]
  simp only [Ty.le_iff_leb]

/-- The paths of the join: letterwise intersections of same-shape path pairs. -/
def Ty.joinPaths (A B : Ty) : List (List Ty × Ty) :=
  A.paths.flatMap fun p =>
    (B.paths.filter fun q => decide (p.2 = q.2) && p.1.length == q.1.length).map
      fun q => (List.zipWith Ty.inter p.1 q.1, p.2)

/-- The join (least upper bound) of two types. -/
def Ty.join (A B : Ty) : Ty := Ty.interList ((A.joinPaths B).map pathTy)

theorem Ty.mem_joinPaths {A B : Ty} {p q : List Ty × Ty} (hp : p ∈ A.paths)
    (hq : q ∈ B.paths) (e : p.2 = q.2) (hl : p.1.length = q.1.length) :
    (List.zipWith Ty.inter p.1 q.1, p.2) ∈ A.joinPaths B := by
  simp only [Ty.joinPaths, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  exact ⟨p, hp, q, ⟨hq, e, hl⟩, rfl⟩

theorem forall₂_zipWith_left : ∀ {l₁ l₂ : List Ty}, l₁.length = l₂.length →
    List.Forall₂ (fun a b => Le a b) (List.zipWith Ty.inter l₁ l₂) l₁
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => .cons (Le.inter_left _ _) (forall₂_zipWith_left (by simpa using h))

theorem forall₂_zipWith_right : ∀ {l₁ l₂ : List Ty}, l₁.length = l₂.length →
    List.Forall₂ (fun a b => Le a b) (List.zipWith Ty.inter l₁ l₂) l₂
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => .cons (Le.inter_right _ _) (forall₂_zipWith_right (by simpa using h))

theorem forall₂_le_zipWith : ∀ {r l₁ l₂ : List Ty},
    List.Forall₂ (fun a b => Le a b) r l₁ → List.Forall₂ (fun a b => Le a b) r l₂ →
    List.Forall₂ (fun a b => Le a b) r (List.zipWith Ty.inter l₁ l₂)
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ =>
    .cons (Le.inter_glb h₁ h₂) (forall₂_le_zipWith t₁ t₂)

theorem Ty.le_join_left (A B : Ty) : Le A (A.join B) := by
  refine le_interList_iff.2 fun x hx => ?_
  simp only [List.mem_map, Ty.joinPaths, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hx
  obtain ⟨_, ⟨p, hp, q, ⟨-, -, hl⟩, rfl⟩, rfl⟩ := hx
  exact (le_pathTy hp).trans (pathTy_le_pathTy p.2 (forall₂_zipWith_left hl))

theorem Ty.le_join_right (A B : Ty) : Le B (A.join B) := by
  refine le_interList_iff.2 fun x hx => ?_
  simp only [List.mem_map, Ty.joinPaths, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hx
  obtain ⟨_, ⟨p, hp, q, ⟨hq, e, hl⟩, rfl⟩, rfl⟩ := hx
  have := (le_pathTy hq).trans (pathTy_le_pathTy q.2 (forall₂_zipWith_right hl))
  simpa [e] using this

/-- The join is the least upper bound. -/
theorem Ty.join_le {A B θ : Ty} (hA : Le A θ) (hB : Le B θ) : Le (A.join B) θ := by
  refine Le.trans (le_interList_iff.2 fun x hx => ?_) (interList_paths_le θ)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p, hp, ep, fp⟩ := le_iff_paths.1 hA r hr
  obtain ⟨q, hq, eq, fq⟩ := le_iff_paths.1 hB r hr
  have hl : p.1.length = q.1.length := fp.length_eq.symm.trans fq.length_eq
  refine (interList_le_of_mem (List.mem_map_of_mem
    (Ty.mem_joinPaths hp hq (ep.trans eq.symm) hl))).trans ?_
  obtain ⟨l, a⟩ := r
  simp only at ep
  rw [ep]
  exact pathTy_le_pathTy a (forall₂_le_zipWith fp fq)

theorem Ty.join_le_iff {A B θ : Ty} : Le (A.join B) θ ↔ Le A θ ∧ Le B θ :=
  ⟨fun h => ⟨(Ty.le_join_left A B).trans h, (Ty.le_join_right A B).trans h⟩,
    fun h => Ty.join_le h.1 h.2⟩

theorem Ty.join_mono_left {A A' : Ty} (B : Ty) (h : Le A A') : Le (A.join B) (A'.join B) :=
  Ty.join_le (h.trans (Ty.le_join_left _ _)) (Ty.le_join_right _ _)

theorem Ty.join_mono_right (A : Ty) {B B' : Ty} (h : Le B B') : Le (A.join B) (A.join B') :=
  Ty.join_le (Ty.le_join_left _ _) (h.trans (Ty.le_join_right _ _))

theorem Ty.join_mono {A A' B B' : Ty} (hA : Le A A') (hB : Le B B') :
    Le (A.join B) (A'.join B') :=
  (Ty.join_mono_left B hA).trans (Ty.join_mono_right A' hB)

theorem Ty.join_self (A : Ty) : Eqv (A.join A) A :=
  ⟨Ty.join_le (Le.refl A) (Le.refl A), Ty.le_join_left A A⟩

theorem Ty.join_comm (A B : Ty) : Eqv (A.join B) (B.join A) :=
  ⟨Ty.join_le (Ty.le_join_right _ _) (Ty.le_join_left _ _),
    Ty.join_le (Ty.le_join_right _ _) (Ty.le_join_left _ _)⟩

end Intersection
