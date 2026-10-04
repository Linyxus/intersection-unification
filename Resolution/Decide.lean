import Resolution.Computability

/-!
# Bounded search for small ground unifiers

`Problem.smallCheck P n` searches all substitutions sending the variables of `P` to ground
types over the constants of `P` of size at most `n`. It is primitive recursive, sound, and
complete for unifiers of that shape. Hence any primitive recursive bound on the size of
small ground unifiers yields decidability of unifiability (`computablePred_of_bound`). The
bound itself, `bigBound`, is established in `Resolution.Final`.
-/

namespace Intersection

/-! ## Constants and variables -/

/-- The constants occurring in a type. -/
def Ty.constList : Ty → List ℕ
  | .const a => [a]
  | .var _ => []
  | .omega => []
  | .arrow σ τ => σ.constList ++ τ.constList
  | .inter σ τ => σ.constList ++ τ.constList

/-- The variables occurring in a type. -/
def Ty.varList : Ty → List ℕ
  | .const _ => []
  | .var α => [α]
  | .omega => []
  | .arrow σ τ => σ.varList ++ τ.varList
  | .inter σ τ => σ.varList ++ τ.varList

/-- The constants occurring in a problem. -/
def Problem.constList (P : Problem) : List ℕ :=
  P.flatMap fun e => e.1.constList ++ e.2.constList

/-- The variables occurring in a problem. -/
def Problem.varList (P : Problem) : List ℕ :=
  P.flatMap fun e => e.1.varList ++ e.2.varList

/-- A ground type all of whose constants are in `cs`. -/
def Ty.GroundIn (cs : List ℕ) : Ty → Prop
  | .const a => a ∈ cs
  | .var _ => False
  | .omega => True
  | .arrow σ τ => σ.GroundIn cs ∧ τ.GroundIn cs
  | .inter σ τ => σ.GroundIn cs ∧ τ.GroundIn cs

theorem Ty.subst_congr {S S' : ℕ → Ty} :
    ∀ {σ : Ty}, (∀ x ∈ σ.varList, S x = S' x) → σ.subst S = σ.subst S'
  | .const _, _ => rfl
  | .var α, h => by simpa [Ty.subst, Ty.varList] using h
  | .omega, _ => rfl
  | .arrow σ τ, h => by
    simp only [Ty.varList, List.mem_append] at h
    simp only [Ty.subst]
    rw [Ty.subst_congr fun x hx => h x (Or.inl hx), Ty.subst_congr fun x hx => h x (Or.inr hx)]
  | .inter σ τ, h => by
    simp only [Ty.varList, List.mem_append] at h
    simp only [Ty.subst]
    rw [Ty.subst_congr fun x hx => h x (Or.inl hx), Ty.subst_congr fun x hx => h x (Or.inr hx)]

/-! ## Small ground types -/

/-- One step of the enumeration of small ground types. -/
def smallStep (cs : List ℕ) (L : List Ty) : List Ty :=
  Ty.omega :: (cs.map Ty.const ++
    L.flatMap fun a => L.flatMap fun b => [Ty.arrow a b, Ty.inter a b])

/-- The ground types over `cs` of size at most `n`. -/
def smallTys (cs : List ℕ) : ℕ → List Ty
  | 0 => []
  | n + 1 => smallStep cs (smallTys cs n)

theorem Ty.size_pos (σ : Ty) : 0 < σ.size := by
  cases σ <;> simp [Ty.size]

theorem mem_smallTys {cs : List ℕ} : ∀ {σ : Ty} {n : ℕ},
    σ.GroundIn cs → σ.size ≤ n → σ ∈ smallTys cs n
  | σ, 0, _, hs => absurd hs (by have := Ty.size_pos σ; omega)
  | .const a, n + 1, hg, _ => by
    simp only [Ty.GroundIn] at hg
    simp [smallTys, smallStep, hg]
  | .var _, _ + 1, hg, _ => hg.elim
  | .omega, n + 1, _, _ => by simp [smallTys, smallStep]
  | .arrow σ τ, n + 1, hg, hs => by
    simp only [Ty.size] at hs
    have h1 := mem_smallTys (n := n) hg.1 (by omega)
    have h2 := mem_smallTys (n := n) hg.2 (by omega)
    simp only [smallTys, smallStep, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inr ⟨σ, h1, τ, h2, by simp⟩)
  | .inter σ τ, n + 1, hg, hs => by
    simp only [Ty.size] at hs
    have h1 := mem_smallTys (n := n) hg.1 (by omega)
    have h2 := mem_smallTys (n := n) hg.2 (by omega)
    simp only [smallTys, smallStep, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inr ⟨σ, h1, τ, h2, by simp⟩)

theorem groundIn_of_mem_smallTys {cs : List ℕ} : ∀ {n : ℕ} {σ : Ty},
    σ ∈ smallTys cs n → σ.GroundIn cs
  | 0, _, h => by simp [smallTys] at h
  | n + 1, σ, h => by
    simp only [smallTys, smallStep, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_flatMap] at h
    rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, h⟩
    · trivial
    · exact ha
    · have h1 := groundIn_of_mem_smallTys ha
      have h2 := groundIn_of_mem_smallTys hb
      simp only [List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact ⟨h1, h2⟩

/-! ## Assignments -/

/-- The substitution sending `xs[i]` to `ts[i]` (and everything else to `ω`). -/
def substOf (xs : List ℕ) (ts : List Ty) (x : ℕ) : Ty :=
  ts.getD (List.idxOf x xs) Ty.omega

theorem substOf_map (S : ℕ → Ty) {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) :
    substOf xs (xs.map S) x = S x := by
  simp [substOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf hx]

/-- All lists of length `k` with entries from `cands`. -/
def assignments (cands : List Ty) : ℕ → List (List Ty)
  | 0 => [[]]
  | k + 1 => cands.flatMap fun c => (assignments cands k).map (c :: ·)

theorem mem_assignments {cands : List Ty} : ∀ {k : ℕ} {ts : List Ty},
    ts ∈ assignments cands k ↔ ts.length = k ∧ ∀ t ∈ ts, t ∈ cands
  | 0, ts => by cases ts <;> simp [assignments]
  | k + 1, [] => by simp [assignments]
  | k + 1, t :: ts => by
    simp only [assignments, List.mem_flatMap, List.mem_map, List.cons.injEq,
      List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨c, hc, us, hus, rfl, rfl⟩
      exact ⟨(mem_assignments.1 hus).1, hc, (mem_assignments.1 hus).2⟩
    · rintro ⟨hl, ht, hts⟩
      exact ⟨t, ht, ts, mem_assignments.2 ⟨hl, hts⟩, rfl, rfl⟩

/-! ## The bounded search -/

/-- Search for a unifier sending each variable to a ground type over the constants of the
problem, of size at most `n`. -/
def Problem.smallCheck (P : Problem) (n : ℕ) : Bool :=
  (assignments (smallTys P.constList n) P.varList.length).any fun ts =>
    P.all fun e => decide (Eqv (e.1.subst (substOf P.varList ts))
      (e.2.subst (substOf P.varList ts)))

/-- Soundness of the search. -/
theorem Problem.smallCheck_sound {P : Problem} {n : ℕ} (h : P.smallCheck n = true) :
    Unifiable P := by
  simp only [Problem.smallCheck, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨ts, -, hts⟩ := h
  exact ⟨_, hts⟩

/-- Completeness of the search for unifiers that are ground over the constants of the problem
and of size at most `n`. -/
theorem Problem.smallCheck_complete {P : Problem} {n : ℕ} (S : ℕ → Ty)
    (hS : ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S))
    (hg : ∀ x ∈ P.varList, (S x).GroundIn P.constList ∧ (S x).size ≤ n) :
    P.smallCheck n = true := by
  simp only [Problem.smallCheck, List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨P.varList.map S, mem_assignments.2 ⟨by simp, ?_⟩, fun e he => ?_⟩
  · simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_smallTys (hg x hx).1 (hg x hx).2
  · have hv : ∀ x ∈ e.1.varList ++ e.2.varList, x ∈ P.varList := fun x hx => by
      simp only [Problem.varList, List.mem_flatMap]
      exact ⟨e, he, hx⟩
    rw [Ty.subst_congr (S' := S) (fun x hx => substOf_map S (hv x (List.mem_append_left _ hx))),
      Ty.subst_congr (S' := S) (fun x hx => substOf_map S (hv x (List.mem_append_right _ hx)))]
    exact hS e he

/-! ## Primitive recursiveness -/

section Prim
open Primrec

theorem Ty.primrec_constList : Primrec Ty.constList :=
  Ty.primrec_of_rec Ty.constList
    (g := fun τ rs => some (τ.elim [] (fun a => [a]) (fun _ => []) (fun _ => rs.flatten)
      (fun _ => rs.flatten)))
    (option_some.comp (Ty.primrec_elim fst (Primrec.const [])
      (list_cons.comp snd (Primrec.const [])).to₂ (Primrec.const []).to₂
      (list_flatten.comp (snd.comp fst)).to₂ (list_flatten.comp (snd.comp fst)).to₂)).to₂
    fun τ => by cases τ <;> simp [Ty.elim, Ty.constList]

theorem Ty.primrec_varList : Primrec Ty.varList :=
  Ty.primrec_of_rec Ty.varList
    (g := fun τ rs => some (τ.elim [] (fun _ => []) (fun a => [a]) (fun _ => rs.flatten)
      (fun _ => rs.flatten)))
    (option_some.comp (Ty.primrec_elim fst (Primrec.const []) (Primrec.const []).to₂
      (list_cons.comp snd (Primrec.const [])).to₂
      (list_flatten.comp (snd.comp fst)).to₂ (list_flatten.comp (snd.comp fst)).to₂)).to₂
    fun τ => by cases τ <;> simp [Ty.elim, Ty.varList]

theorem Problem.primrec_constList : Primrec Problem.constList :=
  list_flatMap .id (list_append.comp (Ty.primrec_constList.comp (fst.comp snd))
    (Ty.primrec_constList.comp (snd.comp snd))).to₂

theorem Problem.primrec_varList : Primrec Problem.varList :=
  list_flatMap .id (list_append.comp (Ty.primrec_varList.comp (fst.comp snd))
    (Ty.primrec_varList.comp (snd.comp snd))).to₂

theorem primrec_smallStep : Primrec₂ smallStep := by
  apply Primrec₂.mk
  refine list_cons.comp (Primrec.const _) (list_append.comp
    (list_map fst (Ty.primrec_const.comp snd).to₂) (list_flatMap snd ?_))
  apply Primrec₂.mk
  refine list_flatMap (snd.comp fst) ?_
  apply Primrec₂.mk
  exact list_cons.comp (Ty.primrec_arrow.comp (snd.comp fst) snd)
    (list_cons.comp (Ty.primrec_inter.comp (snd.comp fst) snd) (Primrec.const []))

theorem primrec_smallTys : Primrec₂ smallTys := by
  have : Primrec₂ fun (cs : List ℕ) (n : ℕ) =>
      n.rec (motive := fun _ => List Ty) [] fun _ IH => smallStep cs IH :=
    nat_rec (Primrec.const []) (primrec_smallStep.comp fst (snd.comp snd)).to₂
  refine this.of_eq fun cs n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [smallTys, ← ih]

theorem primrec_assignments : Primrec₂ assignments := by
  have : Primrec₂ fun (cands : List Ty) (k : ℕ) =>
      k.rec (motive := fun _ => List (List Ty)) [[]] fun _ IH =>
        cands.flatMap fun c => IH.map (c :: ·) :=
    nat_rec (Primrec.const [[]]) (list_flatMap fst
      (list_map (snd.comp (snd.comp fst)) (list_cons.comp (snd.comp fst) snd).to₂).to₂).to₂
  refine this.of_eq fun cands k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [assignments, ← ih]

theorem primrec_substOf : Primrec fun p : (List ℕ × List Ty) × ℕ => substOf p.1.1 p.1.2 p.2 :=
  (list_getD Ty.omega).comp (snd.comp fst) (list_idxOf.comp snd (fst.comp fst))

/-- Substitution with the substitution given by an assignment list. -/
def substData (d : List ℕ × List Ty) (σ : Ty) : Ty := σ.subst (substOf d.1 d.2)

/-- The recombination step for `substData`. -/
def substDataStep (b : (List ℕ × List Ty) × Ty) (rs : List Ty) : Option Ty :=
  some (b.2.elim Ty.omega Ty.const (fun x => substOf b.1.1 b.1.2 x)
    (fun _ => Ty.arrow (rs.getD 0 .omega) (rs.getD 1 .omega))
    (fun _ => Ty.inter (rs.getD 0 .omega) (rs.getD 1 .omega)))

theorem primrec_substDataStep : Primrec₂ substDataStep := by
  apply Primrec₂.mk
  refine option_some.comp (Ty.primrec_elim (snd.comp fst) (Primrec.const _)
    (Ty.primrec_const.comp snd).to₂
    (primrec_substOf.comp (Primrec.pair (fst.comp (fst.comp fst)) snd)).to₂ ?_ ?_)
  · exact (Ty.primrec_arrow.comp ((list_getD Ty.omega).comp (snd.comp fst) (Primrec.const 0))
      ((list_getD Ty.omega).comp (snd.comp fst) (Primrec.const 1))).to₂
  · exact (Ty.primrec_inter.comp ((list_getD Ty.omega).comp (snd.comp fst) (Primrec.const 0))
      ((list_getD Ty.omega).comp (snd.comp fst) (Primrec.const 1))).to₂

theorem primrec_substData : Primrec₂ substData :=
  Primrec.nat_omega_rec' (fun b : (List ℕ × List Ty) × Ty => substData b.1 b.2)
    (m := fun b => b.2.toNat) (l := fun b => b.2.children.map (b.1, ·))
    (Ty.primrec_toNat.comp snd)
    (list_map (Ty.primrec_children.comp snd) (Primrec.pair (fst.comp fst) snd).to₂)
    primrec_substDataStep
    (fun b b' h => by
      simp only [List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      exact Ty.toNat_lt_of_mem_children hc)
    (fun b => by
      rcases b with ⟨d, τ⟩
      cases τ <;> simp [substDataStep, substData, Ty.elim, Ty.subst])

/-- The search is primitive recursive. -/
theorem Problem.primrec_smallCheck : Primrec₂ Problem.smallCheck := by
  have hinner : Primrec₂ fun (q : Problem × ℕ) (ts : List Ty) =>
      q.1.all fun e => decide (Eqv (substData (q.1.varList, ts) e.1)
        (substData (q.1.varList, ts) e.2)) := by
    apply Primrec₂.mk
    refine primrec_list_all (fst.comp fst) ?_
    apply Primrec₂.mk
    have hd : Primrec fun r : ((Problem × ℕ) × List Ty) × (Ty × Ty) =>
        (Problem.varList r.1.1.1, r.1.2) :=
      Primrec.pair (Problem.primrec_varList.comp (fst.comp (fst.comp fst))) (snd.comp fst)
    exact Ty.primrec_decide_eqv.comp (primrec_substData.comp hd (fst.comp snd))
      (primrec_substData.comp hd (snd.comp snd))
  have : Primrec fun q : Problem × ℕ =>
      (assignments (smallTys q.1.constList q.2) q.1.varList.length).any fun ts =>
        q.1.all fun e => decide (Eqv (substData (q.1.varList, ts) e.1)
          (substData (q.1.varList, ts) e.2)) :=
    primrec_list_any (primrec_assignments.comp
      (primrec_smallTys.comp (Problem.primrec_constList.comp fst) snd)
      (list_length.comp (Problem.primrec_varList.comp fst))) hinner
  exact this

end Prim

/-! ## Decidability from a bound -/

/-- **Decidability from a bound.** If every unifiable problem has a ground unifier over its own
constants of size at most a primitive recursive `B P`, then unifiability is computable. -/
theorem computablePred_of_bound (B : Problem → ℕ) (hB : Primrec B)
    (hsmall : ∀ P, Unifiable P → ∃ S, (∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) ∧
      ∀ x ∈ P.varList, (S x).GroundIn P.constList ∧ (S x).size ≤ B P) :
    ComputablePred Unifiable := by
  have key : ∀ P, Unifiable P ↔ P.smallCheck (B P) = true := fun P =>
    ⟨fun h => by
      obtain ⟨S, hS, hg⟩ := hsmall P h
      exact Problem.smallCheck_complete S hS hg,
     Problem.smallCheck_sound⟩
  refine ⟨fun P => decidable_of_iff _ (key P).symm, ?_⟩
  refine ((Problem.primrec_smallCheck.comp Primrec.id hB).to_comp).of_eq fun P => ?_
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
  exact (key P).symm

end Intersection
