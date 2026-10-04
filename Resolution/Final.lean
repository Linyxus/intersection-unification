import Resolution.GammaExists
import Resolution.Tower
import Resolution.Decide
import Resolution.APD

/-!
# Final assembly: decidability of unifiability

The letter bound (`GammaData.exists`), the completeness of the abstract problem
(`APD.complete`), the small-model theorem for multi-level problems (`MLP.small_model`) and
the realisation (`APD.realize`) are chained into an explicit primitive recursive bound
`bigBound P` on the size of a ground unifier of a unifiable problem `P`
(`small_ground_solution`). The bounded search of `Resolution.Decide` then gives
`decidable_final : ComputablePred Unifiable`.
-/

namespace Intersection

/-! ## Monotonicity of `towerBound` -/

theorem towerBound_mono_all : ∀ (R : ℕ) {f f' q q' : ℕ}, f ≤ f' → q ≤ q' →
    towerBound f R q ≤ towerBound f' R q'
  | 0, _, _, _, _, _, hq => hq
  | R + 1, f, f', q, q', hf, hq => by
      simp only [towerBound]
      have h2 : f * 2 ^ q ≤ f' * 2 ^ q' :=
        Nat.mul_le_mul hf (Nat.pow_le_pow_right (by norm_num) hq)
      have := towerBound_mono_all R hf h2
      omega

theorem le_towerBound (f : ℕ) : ∀ R q, q ≤ towerBound f R q
  | 0, _ => le_rfl
  | R + 1, q => by simp only [towerBound]; omega

theorem towerBound_succ_le {f : ℕ} (hf : 1 ≤ f) (R q : ℕ) :
    towerBound f R q ≤ towerBound f (R + 1) q := by
  simp only [towerBound]
  have h1 : q ≤ f * 2 ^ q :=
    (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_left _ hf)
  have := towerBound_mono f R h1
  omega

theorem towerBound_mono_R {f : ℕ} (hf : 1 ≤ f) {R R' : ℕ} (h : R ≤ R') (q : ℕ) :
    towerBound f R q ≤ towerBound f R' q := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (towerBound_succ_le hf _ _)

/-! ## Size bounds on the auxiliary lists of a problem -/

/-- The total size of a problem. -/
def Problem.totalSize (P : Problem) : ℕ := (P.map fun e => e.1.size + e.2.size).sum

theorem Ty.length_subterms (σ : Ty) : σ.subterms.length = σ.size := by
  induction σ with
  | const => rfl
  | var => rfl
  | omega => rfl
  | arrow a b iha ihb => simp [Ty.subterms, Ty.size, iha, ihb]
  | inter a b iha ihb => simp [Ty.subterms, Ty.size, iha, ihb]

theorem Problem.length_flatMap_subterms (P : Problem) :
    (P.flatMap fun e => e.1.subterms ++ e.2.subterms).length = P.totalSize := by
  induction P with
  | nil => rfl
  | cons e P ih =>
    simp only [List.flatMap_cons, List.length_append, Ty.length_subterms] at ih ⊢
    rw [ih]; simp [Problem.totalSize]

theorem Problem.letterSubterms_length_le (P : Problem) :
    P.letterSubterms.length ≤ P.totalSize :=
  (List.length_filterMap_le _ _).trans P.length_flatMap_subterms.le

theorem Problem.entities_length_le (P : Problem) : P.entities.length ≤ P.totalSize :=
  (List.dedup_sublist _).length_le.trans P.length_flatMap_subterms.le

theorem Problem.consts_length_le (P : Problem) : P.consts.length ≤ P.totalSize := by
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [← P.length_flatMap_subterms]
  induction P with
  | nil => simp
  | cons e P ih =>
    simp only [List.flatMap_cons, List.length_append]
    have h1 : e.1.consts.length ≤ e.1.subterms.length := List.length_filterMap_le _ _
    have h2 : e.2.consts.length ≤ e.2.subterms.length := List.length_filterMap_le _ _
    omega

/-! ## Constants: `consts` vs `constList` -/

theorem Ty.mem_constList_of_const_mem_subterms {c : ℕ} :
    ∀ {σ : Ty}, Ty.const c ∈ σ.subterms → c ∈ σ.constList
  | .const n, h => by simp [Ty.subterms] at h; simp [Ty.constList, h]
  | .var n, h => by simp [Ty.subterms] at h
  | .omega, h => by simp [Ty.subterms] at h
  | .arrow a b, h => by
      simp only [Ty.subterms, List.mem_cons, List.mem_append, reduceCtorEq, false_or] at h
      simp only [Ty.constList, List.mem_append]
      exact h.imp mem_constList_of_const_mem_subterms mem_constList_of_const_mem_subterms
  | .inter a b, h => by
      simp only [Ty.subterms, List.mem_cons, List.mem_append, reduceCtorEq, false_or] at h
      simp only [Ty.constList, List.mem_append]
      exact h.imp mem_constList_of_const_mem_subterms mem_constList_of_const_mem_subterms

theorem Ty.mem_constList_of_mem_consts {c : ℕ} {σ : Ty} (h : c ∈ σ.consts) :
    c ∈ σ.constList := by
  unfold Ty.consts at h
  obtain ⟨t, ht, hc⟩ := List.mem_filterMap.1 h
  cases t <;> simp at hc
  subst hc
  exact Ty.mem_constList_of_const_mem_subterms ht

theorem Problem.mem_constList_of_mem_consts {P : Problem} {c : ℕ} (h : c ∈ P.consts) :
    c ∈ P.constList := by
  unfold Problem.consts at h
  obtain ⟨e, he, hc⟩ := List.mem_flatMap.1 (List.mem_dedup.1 h)
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact List.mem_append.2 (Or.inl (Ty.mem_constList_of_mem_consts hc))
  · exact List.mem_append.2 (Or.inr (Ty.mem_constList_of_mem_consts hc))

theorem Ty.groundIn_of_groundOver {A B : List ℕ} (hAB : ∀ c ∈ A, c ∈ B) :
    ∀ {σ : Ty}, σ.GroundOver A → σ.GroundIn B
  | .const _, h => hAB _ h
  | .var _, h => h.elim
  | .omega, _ => trivial
  | .arrow _ _, h => ⟨groundIn_of_groundOver hAB h.1, groundIn_of_groundOver hAB h.2⟩
  | .inter _ _, h => ⟨groundIn_of_groundOver hAB h.1, groundIn_of_groundOver hAB h.2⟩

/-! ## The bound -/

/-- The explicit bound on the size of small ground unifiers. -/
def bigBound (P : Problem) : ℕ :=
  let s := P.totalSize
  let M := 2 ^ (4 ^ s + 1)
  realizeBound (towerBound ((2 ^ s) ^ M) M ((2 ^ s) ^ (s + M))) M s

/-- **Small ground unifiers.** Every unifiable problem has a ground unifier over its own
constants whose values have size at most `bigBound P`. -/
theorem small_ground_solution (P : Problem) (h : Unifiable P) :
    ∃ S : ℕ → Ty, (∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)) ∧
      ∀ x ∈ P.varList, (S x).GroundIn P.constList ∧ (S x).size ≤ bigBound P := by
  obtain ⟨D⟩ := GammaData.exists P h
  obtain ⟨N, ⟨sol⟩⟩ := APD.complete D
  set s := P.totalSize with hs
  set M := 2 ^ (4 ^ s + 1) with hM
  have hm : D.Γ.length ≤ M :=
    D.length_le.trans (Nat.pow_le_pow_right (by norm_num)
      (by have := Nat.pow_le_pow_right (show 4 > 0 by norm_num)
            (show P.letterSubterms.length ≤ s from P.letterSubterms_length_le)
          omega))
  have ha : P.consts.length ≤ s := P.consts_length_le
  have he : P.entities.length ≤ s := P.entities_length_le
  have h2a : 2 ^ P.consts.length ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) ha
  have hF : ∀ r, Fintype.card ((APD.mlp D).F r) ≤ (2 ^ s) ^ M := by
    intro r
    show Fintype.card (Fin D.m → Finset (Fin P.consts.length)) ≤ _
    simp only [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
    exact (Nat.pow_le_pow_left h2a _).trans
      (Nat.pow_le_pow_right (Nat.pow_pos (by norm_num)) hm)
  have hQ : Fintype.card (APD.mlp D).Q ≤ (2 ^ s) ^ (s + M) := by
    show Fintype.card (Fin P.entities.length ⊕ Fin D.m → Finset (Fin P.consts.length)) ≤ _
    simp only [Fintype.card_fun, Fintype.card_finset, Fintype.card_sum, Fintype.card_fin]
    exact (Nat.pow_le_pow_left h2a _).trans
      (Nat.pow_le_pow_right (Nat.pow_pos (by norm_num)) (by simp only [GammaData.m]; omega))
  obtain ⟨sol'⟩ := MLP.small_model (APD.mlp D) sol _ hF
  obtain ⟨S', hS', hb⟩ := APD.realize D sol'
  refine ⟨S', hS', fun x _ => ⟨Ty.groundIn_of_groundOver
    (fun c hc => Problem.mem_constList_of_mem_consts hc) (hb x).2, (hb x).1.trans ?_⟩⟩
  have hf1 : 1 ≤ (2 ^ s) ^ M := Nat.one_le_pow _ _ (Nat.pow_pos (by norm_num))
  have hR : (APD.mlp D).R = D.Γ.length := rfl
  have ht : towerBound ((2 ^ s) ^ M) (APD.mlp D).R (Fintype.card (APD.mlp D).Q) ≤
      towerBound ((2 ^ s) ^ M) M ((2 ^ s) ^ (s + M)) := by
    rw [hR]
    exact (towerBound_mono _ _ hQ).trans (towerBound_mono_R hf1 hm _)
  exact realizeBound_mono ht hm ha

/-! ## Primitive recursiveness of the bound -/

section Prim
open Primrec

theorem primrec_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- One step of the tower iteration on (current argument, accumulator). -/
def towerStep (f : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (f * 2 ^ p.1, p.2 + p.1 + 1)

theorem towerBound_eq_iterate (f : ℕ) : ∀ R q acc,
    towerBound f R q + acc = ((towerStep f)^[R] (q, acc)).1 + ((towerStep f)^[R] (q, acc)).2
  | 0, _, _ => rfl
  | R + 1, q, acc => by
      rw [Function.iterate_succ_apply, ← towerBound_eq_iterate f R]
      simp only [towerBound, towerStep]
      omega

/-- The tower bound is primitive recursive. -/
theorem primrec_towerBound : Primrec fun p : ℕ × ℕ × ℕ => towerBound p.1 p.2.1 p.2.2 := by
  have hstep : Primrec₂ fun (p : ℕ × ℕ × ℕ) (x : ℕ × ℕ) => towerStep p.1 x := by
    refine Primrec₂.mk (Primrec.pair ?_ ?_)
    · exact nat_mul.comp (fst.comp fst)
        (primrec_nat_pow.comp (const 2) (fst.comp snd))
    · exact nat_add.comp (nat_add.comp (snd.comp snd) (fst.comp snd)) (const 1)
  have hit : Primrec fun p : ℕ × ℕ × ℕ =>
      (towerStep p.1)^[p.2.1] (p.2.2, 0) :=
    nat_iterate (fst.comp snd) (Primrec.pair (snd.comp snd) (const 0)) hstep
  refine (nat_add.comp (fst.comp hit) (snd.comp hit)).of_eq fun p => ?_
  rw [← towerBound_eq_iterate]; rfl

theorem tbAux_eq_iterate (N m a : ℕ) : ∀ d,
    tbAux N m a d = (fun t => (m + 1) ^ N * a * (N * (t + 1) + 2) + 1)^[d] 0
  | 0 => rfl
  | d + 1 => by
      rw [Function.iterate_succ_apply', ← tbAux_eq_iterate N m a d]; rfl

/-- The realisation bound is primitive recursive. -/
theorem primrec_realizeBound : Primrec fun p : ℕ × ℕ × ℕ => realizeBound p.1 p.2.1 p.2.2 := by
  have hstep : Primrec₂ fun (p : ℕ × ℕ × ℕ) (t : ℕ) =>
      (p.2.1 + 1) ^ p.1 * p.2.2 * (p.1 * (t + 1) + 2) + 1 := by
    refine Primrec₂.mk ?_
    refine nat_add.comp (nat_mul.comp (nat_mul.comp (primrec_nat_pow.comp
      (nat_add.comp (fst.comp (snd.comp fst)) (const 1)) (fst.comp fst))
      (snd.comp (snd.comp fst)))
      (nat_add.comp (nat_mul.comp (fst.comp fst) (nat_add.comp snd (const 1))) (const 2)))
      (const 1)
  refine (nat_iterate (nat_add.comp (fst.comp snd) (const 1)) (const 0) hstep).of_eq fun p => ?_
  simp only [realizeBound, tbAux_eq_iterate]

theorem Problem.primrec_totalSize : Primrec Problem.totalSize :=
  primrec_list_sum.comp (list_map Primrec.id
    ((nat_add.comp (Ty.primrec_size.comp (fst.comp snd))
      (Ty.primrec_size.comp (snd.comp snd))).to₂))

/-- The bound is primitive recursive. -/
theorem primrec_bigBound : Primrec bigBound := by
  have hs := Problem.primrec_totalSize
  have hM : Primrec fun P : Problem => 2 ^ (4 ^ P.totalSize + 1) :=
    primrec_nat_pow.comp (const 2)
      (nat_add.comp (primrec_nat_pow.comp (const 4) hs) (const 1))
  have h2s : Primrec fun P : Problem => 2 ^ P.totalSize := primrec_nat_pow.comp (const 2) hs
  have ht : Primrec fun P : Problem => towerBound ((2 ^ P.totalSize) ^ (2 ^ (4 ^ P.totalSize + 1)))
      (2 ^ (4 ^ P.totalSize + 1)) ((2 ^ P.totalSize) ^ (P.totalSize + 2 ^ (4 ^ P.totalSize + 1))) :=
    primrec_towerBound.comp (Primrec.pair (primrec_nat_pow.comp h2s hM)
      (Primrec.pair hM (primrec_nat_pow.comp h2s (nat_add.comp hs hM))))
  exact primrec_realizeBound.comp (Primrec.pair ht (Primrec.pair hM hs))

end Prim

/-- **Unifiability of intersection types is decidable.** -/
theorem decidable_final : ComputablePred Unifiable :=
  computablePred_of_bound bigBound primrec_bigBound small_ground_solution

end Intersection
