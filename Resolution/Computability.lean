import Resolution.Paths

/-!
# Primitive recursiveness of the subtyping algorithm

Relative to `Primcodable Ty` (encoding `Ty.toNat`): constructors, case analysis (`Ty.view`,
`Ty.elim`), structural recursion (`Ty.primrec_of_rec`), `Ty.size`, `Ty.paths`, and the main
result `Ty.primrec_leb : Primrec₂ Ty.leb`, with corollaries for `Le` and `Eqv`.
-/

namespace Intersection
open Encodable

theorem Ty.encode_eq (σ : Ty) : encode σ = σ.toNat := rfl
theorem Ty.decode_eq (n : ℕ) : (decode n : Option Ty) = some (Ty.ofNat n) := by
  simp [Encodable.decode]
  rfl
theorem Ty.ofNat_eq (n : ℕ) : Denumerable.ofNat Ty n = Ty.ofNat n := by
  have := Denumerable.decode_eq_ofNat Ty n
  rw [Ty.decode_eq] at this
  exact (Option.some.inj this).symm

theorem Ty.primrec_toNat : Primrec Ty.toNat := Primrec.encode
theorem Ty.primrec_ofNat : Primrec Ty.ofNat :=
  (Primrec.ofNat Ty).of_eq Ty.ofNat_eq

open Primrec in
theorem Ty.primrec_const : Primrec Ty.const :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (Primrec.const 4) .id) (Primrec.const 1)).of_eq
    fun _ => rfl

open Primrec in
theorem Ty.primrec_var : Primrec Ty.var :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (Primrec.const 4) .id) (Primrec.const 2)).of_eq
    fun _ => rfl

open Primrec in
theorem Ty.primrec_arrow : Primrec₂ Ty.arrow :=
  Primrec₂.encode_iff.1 <| (nat_add.comp (nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd))) (Primrec.const 3)).of_eq
    fun _ => rfl

open Primrec in
theorem Ty.primrec_inter : Primrec₂ Ty.inter :=
  Primrec₂.encode_iff.1 <| (nat_add.comp (nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd))) (Primrec.const 4)).of_eq
    fun _ => rfl

theorem Ty.primrec_omega {α : Type*} [Primcodable α] : Primrec fun _ : α => Ty.omega :=
  Primrec.const _

/-- Case analysis on a type: `ω`, constant, variable, arrow, intersection. -/
def Ty.view : Ty → Unit ⊕ ℕ ⊕ ℕ ⊕ (Ty × Ty) ⊕ (Ty × Ty)
  | .omega => .inl ()
  | .const a => .inr (.inl a)
  | .var a => .inr (.inr (.inl a))
  | .arrow σ τ => .inr (.inr (.inr (.inl (σ, τ))))
  | .inter σ τ => .inr (.inr (.inr (.inr (σ, τ))))

@[simp] theorem Ty.view_omega : Ty.omega.view = .inl () := rfl
@[simp] theorem Ty.view_const (a : ℕ) : (Ty.const a).view = .inr (.inl a) := rfl
@[simp] theorem Ty.view_var (a : ℕ) : (Ty.var a).view = .inr (.inr (.inl a)) := rfl
@[simp] theorem Ty.view_arrow (σ τ : Ty) :
    (Ty.arrow σ τ).view = .inr (.inr (.inr (.inl (σ, τ)))) := rfl
@[simp] theorem Ty.view_inter (σ τ : Ty) :
    (Ty.inter σ τ).view = .inr (.inr (.inr (.inr (σ, τ)))) := rfl

/-- The view computed from the number of a type. -/
def Ty.viewNat (n : ℕ) : Unit ⊕ ℕ ⊕ ℕ ⊕ (Ty × Ty) ⊕ (Ty × Ty) :=
  n.casesOn (.inl ()) fun m =>
    bif m % 4 == 0 then .inr (.inl (m / 4)) else
    bif m % 4 == 1 then .inr (.inr (.inl (m / 4))) else
    bif m % 4 == 2 then
      .inr (.inr (.inr (.inl (Ty.ofNat (Nat.unpair (m / 4)).1, Ty.ofNat (Nat.unpair (m / 4)).2))))
    else .inr (.inr (.inr (.inr (Ty.ofNat (Nat.unpair (m / 4)).1, Ty.ofNat (Nat.unpair (m / 4)).2))))

open Primrec in
theorem Ty.primrec_viewNat : Primrec Ty.viewNat := by
  have hq : Primrec fun m : ℕ => m / 4 := nat_div.comp .id (Primrec.const 4)
  have hr : Primrec fun m : ℕ => m % 4 := nat_mod.comp .id (Primrec.const 4)
  have hp : Primrec fun m : ℕ =>
      (Ty.ofNat (Nat.unpair (m / 4)).1, Ty.ofNat (Nat.unpair (m / 4)).2) :=
    pair (Ty.primrec_ofNat.comp (fst.comp (unpair.comp hq)))
      (Ty.primrec_ofNat.comp (snd.comp (unpair.comp hq)))
  refine nat_casesOn₁ _ ?_
  refine cond (Primrec.beq.comp hr (Primrec.const 0)) (sumInr.comp (sumInl.comp hq)) ?_
  refine cond (Primrec.beq.comp hr (Primrec.const 1)) (sumInr.comp (sumInr.comp (sumInl.comp hq))) ?_
  refine cond (Primrec.beq.comp hr (Primrec.const 2))
    (sumInr.comp (sumInr.comp (sumInr.comp (sumInl.comp hp)))) ?_
  exact sumInr.comp (sumInr.comp (sumInr.comp (sumInr.comp hp)))

theorem Ty.view_ofNat (n : ℕ) : (Ty.ofNat n).view = Ty.viewNat n := by
  cases n with
  | zero => rw [Ty.ofNat]; rfl
  | succ m =>
    rw [Ty.ofNat]
    simp only [Ty.viewNat]
    obtain h | h | h | h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    all_goals simp [h]

theorem Ty.view_eq (σ : Ty) : σ.view = Ty.viewNat σ.toNat := by
  rw [← Ty.view_ofNat, Ty.ofNat_toNat]

theorem Ty.primrec_view : Primrec Ty.view :=
  (Ty.primrec_viewNat.comp Ty.primrec_toNat).of_eq fun σ => (Ty.view_eq σ).symm

/-! ## Auxiliary list combinators -/

section ListAux
variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
open Primrec

theorem primrec_list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec₂ p) : Primrec fun a => (f a).all (p a) :=
  (list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hp.comp fst (fst.comp snd)) (snd.comp snd)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons x l ih => simp [ih]

theorem primrec_list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec₂ p) : Primrec fun a => (f a).any (p a) :=
  (list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp fst (fst.comp snd)) (snd.comp snd)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons x l ih => simp [ih]

theorem primrec_list_sum : Primrec (List.sum : List ℕ → ℕ) :=
  (list_foldr .id (Primrec.const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun _ => (List.sum_eq_foldr).symm

/-- One step of `zip`, as a left fold. -/
def zipStep (s : List (β × γ) × List γ) (b : β) : List (β × γ) × List γ :=
  match s.2 with
  | [] => (s.1, [])
  | c :: r => ((b, c) :: s.1, r)

omit [Primcodable β] [Primcodable γ] in
theorem zipStep_foldl_nil (l : List β) (acc : List (β × γ)) :
    l.foldl zipStep (acc, ([] : List γ)) = (acc, []) := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

omit [Primcodable β] [Primcodable γ] in
theorem zipStep_foldl (l : List β) : ∀ (acc : List (β × γ)) (r : List γ),
    (l.foldl zipStep (acc, r)).1 = (l.zip r).reverse ++ acc := by
  induction l with
  | nil => intro acc r; simp
  | cons b l ih =>
    intro acc r
    cases r with
    | nil =>
      simp only [List.foldl_cons, zipStep, List.zip_nil_right, List.reverse_nil, List.nil_append]
      exact congrArg Prod.fst (zipStep_foldl_nil l acc)
    | cons c r => simp [zipStep, ih]

theorem primrec_list_zip : Primrec₂ (@List.zip β γ) := by
  have hstep : Primrec₂ (@zipStep β γ) :=
    (list_casesOn (snd.comp fst) (Primrec.pair (fst.comp fst) (Primrec.const []))
      (Primrec.pair (list_cons.comp (Primrec.pair (snd.comp fst) (fst.comp snd))
        (fst.comp (fst.comp fst))) (snd.comp snd)).to₂).to₂.of_eq fun s b => by
      rcases s with ⟨acc, _ | ⟨c, r⟩⟩ <;> rfl
  have : Primrec₂ fun (l : List β) (r : List γ) => (l.foldl zipStep ([], r)).1.reverse :=
    (list_reverse.comp (fst.comp (list_foldl fst (Primrec.pair (Primrec.const []) snd)
      (hstep.comp (fst.comp snd) (snd.comp snd)).to₂))).to₂
  exact this.of_eq fun l r => by simp [zipStep_foldl]

end ListAux

/-! ## Case analysis and structural recursion -/

/-- Non-dependent eliminator for types (one step of case analysis). -/
def Ty.elim {σ : Type*} (g0 : σ) (gc gv : ℕ → σ) (ga gi : Ty × Ty → σ) : Ty → σ
  | .omega => g0
  | .const a => gc a
  | .var a => gv a
  | .arrow τ₁ τ₂ => ga (τ₁, τ₂)
  | .inter τ₁ τ₂ => gi (τ₁, τ₂)

section Elim
variable {α σ : Type*} [Primcodable α] [Primcodable σ]
open Primrec

theorem Ty.primrec_elim {f : α → Ty} {g0 : α → σ} {gc gv : α → ℕ → σ}
    {ga gi : α → Ty × Ty → σ} (hf : Primrec f) (h0 : Primrec g0) (hc : Primrec₂ gc)
    (hv : Primrec₂ gv) (ha : Primrec₂ ga) (hi : Primrec₂ gi) :
    Primrec fun a => (f a).elim (g0 a) (gc a) (gv a) (ga a) (gi a) := by
  have h3 : Primrec₂ fun (a : α) (x : (Ty × Ty) ⊕ (Ty × Ty)) =>
      (Sum.casesOn x (ga a) (gi a) : σ) :=
    (sumCasesOn snd (ha.comp (fst.comp fst) snd).to₂ (hi.comp (fst.comp fst) snd).to₂).to₂
  have h2 : Primrec₂ fun (a : α) (x : ℕ ⊕ (Ty × Ty) ⊕ (Ty × Ty)) =>
      (Sum.casesOn x (gv a) (fun y => Sum.casesOn y (ga a) (gi a)) : σ) :=
    (sumCasesOn snd (hv.comp (fst.comp fst) snd).to₂ (h3.comp (fst.comp fst) snd).to₂).to₂
  have h1 : Primrec₂ fun (a : α) (x : ℕ ⊕ ℕ ⊕ (Ty × Ty) ⊕ (Ty × Ty)) =>
      (Sum.casesOn x (gc a)
        (fun y => Sum.casesOn y (gv a) (fun z => Sum.casesOn z (ga a) (gi a))) : σ) :=
    (sumCasesOn snd (hc.comp (fst.comp fst) snd).to₂ (h2.comp (fst.comp fst) snd).to₂).to₂
  refine (sumCasesOn (Ty.primrec_view.comp hf) (h0.comp fst).to₂
    h1).of_eq fun a => ?_
  cases f a <;> rfl

end Elim

/-- The immediate subterms of a type. -/
def Ty.children : Ty → List Ty :=
  Ty.elim [] (fun _ => []) (fun _ => []) (fun p => [p.1, p.2]) (fun p => [p.1, p.2])

@[simp] theorem Ty.children_omega : Ty.omega.children = [] := rfl
@[simp] theorem Ty.children_const (a : ℕ) : (Ty.const a).children = [] := rfl
@[simp] theorem Ty.children_var (a : ℕ) : (Ty.var a).children = [] := rfl
@[simp] theorem Ty.children_arrow (σ τ : Ty) : (Ty.arrow σ τ).children = [σ, τ] := rfl
@[simp] theorem Ty.children_inter (σ τ : Ty) : (Ty.inter σ τ).children = [σ, τ] := rfl

open Primrec in
theorem Ty.primrec_children : Primrec Ty.children := by
  have hp : Primrec₂ fun (_ : Ty) (p : Ty × Ty) => [p.1, p.2] :=
    (list_cons.comp (fst.comp snd) (list_cons.comp (snd.comp snd) (Primrec.const []))).to₂
  exact Ty.primrec_elim .id (Primrec.const []) (Primrec.const []) (Primrec.const []) hp hp

theorem Ty.toNat_lt_of_mem_children {σ τ : Ty} (h : τ ∈ σ.children) : τ.toNat < σ.toNat := by
  cases σ with
  | omega | const _ | var _ => simp at h
  | arrow a b | inter a b =>
    have h1 := Nat.left_le_pair a.toNat b.toNat
    have h2 := Nat.right_le_pair a.toNat b.toNat
    simp only [Ty.children_arrow, Ty.children_inter, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl <;> simp only [Ty.toNat] <;> omega

/-- Structural recursion on types is primitive recursive: `f τ` is computed by a primitive
recursive `g` from `τ` and the values of `f` on the immediate subterms of `τ`. -/
theorem Ty.primrec_of_rec {σ : Type*} [Primcodable σ] (f : Ty → σ)
    {g : Ty → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ τ, g τ (τ.children.map f) = some (f τ)) : Primrec f :=
  Primrec.nat_omega_rec' f Ty.primrec_toNat Ty.primrec_children hg
    (fun _ _ h => Ty.toNat_lt_of_mem_children h) H

open Primrec in
theorem Ty.primrec_size : Primrec Ty.size :=
  Ty.primrec_of_rec Ty.size (g := fun _ rs => some (rs.sum + 1))
    (option_some.comp (succ.comp (primrec_list_sum.comp snd))).to₂ fun τ => by
    cases τ <;> simp [Ty.size]

/-- One step of the computation of `Ty.paths`. -/
def Ty.pathsStep (τ : Ty) (rs : List (List (List Ty × Ty))) : List (List Ty × Ty) :=
  τ.elim [] (fun n => [([], .const n)]) (fun n => [([], .var n)])
    (fun p => (rs.getD 1 []).map fun π => (p.1 :: π.1, π.2))
    (fun _ => rs.getD 0 [] ++ rs.getD 1 [])

open Primrec in
theorem Ty.primrec_pathsStep : Primrec₂ Ty.pathsStep := by
  let R := List (List (List Ty × Ty))
  refine Primrec₂.mk (Ty.primrec_elim (f := fun p : Ty × R => p.1) (g0 := fun _ => [])
    (gc := fun _ n => [([], .const n)]) (gv := fun _ n => [([], .var n)])
    (ga := fun x p => (x.2.getD 1 []).map fun π => (p.1 :: π.1, π.2))
    (gi := fun x _ => x.2.getD 0 [] ++ x.2.getD 1 []) fst (Primrec.const []) ?_ ?_ ?_ ?_)
  · exact (list_cons.comp (Primrec.pair (Primrec.const []) (Ty.primrec_const.comp snd))
      (Primrec.const [])).to₂
  · exact (list_cons.comp (Primrec.pair (Primrec.const []) (Ty.primrec_var.comp snd))
      (Primrec.const [])).to₂
  · apply Primrec₂.mk
    refine list_map (f := fun q : (Ty × R) × (Ty × Ty) => q.1.2.getD 1 [])
      ((list_getD ([] : List (List Ty × Ty))).comp (snd.comp fst) (Primrec.const 1)) ?_
    exact (Primrec.pair (list_cons.comp (fst.comp (snd.comp fst)) (fst.comp snd))
      (snd.comp snd)).to₂
  · apply Primrec₂.mk
    exact list_append.comp ((list_getD ([] : List (List Ty × Ty))).comp (snd.comp fst)
      (Primrec.const 0)) ((list_getD ([] : List (List Ty × Ty))).comp (snd.comp fst)
      (Primrec.const 1))

theorem Ty.primrec_paths : Primrec Ty.paths :=
  Ty.primrec_of_rec Ty.paths (Primrec.option_some.comp Ty.primrec_pathsStep).to₂ fun τ => by
    cases τ <;> simp [Ty.pathsStep, Ty.elim, Ty.paths]


/-! ## The subtyping algorithm is primitive recursive -/

/-- The pairs of letters on which `Ty.leb σ τ` recurses. -/
def Ty.lebPairs (σ τ : Ty) : List (Ty × Ty) :=
  τ.paths.flatMap fun π' => σ.paths.flatMap fun π => π'.1.zip π.1

/-- The path-matching algorithm with the letter comparison given by an oracle `F`. -/
def Ty.lebWith (F : Ty × Ty → Bool) (σ τ : Ty) : Bool :=
  τ.paths.all fun π' => σ.paths.any fun π =>
    decide (π.2 = π'.2) && decide (π'.1.length = π.1.length) && (π'.1.zip π.1).all F

theorem Ty.leb_eq_lebWith (σ τ : Ty) : σ.leb τ = Ty.lebWith (fun p => p.1.leb p.2) σ τ := by
  rw [Bool.eq_iff_iff, Ty.leb_iff, Ty.lebWith]
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.forall₂_iff_zip]
  constructor
  · intro h π' hπ'
    obtain ⟨π, hπ, e, hl, hz⟩ := h π' hπ'
    exact ⟨π, hπ, ⟨e, hl⟩, fun p hp => hz hp⟩
  · intro h π' hπ'
    obtain ⟨π, hπ, ⟨e, hl⟩, hz⟩ := h π' hπ'
    exact ⟨π, hπ, e, hl, fun hp => hz _ hp⟩

theorem Ty.lebWith_congr {F F' : Ty × Ty → Bool} {σ τ : Ty}
    (h : ∀ p ∈ Ty.lebPairs σ τ, F p = F' p) : Ty.lebWith F σ τ = Ty.lebWith F' σ τ := by
  have key : ∀ π' ∈ τ.paths, ∀ π ∈ σ.paths, (∀ x ∈ π'.1.zip π.1, F x = true) ↔
      (∀ x ∈ π'.1.zip π.1, F' x = true) := by
    intro π' hπ' π hπ
    refine forall₂_congr fun p hp => ?_
    rw [h p (by simp only [Ty.lebPairs, List.mem_flatMap]; exact ⟨π', hπ', π, hπ, hp⟩)]
  rw [Bool.eq_iff_iff, Ty.lebWith, Ty.lebWith]
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  refine forall₂_congr fun π' hπ' => exists_congr fun π => ?_
  constructor
  · rintro ⟨hπ, a, b⟩; exact ⟨hπ, a, (key π' hπ' π hπ).1 b⟩
  · rintro ⟨hπ, a, b⟩; exact ⟨hπ, a, (key π' hπ' π hπ).2 b⟩

theorem Ty.size_lt_of_mem_lebPairs {σ τ : Ty} {p : Ty × Ty} (h : p ∈ Ty.lebPairs σ τ) :
    p.1.size + p.2.size < σ.size + τ.size := by
  simp only [Ty.lebPairs, List.mem_flatMap] at h
  obtain ⟨π', hπ', π, hπ, hp⟩ := h
  have h1 := Ty.size_of_mem_paths hπ' _ (List.of_mem_zip hp).1
  have h2 := Ty.size_of_mem_paths hπ _ (List.of_mem_zip hp).2
  omega

theorem zip_map_self {β γ : Type*} (f : β → γ) :
    ∀ l : List β, l.zip (l.map f) = l.map fun p => (p, f p)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

section LebPrimrec
open Primrec
variable {α : Type*} [Primcodable α]

theorem Ty.primrec_lebPairs : Primrec₂ Ty.lebPairs := by
  apply Primrec₂.mk
  refine list_flatMap (Ty.primrec_paths.comp snd) ?_
  apply Primrec₂.mk
  refine list_flatMap (Ty.primrec_paths.comp (fst.comp fst)) ?_
  apply Primrec₂.mk
  exact primrec_list_zip.comp (fst.comp (snd.comp fst)) (fst.comp snd)

theorem Ty.primrec_lebWith {F : α → Ty × Ty → Bool} {s t : α → Ty} (hF : Primrec₂ F)
    (hs : Primrec s) (ht : Primrec t) : Primrec fun a => Ty.lebWith (F a) (s a) (t a) := by
  unfold Ty.lebWith
  refine primrec_list_all (Ty.primrec_paths.comp ht) ?_
  apply Primrec₂.mk
  refine primrec_list_any (Ty.primrec_paths.comp (hs.comp fst)) ?_
  apply Primrec₂.mk
  refine Primrec.and.comp (Primrec.and.comp ?_ ?_) ?_
  · exact Primrec.eq.decide.comp (snd.comp snd) (snd.comp (snd.comp fst))
  · exact Primrec.eq.decide.comp (list_length.comp (fst.comp (snd.comp fst)))
      (list_length.comp (fst.comp snd))
  · exact primrec_list_all (primrec_list_zip.comp (fst.comp (snd.comp fst)) (fst.comp snd))
      (hF.comp (fst.comp (fst.comp fst)) snd)

/-- The recombination step: recompute `leb` from the list of results on `lebPairs`. -/
def Ty.lebStep (b : Ty × Ty) (rs : List Bool) : Option Bool :=
  some (Ty.lebWith (fun p => ((Ty.lebPairs b.1 b.2).zip rs).any fun e => decide (e.1 = p) && e.2)
    b.1 b.2)

theorem Ty.primrec_lebStep : Primrec₂ Ty.lebStep := by
  apply Primrec₂.mk
  refine option_some.comp (Ty.primrec_lebWith ?_ (fst.comp fst) (snd.comp fst))
  apply Primrec₂.mk
  refine primrec_list_any
    (primrec_list_zip.comp (Ty.primrec_lebPairs.comp (fst.comp (fst.comp fst))
      (snd.comp (fst.comp fst))) (snd.comp fst)) ?_
  apply Primrec₂.mk
  exact Primrec.and.comp (Primrec.eq.decide.comp (fst.comp snd) (snd.comp fst))
    (snd.comp snd)

theorem Ty.lebStep_spec (b : Ty × Ty) :
    Ty.lebStep b ((Ty.lebPairs b.1 b.2).map fun p => p.1.leb p.2) = some (b.1.leb b.2) := by
  rw [Ty.lebStep, Ty.leb_eq_lebWith b.1 b.2]
  congr 1
  apply Ty.lebWith_congr
  intro p hp
  rw [zip_map_self, List.any_map, Bool.eq_iff_iff]
  simp only [List.any_eq_true, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, -, rfl, h⟩; exact h
  · intro h; exact ⟨p, hp, rfl, h⟩

/-- Main result: the subtyping decision procedure is primitive recursive. -/
theorem Ty.primrec_leb : Primrec₂ Ty.leb :=
  Primrec.nat_omega_rec' (fun b : Ty × Ty => b.1.leb b.2)
    (m := fun b => b.1.size + b.2.size) (l := fun b => Ty.lebPairs b.1 b.2)
    (nat_add.comp (Ty.primrec_size.comp fst) (Ty.primrec_size.comp snd))
    (Ty.primrec_lebPairs.comp fst snd) Ty.primrec_lebStep
    (fun _ _ h => Ty.size_lt_of_mem_lebPairs h) Ty.lebStep_spec

end LebPrimrec

theorem Ty.decide_le (σ τ : Ty) : decide (Le σ τ) = σ.leb τ := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Ty.le_iff_leb]

theorem Ty.decide_eqv (σ τ : Ty) : decide (Eqv σ τ) = (σ.leb τ && τ.leb σ) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, ← Ty.le_iff_leb, ← Ty.le_iff_leb]
  rfl

theorem Ty.primrec_decide_le : Primrec₂ fun σ τ : Ty => decide (Le σ τ) :=
  Ty.primrec_leb.of_eq fun σ τ => (Ty.decide_le σ τ).symm

theorem Ty.primrec_decide_eqv : Primrec₂ fun σ τ : Ty => decide (Eqv σ τ) :=
  (Primrec.and.comp Ty.primrec_leb Ty.primrec_leb.swap).to₂.of_eq fun σ τ =>
    (Ty.decide_eqv σ τ).symm

theorem primrecRel_le : PrimrecRel Le := primrecRel_iff_primrec_decide.2 Ty.primrec_decide_le

theorem primrecRel_eqv : PrimrecRel Eqv := primrecRel_iff_primrec_decide.2 Ty.primrec_decide_eqv

theorem Ty.computable_leb : Computable₂ Ty.leb := Ty.primrec_leb.to_comp

theorem Ty.computable_decide_le : Computable₂ fun σ τ : Ty => decide (Le σ τ) :=
  Ty.primrec_decide_le.to_comp

theorem Ty.computable_decide_eqv : Computable₂ fun σ τ : Ty => decide (Eqv σ τ) :=
  Ty.primrec_decide_eqv.to_comp

end Intersection
