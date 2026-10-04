import Intersection

namespace Intersection

/-!
# Paths and a decision procedure for BCD subtyping

Every type is equivalent to an intersection of *paths* `ρ₁ → ⋯ → ρₖ → a` with `a` an atom
(a constant or a variable). A path is represented as a pair `(ls, a) : List Ty × Ty`, where
`ls = [ρ₁, …, ρₖ]` are its *letters* and `a` is the atom itself (`Ty.const n` or `Ty.var n`).

`Ty.leb σ τ` holds iff every path of `τ` is matched by a path of `σ` with the same atom, the
same length, and letters related contravariantly (letter comparisons as a `List.Forall₂`).
Main result: `Ty.le_iff_leb : Le σ τ ↔ Ty.leb σ τ = true`.
-/

/-- Size of a type (number of constructors). -/
def Ty.size : Ty → ℕ
  | .const _ => 1
  | .var _ => 1
  | .omega => 1
  | .arrow σ τ => σ.size + τ.size + 1
  | .inter σ τ => σ.size + τ.size + 1

/-- The paths of a type: `(letters, atom)`; `ω` has no paths. -/
def Ty.paths : Ty → List (List Ty × Ty)
  | .const n => [([], .const n)]
  | .var n => [([], .var n)]
  | .omega => []
  | .inter σ τ => σ.paths ++ τ.paths
  | .arrow ρ τ => τ.paths.map fun π => (ρ :: π.1, π.2)

theorem Ty.size_of_mem_paths {σ : Ty} {π : List Ty × Ty} (h : π ∈ σ.paths) :
    ∀ ρ ∈ π.1, ρ.size < σ.size := by
  induction σ generalizing π with
  | const n => simp [paths] at h; subst h; simp
  | var n => simp [paths] at h; subst h; simp
  | omega => simp [paths] at h
  | inter σ τ ihσ ihτ =>
    simp only [paths, List.mem_append] at h
    rcases h with h | h
    · intro ρ hρ; have := ihσ h ρ hρ; simp [size]; omega
    · intro ρ hρ; have := ihτ h ρ hρ; simp [size]; omega
  | arrow ρ τ _ ihτ =>
    simp only [paths, List.mem_map] at h
    obtain ⟨π', hπ', rfl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [size]; omega
    · have := ihτ hπ' x hx; simp [size]; omega

/-- The path-matching subtyping algorithm. -/
def Ty.leb (σ τ : Ty) : Bool :=
  τ.paths.attach.all fun π' =>
    σ.paths.attach.any fun π =>
      decide (π.1.2 = π'.1.2) && (π'.1.1.length == π.1.1.length) &&
        (π'.1.1.zip π.1.1).attach.all fun ⟨(a, b), _hab⟩ => Ty.leb a b
termination_by σ.size + τ.size
decreasing_by
  have h1 := Ty.size_of_mem_paths π'.2 _ (List.of_mem_zip _hab).1
  have h2 := Ty.size_of_mem_paths π.2 _ (List.of_mem_zip _hab).2
  omega

theorem Ty.leb_iff (σ τ : Ty) : σ.leb τ = true ↔ ∀ π' ∈ τ.paths, ∃ π ∈ σ.paths,
    π.2 = π'.2 ∧ List.Forall₂ (fun a b => a.leb b = true) π'.1 π.1 := by
  rw [Ty.leb.eq_1]
  simp only [List.all_eq_true, List.any_eq_true, List.mem_attach, true_implies,
    Subtype.forall, Subtype.exists, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.forall₂_iff_zip, Prod.forall, Prod.exists]
  constructor
  · intro h a b hab
    obtain ⟨c, d, h1, -, ⟨h2, h3⟩, h4⟩ := h a b hab
    exact ⟨c, d, h1, h2, h3, fun h => h4 _ _ h⟩
  · intro h a b hab
    obtain ⟨c, d, h1, h2, h3, h4⟩ := h a b hab
    exact ⟨c, d, h1, trivial, ⟨h2, h3⟩, fun _ _ h => h4 h⟩

/-- Pointwise composition of `Forall₂` with membership information. -/
theorem forall₂_comp {α : Type*} {R S T : α → α → Prop} :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ →
      (∀ a ∈ l₁, ∀ b ∈ l₂, ∀ c ∈ l₃, R a b → S b c → T a c) → List.Forall₂ T l₁ l₃
  | [], [], [], .nil, .nil, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂, H =>
    .cons (H _ (by simp) _ (by simp) _ (by simp) h₁ h₂)
      (forall₂_comp t₁ t₂ fun a ha b hb c hc =>
        H a (by simp [ha]) b (by simp [hb]) c (by simp [hc]))

theorem forall₂_imp_mem {α : Type*} {R S : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ →
      (∀ a ∈ l₁, ∀ b ∈ l₂, R a b → S a b) → List.Forall₂ S l₁ l₂
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h t, H =>
    .cons (H _ (by simp) _ (by simp) h)
      (forall₂_imp_mem t fun a ha b hb => H a (by simp [ha]) b (by simp [hb]))

theorem Ty.leb_refl_aux : ∀ n (σ : Ty), σ.size = n → σ.leb σ = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hσ
    rw [Ty.leb_iff]
    intro π hπ
    refine ⟨π, hπ, rfl, ?_⟩
    refine List.forall₂_same.2 fun x hx => ih _ ?_ x rfl
    have := Ty.size_of_mem_paths hπ x hx
    omega

theorem Ty.leb_refl (σ : Ty) : σ.leb σ = true := Ty.leb_refl_aux _ σ rfl

theorem Ty.leb_of_subset {σ τ : Ty} (h : τ.paths ⊆ σ.paths) : σ.leb τ = true := by
  rw [Ty.leb_iff]
  intro π hπ
  exact ⟨π, h hπ, rfl, List.forall₂_same.2 fun x _ => Ty.leb_refl x⟩

theorem Ty.leb_trans_aux : ∀ n (σ τ ρ : Ty), σ.size + τ.size + ρ.size = n →
    σ.leb τ = true → τ.leb ρ = true → σ.leb ρ = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ ρ hn h₁ h₂
    rw [Ty.leb_iff] at *
    intro π₃ h₃
    obtain ⟨π₂, h₂', e₂, f₂⟩ := h₂ π₃ h₃
    obtain ⟨π₁, h₁', e₁, f₁⟩ := h₁ π₂ h₂'
    refine ⟨π₁, h₁', e₁.trans e₂, forall₂_comp f₂ f₁ fun c hc b hb a ha hcb hba => ?_⟩
    have := Ty.size_of_mem_paths h₃ c hc
    have := Ty.size_of_mem_paths h₂' b hb
    have := Ty.size_of_mem_paths h₁' a ha
    exact ih _ (by omega) c b a rfl hcb hba

theorem Ty.leb_trans {σ τ ρ : Ty} (h₁ : σ.leb τ = true) (h₂ : τ.leb ρ = true) :
    σ.leb ρ = true :=
  Ty.leb_trans_aux _ σ τ ρ rfl h₁ h₂

theorem Ty.leb_arrow {σ₁ σ₂ τ₁ τ₂ : Ty} (hσ : σ₂.leb σ₁ = true) (hτ : τ₁.leb τ₂ = true) :
    (Ty.arrow σ₁ τ₁).leb (.arrow σ₂ τ₂) = true := by
  rw [Ty.leb_iff] at hτ ⊢
  simp only [Ty.paths, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    exists_exists_and_eq_and]
  intro π hπ
  obtain ⟨π', h', e, f⟩ := hτ π hπ
  exact ⟨π', h', e, .cons hσ f⟩

/-- Completeness of the algorithm. -/
theorem Ty.leb_of_le {σ τ : Ty} (h : Le σ τ) : σ.leb τ = true := by
  induction h with
  | refl σ => exact Ty.leb_refl σ
  | trans _ _ ih₁ ih₂ => exact Ty.leb_trans ih₁ ih₂
  | omega σ => exact Ty.leb_of_subset (by simp [Ty.paths])
  | omega_arrow => exact Ty.leb_of_subset (by simp [Ty.paths])
  | inter_left σ τ => exact Ty.leb_of_subset (by simp [Ty.paths])
  | inter_right σ τ => exact Ty.leb_of_subset (by simp [Ty.paths])
  | inter_glb _ _ ih₁ ih₂ =>
    rw [Ty.leb_iff] at *
    simp only [Ty.paths, List.mem_append]
    rintro π (h | h)
    exacts [ih₁ π h, ih₂ π h]
  | arrow_inter σ τ₁ τ₂ => exact Ty.leb_of_subset (by simp [Ty.paths])
  | arrow _ _ ih₁ ih₂ => exact Ty.leb_arrow ih₁ ih₂

/-! ## Soundness -/

/-- The type `ρ₁ → ⋯ → ρₖ → a` of a path `([ρ₁, …, ρₖ], a)`. -/
def pathTy (π : List Ty × Ty) : Ty := π.1.foldr Ty.arrow π.2

/-- Intersection of a list of types; the empty intersection is `ω`. -/
def Ty.interList : List Ty → Ty
  | [] => .omega
  | σ :: l => .inter σ (Ty.interList l)

theorem Le.of_eq {σ τ : Ty} (h : σ = τ) : Le σ τ := h ▸ Le.refl σ

theorem le_interList_iff {σ : Ty} {l : List Ty} :
    Le σ (Ty.interList l) ↔ ∀ τ ∈ l, Le σ τ := by
  induction l with
  | nil => simp [Ty.interList, Le.omega]
  | cons τ l ih =>
    simp only [Ty.interList, List.mem_cons, forall_eq_or_imp, ← ih]
    exact ⟨fun h => ⟨h.trans (Le.inter_left _ _), h.trans (Le.inter_right _ _)⟩,
      fun h => Le.inter_glb h.1 h.2⟩

theorem interList_le_of_mem {σ : Ty} {l : List Ty} (h : σ ∈ l) : Le (Ty.interList l) σ :=
  le_interList_iff.1 (Le.refl _) σ h

theorem le_pathTy {σ : Ty} {π : List Ty × Ty} (h : π ∈ σ.paths) : Le σ (pathTy π) := by
  induction σ generalizing π with
  | const n => simp [Ty.paths] at h; subst h; exact Le.refl _
  | var n => simp [Ty.paths] at h; subst h; exact Le.refl _
  | omega => simp [Ty.paths] at h
  | inter σ τ ihσ ihτ =>
    simp only [Ty.paths, List.mem_append] at h
    rcases h with h | h
    exacts [(Le.inter_left _ _).trans (ihσ h), (Le.inter_right _ _).trans (ihτ h)]
  | arrow ρ τ _ ihτ =>
    simp only [Ty.paths, List.mem_map] at h
    obtain ⟨π', hπ', rfl⟩ := h
    exact Le.arrow (Le.refl _) (ihτ hπ')

theorem interList_map_arrow_le (ρ : Ty) (l : List Ty) :
    Le (Ty.interList (l.map (Ty.arrow ρ))) (Ty.arrow ρ (Ty.interList l)) := by
  induction l with
  | nil => exact Le.omega_arrow.trans (Le.arrow (Le.omega ρ) (Le.refl _))
  | cons τ l ih =>
    exact (Le.inter_glb (Le.inter_left _ _) ((Le.inter_right _ _).trans ih)).trans
      (Le.arrow_inter _ _ _)

theorem interList_paths_le (σ : Ty) :
    Le (Ty.interList (σ.paths.map pathTy)) σ := by
  induction σ with
  | const n => exact Le.inter_left _ _
  | var n => exact Le.inter_left _ _
  | omega => exact Le.refl _
  | inter σ τ ihσ ihτ =>
    simp only [Ty.paths, List.map_append]
    refine Le.inter_glb ((le_interList_iff.2 fun x hx => ?_).trans ihσ)
      ((le_interList_iff.2 fun x hx => ?_).trans ihτ)
    all_goals exact interList_le_of_mem (by simp [hx])
  | arrow ρ τ _ ihτ =>
    have : (Ty.arrow ρ τ).paths.map pathTy = (τ.paths.map pathTy).map (Ty.arrow ρ) := by
      simp [Ty.paths, pathTy, Function.comp_def]
    rw [this]
    exact (interList_map_arrow_le ρ _).trans (Le.arrow (Le.refl _) ihτ)

/-- Every type is equivalent to the intersection of its paths. -/
theorem eqv_interList_paths (σ : Ty) : Eqv σ (Ty.interList (σ.paths.map pathTy)) :=
  ⟨le_interList_iff.2 fun _ h => by
    obtain ⟨π, hπ, rfl⟩ := List.mem_map.1 h
    exact le_pathTy hπ, interList_paths_le σ⟩

theorem pathTy_le_pathTy {l l' : List Ty} (a : Ty) (h : List.Forall₂ (fun x y => Le x y) l' l) :
    Le (pathTy (l, a)) (pathTy (l', a)) := by
  induction h with
  | nil => exact Le.refl _
  | cons h _ ih => exact Le.arrow h ih

theorem Ty.le_of_leb_aux : ∀ n (σ τ : Ty), σ.size + τ.size = n → σ.leb τ = true → Le σ τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hn h
    rw [Ty.leb_iff] at h
    refine Le.trans (le_interList_iff.2 fun x hx => ?_) (interList_paths_le τ)
    obtain ⟨π', hπ', rfl⟩ := List.mem_map.1 hx
    obtain ⟨π, hπ, e, f⟩ := h π' hπ'
    refine (le_pathTy hπ).trans ?_
    obtain ⟨l, a⟩ := π
    obtain ⟨l', a'⟩ := π'
    simp only at e
    subst e
    refine pathTy_le_pathTy a (forall₂_imp_mem f fun x hx y hy hxy => ?_)
    have := Ty.size_of_mem_paths hπ' x hx
    have := Ty.size_of_mem_paths hπ y hy
    exact ih _ (by omega) x y rfl hxy

theorem Ty.le_of_leb {σ τ : Ty} (h : σ.leb τ = true) : Le σ τ := Ty.le_of_leb_aux _ σ τ rfl h

/-- Main theorem: the path algorithm decides BCD subtyping. -/
theorem Ty.le_iff_leb (σ τ : Ty) : Le σ τ ↔ σ.leb τ = true :=
  ⟨Ty.leb_of_le, Ty.le_of_leb⟩

instance : DecidableRel Le := fun σ τ => decidable_of_iff _ (Ty.le_iff_leb σ τ).symm

instance (σ τ : Ty) : Decidable (Eqv σ τ) := inferInstanceAs (Decidable (Le σ τ ∧ Le τ σ))

/-! ## Characterization lemmas -/

theorem le_inter_iff {σ τ₁ τ₂ : Ty} : Le σ (.inter τ₁ τ₂) ↔ Le σ τ₁ ∧ Le σ τ₂ :=
  ⟨fun h => ⟨h.trans (Le.inter_left _ _), h.trans (Le.inter_right _ _)⟩,
    fun h => Le.inter_glb h.1 h.2⟩

theorem le_atom_iff {σ a : Ty} (ha : a.paths = [([], a)]) :
    Le σ a ↔ ∃ π ∈ σ.paths, π = ([], a) := by
  rw [Ty.le_iff_leb, Ty.leb_iff, ha]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.forall₂_nil_left_iff]
  constructor
  · rintro ⟨π, hπ, e, h⟩
    exact ⟨π, hπ, Prod.ext h e⟩
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨_, hπ, rfl, rfl⟩

theorem le_const_iff {σ : Ty} {n : ℕ} : Le σ (.const n) ↔ ∃ π ∈ σ.paths, π = ([], .const n) :=
  le_atom_iff rfl

theorem le_var_iff {σ : Ty} {n : ℕ} : Le σ (.var n) ↔ ∃ π ∈ σ.paths, π = ([], .var n) :=
  le_atom_iff rfl

theorem le_const_iff_mem {σ : Ty} {n : ℕ} : Le σ (.const n) ↔ ([], .const n) ∈ σ.paths := by
  simp [le_const_iff]

theorem le_var_iff_mem {σ : Ty} {n : ℕ} : Le σ (.var n) ↔ ([], .var n) ∈ σ.paths := by
  simp [le_var_iff]

theorem omega_le_iff {σ : Ty} : Le .omega σ ↔ σ.paths = [] := by
  rw [Ty.le_iff_leb, Ty.leb_iff, List.eq_nil_iff_forall_not_mem]
  simp [Ty.paths]

theorem eqv_omega_iff {σ : Ty} : Eqv σ .omega ↔ σ.paths = [] :=
  ⟨fun h => omega_le_iff.1 h.2, fun h => ⟨Le.omega σ, omega_le_iff.2 h⟩⟩

/-- Arrow inversion: if the codomain of the larger arrow is not `ω`, both components are
related. -/
theorem Le.arrow_inv {σ₁ σ₂ τ₁ τ₂ : Ty} (h : Le (.arrow σ₁ τ₁) (.arrow σ₂ τ₂))
    (hτ : τ₂.paths ≠ []) : Le σ₂ σ₁ ∧ Le τ₁ τ₂ := by
  rw [Ty.le_iff_leb, Ty.leb_iff] at h
  simp only [Ty.paths, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    exists_exists_and_eq_and, List.forall₂_cons] at h
  obtain ⟨π₀, h₀⟩ := List.exists_mem_of_ne_nil _ hτ
  refine ⟨Ty.le_of_leb (h π₀ h₀).choose_spec.2.2.1, ?_⟩
  rw [Ty.le_iff_leb, Ty.leb_iff]
  intro π hπ
  obtain ⟨π', h', e, -, f⟩ := h π hπ
  exact ⟨π', h', e, f⟩

/-! ## Substitution stability -/

theorem Le.subst (S : ℕ → Ty) {σ τ : Ty} (h : Le σ τ) : Le (σ.subst S) (τ.subst S) := by
  induction h with
  | refl σ => exact Le.refl _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | omega σ => exact Le.omega _
  | omega_arrow => exact Le.omega_arrow
  | inter_left σ τ => exact Le.inter_left _ _
  | inter_right σ τ => exact Le.inter_right _ _
  | inter_glb _ _ ih₁ ih₂ => exact Le.inter_glb ih₁ ih₂
  | arrow_inter σ τ₁ τ₂ => exact Le.arrow_inter _ _ _
  | arrow _ _ ih₁ ih₂ => exact Le.arrow ih₁ ih₂

theorem Eqv.subst (S : ℕ → Ty) {σ τ : Ty} (h : Eqv σ τ) : Eqv (σ.subst S) (τ.subst S) :=
  ⟨h.1.subst S, h.2.subst S⟩

/-- Substitution of types for constants (variables unchanged). -/
def Ty.csubst (f : ℕ → Ty) : Ty → Ty
  | .const a => f a
  | .var α => .var α
  | .omega => .omega
  | .arrow σ τ => .arrow (σ.csubst f) (τ.csubst f)
  | .inter σ τ => .inter (σ.csubst f) (τ.csubst f)

theorem Le.csubst (f : ℕ → Ty) {σ τ : Ty} (h : Le σ τ) : Le (σ.csubst f) (τ.csubst f) := by
  induction h with
  | refl σ => exact Le.refl _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | omega σ => exact Le.omega _
  | omega_arrow => exact Le.omega_arrow
  | inter_left σ τ => exact Le.inter_left _ _
  | inter_right σ τ => exact Le.inter_right _ _
  | inter_glb _ _ ih₁ ih₂ => exact Le.inter_glb ih₁ ih₂
  | arrow_inter σ τ₁ τ₂ => exact Le.arrow_inter _ _ _
  | arrow _ _ ih₁ ih₂ => exact Le.arrow ih₁ ih₂

theorem Eqv.csubst (f : ℕ → Ty) {σ τ : Ty} (h : Eqv σ τ) : Eqv (σ.csubst f) (τ.csubst f) :=
  ⟨h.1.csubst f, h.2.csubst f⟩

/-! ## Equivalence helpers -/

theorem Eqv.refl (σ : Ty) : Eqv σ σ := ⟨Le.refl σ, Le.refl σ⟩

theorem Eqv.symm {σ τ : Ty} (h : Eqv σ τ) : Eqv τ σ := ⟨h.2, h.1⟩

theorem Eqv.trans {σ τ ρ : Ty} (h₁ : Eqv σ τ) (h₂ : Eqv τ ρ) : Eqv σ ρ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

end Intersection
