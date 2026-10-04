import Mathlib.Computability.RE

/-!
# Intersection types and their unification

Types are built from constants, variables, the universal type `ω`, arrows and
intersections. Subtyping is the least preorder closed under the axioms below, and two
types are equal when each is a subtype of the other. A substitution replaces the variables
of a type by types. A problem is a finite list of equations, and it is unifiable when some
substitution makes the two sides of every equation equal.

Constants and variables are numbered by naturals.
-/

namespace Intersection

/-- Intersection types. -/
inductive Ty : Type where
  | const : ℕ → Ty
  | var : ℕ → Ty
  | omega : Ty
  | arrow : Ty → Ty → Ty
  | inter : Ty → Ty → Ty
  deriving DecidableEq

/-- Subtyping: the least preorder closed under the axioms. -/
inductive Le : Ty → Ty → Prop where
  | refl (σ : Ty) : Le σ σ
  | trans {σ τ ρ : Ty} : Le σ τ → Le τ ρ → Le σ ρ
  | omega (σ : Ty) : Le σ .omega
  | omega_arrow : Le .omega (.arrow .omega .omega)
  | inter_left (σ τ : Ty) : Le (.inter σ τ) σ
  | inter_right (σ τ : Ty) : Le (.inter σ τ) τ
  | inter_glb {σ τ₁ τ₂ : Ty} : Le σ τ₁ → Le σ τ₂ → Le σ (.inter τ₁ τ₂)
  | arrow_inter (σ τ₁ τ₂ : Ty) :
      Le (.inter (.arrow σ τ₁) (.arrow σ τ₂)) (.arrow σ (.inter τ₁ τ₂))
  | arrow {σ₁ σ₂ τ₁ τ₂ : Ty} : Le σ₂ σ₁ → Le τ₁ τ₂ → Le (.arrow σ₁ τ₁) (.arrow σ₂ τ₂)

/-- Type equality: mutual subtyping. -/
def Eqv (σ τ : Ty) : Prop :=
  Le σ τ ∧ Le τ σ

/-- Substitution of types for variables. -/
def Ty.subst (S : ℕ → Ty) : Ty → Ty
  | .const a => .const a
  | .var α => S α
  | .omega => .omega
  | .arrow σ τ => .arrow (σ.subst S) (τ.subst S)
  | .inter σ τ => .inter (σ.subst S) (τ.subst S)

/-- A unification problem: a finite list of equations. -/
abbrev Problem := List (Ty × Ty)

/-- The problem has a unifier: a substitution making the two sides of every equation
equal. -/
def Unifiable (P : Problem) : Prop :=
  ∃ S : ℕ → Ty, ∀ e ∈ P, Eqv (e.1.subst S) (e.2.subst S)

/-! ## Encoding

Types are numbered by naturals, with `Nat.pair` for the binary constructors, which fixes
what it means for a predicate on problems to be computable: problems are lists of pairs
of types, encoded in the standard way. -/

/-- The number of a type. -/
def Ty.toNat : Ty → ℕ
  | .omega => 0
  | .const a => 4 * a + 1
  | .var α => 4 * α + 2
  | .arrow σ τ => 4 * Nat.pair σ.toNat τ.toNat + 3
  | .inter σ τ => 4 * Nat.pair σ.toNat τ.toNat + 4

/-- The type with a given number, the inverse of `Ty.toNat`. -/
def Ty.ofNat : ℕ → Ty
  | 0 => .omega
  | n + 1 =>
    if n % 4 = 0 then .const (n / 4)
    else if n % 4 = 1 then .var (n / 4)
    else if n % 4 = 2 then
      .arrow (Ty.ofNat (Nat.unpair (n / 4)).1) (Ty.ofNat (Nat.unpair (n / 4)).2)
    else .inter (Ty.ofNat (Nat.unpair (n / 4)).1) (Ty.ofNat (Nat.unpair (n / 4)).2)
decreasing_by
  all_goals
    have h1 := Nat.unpair_left_le (n / 4)
    have h2 := Nat.unpair_right_le (n / 4)
    omega

theorem Ty.toNat_ofNat : ∀ n : ℕ, (Ty.ofNat n).toNat = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [Ty.ofNat]; rfl
    | m + 1 =>
      have h1 := Nat.unpair_left_le (m / 4)
      have h2 := Nat.unpair_right_le (m / 4)
      rw [Ty.ofNat]
      split_ifs with h0 h1' h2'
      · simp only [Ty.toNat]; omega
      · simp only [Ty.toNat]; omega
      · simp only [Ty.toNat, ih (Nat.unpair (m / 4)).1 (by omega),
          ih (Nat.unpair (m / 4)).2 (by omega), Nat.pair_unpair]
        omega
      · simp only [Ty.toNat, ih (Nat.unpair (m / 4)).1 (by omega),
          ih (Nat.unpair (m / 4)).2 (by omega), Nat.pair_unpair]
        omega

theorem Ty.ofNat_toNat : ∀ σ : Ty, Ty.ofNat σ.toNat = σ := by
  intro σ
  induction σ with
  | const a =>
    show Ty.ofNat (4 * a + 1) = _
    rw [Ty.ofNat]
    simp
  | var α =>
    show Ty.ofNat (4 * α + 1 + 1) = _
    rw [Ty.ofNat]
    simp [Nat.add_mod]
    omega
  | omega => show Ty.ofNat 0 = _; rw [Ty.ofNat]
  | arrow σ τ ihσ ihτ =>
    show Ty.ofNat (4 * Nat.pair σ.toNat τ.toNat + 2 + 1) = _
    rw [Ty.ofNat]
    have e1 : (4 * Nat.pair σ.toNat τ.toNat + 2) % 4 = 2 := by omega
    have e2 : (4 * Nat.pair σ.toNat τ.toNat + 2) / 4 = Nat.pair σ.toNat τ.toNat := by omega
    simp [e1, e2, Nat.unpair_pair, ihσ, ihτ]
  | inter σ τ ihσ ihτ =>
    show Ty.ofNat (4 * Nat.pair σ.toNat τ.toNat + 3 + 1) = _
    rw [Ty.ofNat]
    have e1 : (4 * Nat.pair σ.toNat τ.toNat + 3) % 4 = 3 := by omega
    have e2 : (4 * Nat.pair σ.toNat τ.toNat + 3) / 4 = Nat.pair σ.toNat τ.toNat := by omega
    simp [e1, e2, Nat.unpair_pair, ihσ, ihτ]

/-- Types are in bijection with the naturals. -/
def Ty.equivNat : Ty ≃ ℕ where
  toFun := Ty.toNat
  invFun := Ty.ofNat
  left_inv := Ty.ofNat_toNat
  right_inv := Ty.toNat_ofNat

instance : Denumerable Ty := Denumerable.ofEquiv ℕ Ty.equivNat

instance : Primcodable Ty := Primcodable.ofDenumerable Ty

end Intersection
