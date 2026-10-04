# Research brief: bounding solutions of BCD intersection-type unification

## Setting
Types σ ::= a (constants) | α (vars) | ω | σ→σ | σ∩σ, BCD subtyping ≤, ≡ = mutual ≤.
Unification problem P: finite set of equations sᵢ ≐ tᵢ; unifiable iff ∃ substitution S
(variables ↦ finite types) with sᵢS ≡ tᵢS. (σ ≤ τ is expressible as σ ≐ σ∩τ.)
Decidability is OPEN in the literature (Dudenhefner–Martens–Rehof 2016/2017: EXPTIME-hard).
We want: a computable bound B(P) such that unifiable ⇒ unifiable by S with all S(x) of size ≤ B(P).
(Everything else — decidable ≤, enumeration, computability — is already formalized.)

## Established facts (all verified)
1. Path normal form: every type ≡ finite set of paths (θ₁…θₖ; a), a an atom; ω = ∅.
   T ≤ T' iff ∀p'∈T' ∃p∈T: same length, same atom, θ'ᵢ ≤ θᵢ (letters contravariant).
2. WLOG solutions are ground and use only constants of P (substitute others by ω).
3. Types modulo ≡ form a DISTRIBUTIVE LATTICE: meet = ∩; join J(A,B) = ∩ over pairs of
   same-shape paths (p of A, q of B) of the path with letters pᵢ∩qᵢ. (Types ≅ finitely generated
   up-sets of the path poset, reverse inclusion.) Laws: (σ₁∩σ₂)→τ = (σ₁→τ)∨(σ₂→τ),
   σ→(τ₁∩τ₂) = (σ→τ₁)∩(σ→τ₂), σ→(τ₁∨τ₂) = (σ→τ₁)∨(σ→τ₂), σ→ω = ω.
4. Monotone letter maps: if c is a monotone map on types (θ≤θ' ⇒ cθ≤cθ') and ĉ(T) applies c to
   every top-level letter of every path of T, then ĉ is monotone. If moreover c(λS) = ĉ(λS) for
   every letter-subterm λ of P (λ occurs as σ in some σ→τ of P), then S' := ĉ∘S is again a
   solution (ĉ commutes with the problem's structure).
5. Problem letters ground ⇒ fine: if all letter-subterms of P are ground, take
   c(θ) := ∩{κ ∈ K : θ ≤ κ}, K = hereditary letters of the ground letters, closed under ∩.
   Then WLOG all letters are in the finite set K∩, and word lengths can be bounded by FL0-style
   pumping (ordered alphabets reduce to plain FL0 via γ→z ↦ ⋂_{γ'≤γ}(γ'→z) on up-sets; FL0
   unification = Baader–Narendran, EXPTIME-complete, solutions = runs of looping tree automata,
   pumpable along branches).
6. LETTER SYSTEM CHARACTERIZATION. P is unifiable iff there is a finite "letter system":
   a finite set Γ of abstract letters with a preorder ⪯, a rank r: Γ→ℕ, for each g∈Γ a finite
   word-set W_g over Γ using only letters of rank < r(g), for each variable x a word-set W_x,
   and γ: (letter variables of P) → Γ such that (i) the equations of P hold "abstractly"
   (letters compared via ⪯, the letter variable y in letter position replaced by symbol γ(y)),
   (ii) W_{γ(y)} ≡ W_y abstractly, (iii) g ⪯ g' ⇒ W_g ≤ W_{g'} abstractly. (Soundness: realize
   letters by recursion on rank; the realization is monotone, so equations survive.
   Completeness: take Γ = all hereditary letters of a solution.) Since WLOG ⪯ can be the
   actual order, the CORE QUESTION is: bound the number of distinct hereditary letters of some
   solution (given that, FL0 pumping bounds word lengths).
7. THE OBSTACLE (cycles). The natural canonicalizations — max: c(θ) := ∩{S(y) : θ ≤ S(y)}, or
   min: c(θ) := ∨{λS : λS ≤ θ} (y ranging over letter variables / λ over letter-subterms) — must
   be applied consistently to the letters inside the letter-variable values themselves (to commute
   with the problem). This yields a regular (possibly cyclic, i.e. infinite) system. Example:
   constraints "y→c ≤ y" (every letter θ of y satisfies θ ≤ y) and "y ≤ z→c" (y nonempty):
   minimal solution y = (ω→c)→c, z = ω→c; but max-canonicalization sends the letter ω→c of y to
   S'(y) itself: S'(y) = S'(y)→c, infinite. Finite solutions there are exactly the even
   approximants F^{2m}(ω), F(v) = v→c (F(ω) ≤ F³(ω) ≤ … ≤ F⁴(ω) ≤ F²(ω) ≤ ω).
   "Pinned" cycles (y ≐ y→c) are genuinely unsolvable. Single-cycle analysis: θ ∈ [L, F(θ)]
   with F antitone is solvable iff L ≤ F(L), witnessed by θ := L.
8. Empirically (brute force up to size ~13): every minimal solution of every tested problem is
   tiny; every letter is ω, a constant (∩), another variable's value, or an "ω-approximant"
   (one unfolding of a self-referential term with ω inside). E.g. x ≐ y→c, y ≐ z→c, z ≤ x→c
   gives z = ω→c, y = (ω→c)→c, x = ((ω→c)→c)→c.

## Retraction formulation of the core question
Given a solution, let Γ = its hereditary letters closed under ∩ (finite, closed under taking
letters), with the actual order. For an ∩-closed Γ' ⊆ Γ containing ω and the letter-variable
values, the upper retraction c(h) := min{g ∈ Γ' : h ≤ g} is monotone; replacing letters by c
gives a valid letter system on Γ' PROVIDED the "uses" relation on Γ' (g uses c(h) for every
letter h of g) is acyclic. Starting from Γ'₀ = ∩-closure of letter-variable values, cycles force
adding letters (e.g. the letter ω→c above). The order ⪯ may be replaced by any smaller preorder
that still contains all comparisons actually used to certify the equations and is closed under
the consistency requirement (iii) — fewer relations make retractions more likely to hit ω and
reduce cycles. QUESTION: is the number of added letters bounded by a computable function of P?
