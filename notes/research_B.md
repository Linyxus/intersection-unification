# Research B — regular solutions and approximation

Status, stated up front:

* **Not solved.** I do not have a proof that BCD intersection-type unification is decidable, and I
  found no undecidability mechanism.
* **Proved here (unconditional):**
  * (R) *Regular* unifiability is decidable, and every regularly unifiable problem has a regular
    solution with at most 2^|Λ| letter states (Λ = the letter subterms of P).
  * (K) For a decidable syntactic class, the **κ-aligned problems**, finite unifiability is
    equivalent to regular unifiability. So it is decidable, and solutions with ≤ (N+1)·2^|Λ|
    hereditary letters exist. This class strictly contains the *stratified* problems, which in turn
    contain fact 5's "ground letter subterms" case. It also contains cyclic examples such as
    y→c ≤ y, y ≤ z→c; x≐y→c, y≐z→c, z≤x→c; (x→c)→c ≤ x, x ≤ z→c; x ≤ (x→c)→c. Empirically it covers 853
    of 1083 random solvable problems syntactically, and 1079 of 1083 after instantiating letter-free
    variables.
* **Counterexamples showing two natural strategies cannot be complete:**
  * Q8: a unifiable problem with no V-closed solution, i.e. no solution whose letters are all meets
    of letter-subterm values. So the "retraction onto Γ'₀ = V∩" approach must add letters. The brief's
    fact-7 example is actually V-closed; see §5.1.
  * P♯: a unifiable problem for which no solution S and no depth vector make the
    "per-variable ω-approximant of the canonical regular solution" a solution. This is exactly the
    approximation that powers (K).
* **Remaining gap**, isolated as Conjecture Λ (§6): approximate only the letters that are *not*
  letter values, and keep letter values structural. It has been checked with 0 failures on 18,901
  random solutions, about 4,500 planted oscillating solutions, and every hand-made counterexample.
  With a depth-bound (compression) argument that I only sketch, it would imply decidability.

Code: `/tmp/explore_B/Main.lean`. It extends the brute-force explorer. The binary is
`/tmp/exB`; the commands are listed in §8.

---

## 1. Notation

* Types are finite sets of paths (θ₁…θ_k; a); ω = ∅; ≤ is the path order (fact 1). The
  **normal form** nf(T) is the antichain of minimal paths with letters recursively in normal form.
  It is unique, so T ≡ T' iff nf T = nf T'. **rank** r(T) is the letter-nesting depth of nf(T);
  it is an ≡-invariant. If θ is a letter of nf(T), then r(θ) < r(T), so θ ≢ T.
* For a map c on types, T[c] (written ĉ(T) in the brief) replaces every top-level letter θ of T by
  c(θ). If c is monotone, T ↦ T[c] is monotone (fact 4).
  If c ≤ c' pointwise, then T[c'] ≤ T[c] (contravariance).
* Λ = the letter subterms of P (all σ with σ→τ in P). For a solution S, V = {λS : λ ∈ Λ}, taken
  up to ≡; these are the **letter values**. V∩ is the set of meets of subsets of V (∩∅ = ω).
  The upper canonical map is ρ(θ) := ⋂{v ∈ V : θ ≤ v} ∈ V∩.
* Occurrence depth: the depth d(o) of a node o of a term is the number of left-arguments of →
  on its root path. Polarity is (−1)^d. D(s) is the maximal depth of a node of s.
* By fact 2, solutions are WLOG ground over the constants of P.

## 2. Regular solutions (Theorem R)

**Definition.** A *type graph* is a finite set Q of states; each q has a finite set W_q of paths
(q₁…q_k; a) over states. *Subtyping* ≤_G is the greatest relation such that q ≤_G q' implies:
for every (q'₁…q'_k; a) ∈ W_{q'} there is (q₁…q_k; a) ∈ W_q with q'_i ≤_G q_i for all i.
A type graph is closed under → and ∩ (prefixing and union of path sets) by adding states.

* ≤_G is a preorder, being the greatest simulation.
* On acyclic graphs (finite types) it coincides with BCD ≤, by induction on rank: the inductive
  path characterization is a fixpoint and it is unique on well-founded structures.
* A **regular solution** of P is an assignment of states to the variables with sS ≡_G tS for every
  equation s ≐ t.

**Theorem R.**
(a) If P has a regular solution, it has one whose letter states are elements of V∩ (abstractly
≤ 2^|Λ| letter states), with W_g := g[ρ].
(b) Regular unifiability is decidable.

*Proof (a).* Let S be a regular solution and ρ(q) := ⋂{v ∈ V : q ≤_G v}, a union of path sets.

* ρ is monotone, by transitivity of ≤_G.
* New graph: the states are g ∈ V∩ with W'_g := g[ρ], and each variable x gets the state with path
  set S(x)[ρ].
* The relation R = {(ρ-image of g, ρ-image of g') : g ≤_G g'} is a simulation in the new graph.
  If g ≤_G g', every path of g' (letters κ') has a path of g with letters κ ≥_G κ'. The images
  have letters ρκ' ≤ ρκ, and that pair is again in R.
* Commutation: for a letter subterm λ, λS ∈ V gives ρ(λS) = λS. So evaluating a problem term in
  the new graph produces exactly (term·S)[ρ].
* Every equation therefore survives.

*Proof (b).* Guess the finite skeleton: an abstract alphabet Γ (|Γ| ≤ 2^|Λ|), a preorder ⪯ on Γ, and
γ: Λ → Γ. The unknowns are finite word sets W_g (g ∈ Γ) and W_x (x a variable). The constraints are:

* the equations of P, abstractly, with letters compared by ⪯;
* W_{γ(λ)} ≡ eval(λ);
* W_g ≤ W_{g'} whenever g ⪯ g'.

The last item says exactly that ⪯ is a simulation, which gives soundness; (a) gives completeness.
This is FL0 unification over an ordered alphabet. Fact 5 reduces it to plain FL0 (quotient ⪯ to a
partial order first), and FL0 unification is decidable (Baader–Narendran). ∎

* Finite unifiability implies regular unifiability.
* The converse fails: y ≐ y→c is solved by the state Y with W_Y = {(Y;c)}, but has no finite solution.
* The whole difficulty is the passage from regular to finite.

## 3. ω-approximants of the canonical regular solution

Fix a solution S (finite or regular) and its V. Define the following.

* u^(0)_v := ω, and u^(n+1)_v := v[c^(n)].
* c^(n)(θ) := ⋂{u^(n)_v : v ∈ V, θ ≤ v}.
* τ_n(T) := T[c^(n)] for n ≥ 0, and τ_{−1}(T) := ω.

So u^(n)_v = τ_{n−1}(v) is the depth-n unfolding from ω of the canonical regular solution of
Theorem R. All of these are finite types, even when S is regular.

**Lemma 3.1.**
* c^(n) is monotone.
* u^(n) is monotone on V.
* c^(n)(v) = u^(n)_v for v ∈ V.

*Proof.* Induction on n. If θ ≤ θ', then {v ≥ θ'} ⊆ {v ≥ θ}, so c^(n) is monotone. Then fact 4
gives v ≤ v' ⇒ v[c^(n)] ≤ v'[c^(n)]. For v ∈ V, the meet defining c^(n)(v) contains u^(n)_v, and
every other meetand is ≥ u^(n)_v by monotonicity. ∎

**Lemma 3.2 (alternation).** Let ⊑ be the total order 0 ⊑ 2 ⊑ 4 ⊑ … ⊑ 5 ⊑ 3 ⊑ 1 ⊑ −1. Then
j ⊑ k implies τ_j(T) ≤ τ_k(T) for every T.

*Proof.* Ψ(u)_v := v[⋂{u_{v'} : θ ≤ v'}] is antitone, and u^(0) = ω⃗ is the top element. Induction
gives u^(n+1) ≤ u^(n+2) ≤ u^(n) for n even and u^(n) ≤ u^(n+2) ≤ u^(n+1) for n odd. So the even
terms decrease, the odd terms increase, and every odd term is ≤ every even term. The c^(n) inherit
this order and τ reverses it. τ_{−1} = ω is the top. ∎

**Lemma 3.3 (level evaluation).** For a term s and m ≥ −1, define ⟦s⟧_m:

* ⟦x⟧_m = τ_m(Sx);
* ⟦a⟧ = a, ⟦ω⟧ = ω;
* ⟦s₁∩s₂⟧_m = ⟦s₁⟧_m ∩ ⟦s₂⟧_m;
* ⟦σ→s₂⟧_m = ⟦σ⟧_{m−1} → ⟦s₂⟧_m, where ⟦σ⟧_{−1} := ω.

Then ⟦s⟧_m ≡ τ_m(sS) for all m ≥ 0. If m ≥ D(s), no cut-off ever occurs, so ⟦s⟧_m is the
occurrence-wise substitution s[o ↦ τ_{m−d(o)}(S x_o)].

*Proof.* Induction on s. The only non-trivial case is σ→s₂:
τ_m(σS → s₂S) = c^(m)(σS) → τ_m(s₂S), and c^(m)(σS) = u^(m)_{σS} (Lemma 3.1, since σS ∈ V).
This equals τ_{m−1}(σS) ≡ ⟦σ⟧_{m−1} for m ≥ 1, and ω for m = 0. ∎

**Remark (why per-variable levels are needed).** The naive choice S'(x) := S(x)[c^(n)], with the
same n for every variable, already fails on the trivially solvable y ≐ z→c with S(z) = (ω→c)→c.
It failed on about 30 of 1,593 random solvable problems. Max-canonicalization creates a spurious
cycle (z's letter ω→c ≤ Sz) and the letter z ends up one level too deep.

## 4. Theorem K: κ-aligned problems

Write P as inequalities s_i ≤ t_i (an equation is two inequalities). Decompose ∩ on the right and
drop s ≤ t when t is a ∩-conjunct of s. In particular x ≐ x∩t contributes only x ≤ t.

**Definition.** P is **κ-aligned** if there exist ℓ: Var → {−1,0,1,…} and, for each i, an integer
m_i ≥ max(D(s_i), D(t_i)) such that:

* for every occurrence of x at depth d in s_i: ℓ(x) ⊑ m_i−d if d is even, and m_i−d ⊑ ℓ(x) if d is odd;
* for every occurrence in t_i: the reverse conditions.

Only the relative order, parity and threshold of the integers matter. So κ-alignment is decidable
(it is a Presburger formula, and small solutions suffice).

**Theorem K.** Let P be κ-aligned via ℓ and let S be any finite or regular solution. Then
S'(x) := τ_{ℓ(x)}(S x) is a finite solution. Its hereditary letters lie in
{⋂_{v∈G} u^(k)_v : G ⊆ V, k ≤ N}, where N = max ℓ, so there are ≤ (N+1)·2^|Λ| of them and
letter-rank is ≤ N+1.

*Proof.* Fix i and m = m_i. Since m ≥ D, Lemma 3.3 says ⟦s_i⟧_m is the occurrence-wise
substitution with τ_{m−d}(Sx), whereas s_i S' substitutes τ_{ℓ(x)}(Sx). A term is monotone in its
even-depth occurrences and antitone in its odd-depth ones. Lemma 3.2 and the alignment conditions
therefore give s_i S' ≤ ⟦s_i⟧_m and ⟦t_i⟧_m ≤ t_i S'. Hence

s_iS' ≤ ⟦s_i⟧_m ≡ τ_m(s_iS) ≤ τ_m(t_iS) ≡ ⟦t_i⟧_m ≤ t_iS'.

The middle inequality holds because τ_m is monotone (also for ≤_G). The letter bound follows from
the definitions. ∎

**Corollary K1.** For κ-aligned P: P is finitely unifiable iff it is regularly unifiable. This is
decidable by Theorem R, and every unifiable κ-aligned P has a solution with ≤ (N+1)·2^|Λ|
hereditary letters.

**Corollary K2 (stratified problems).**
* *Definition.* P is stratified if ℓ(x) = m_e − d holds for every occurrence (the "depth graph" has
  no nonzero cycle).
* Stratified problems are κ-aligned (all relations are equalities), so they are decidable.
* Fact 5 is the special case where no variable occurs inside a letter.

**Corollary K3.** Corollary K1 also holds after replacing some variables by letter-free ground
types (ω or meets of constants), and after eliminating defined variables (x ≐ s, x ∉ s).

**Examples, hand-checked and machine-checked.**
* y→c ≤ y, y ≤ z→c: ℓ = (y:1, z:0).
* x≐y→c, y≐z→c, z≤x→c: ℓ = (2,1,0).
* x ≤ (x→c)→c: ℓ = 0.
* (x→c)→c ≤ x, x ≤ z→c: ℓ = (x:1, z:0).
* Q8 is *not* syntactically κ-aligned (the constraint y ≤ x→c would need ℓ(x) = ℓ(y)+1 ⊑ ℓ(y)−1). It is still
  semantically per-variable approximable with depths (y:1, x:2), because of absorption in x.
* y ≐ y→c, x ≐ (x→c)→c and x ≐ c∩(x→c) are *not* aligned. These are the pinned, unsolvable ones.
  Alignment does not imply solvability (y→c ≤ y, y ≤ e→c is aligned and unsolvable); it only gives
  "finite ⟺ regular".

**Empirical coverage** (random problems with ≤ 3 variables, all solutions of nf-size ≤ 7):
* 853 of 1083 solvable problems are syntactically κ-aligned.
* 1079 of 1083 are covered after instantiating the variables that are letter-free in some solution.
* The 4 leftovers are absorption effects, e.g. x ≐ (y∩x)→a with y ≤ x. The semantic version below
  handles them.
* The Theorem K construction was re-checked on every solution of every aligned problem: 0 failures.

**Semantic version.** Instead of syntactic alignment, ask for any depth vector n with
S'_n(x) := τ_{n_x}(Sx) a solution (call this **PV**).
* PV held for every one of 36,096 random solutions.
* It held for every one of about 15,000 *planted* solutions whose canonical regular system really
  oscillates (u^(n) does not stabilise).
* §5.3 shows it is nevertheless not complete.

## 5. Limits: counterexamples (rigorous)

### 5.1 The brief's fact-7 example is V-closed

For y→c ≤ y, y ≤ z→c, the variable z is also a letter variable, so S(z) = ω→c ∈ V.
Then ρ(ω→c) = S(y) ∩ S(z) = S(z), and the canonical system Y = Z→c, Z = ω→c is acyclic. The
cycle only appears if z's value is left out of V.

### 5.2 Q8: some solvable problems have no V-closed solution

Call a solution **V-closed** if every top-level letter of every S(x) is ≡ a meet of letter values.

**Q8:** y→c ≤ y, y ≤ x→c, x ≐ (y→e) ∩ (ω→c). It is solvable: y = (ω→c)→c,
x = (ω→c) ∩ (((ω→c)→c)→e) (machine-checked; it is the only solution of size ≤ 11).

**Proposition.** Q8 has no V-closed solution.

*Proof.* Let S be any solution; V = {Sy, Sx, ω}.

1. x→c ≠ ω, so Sy ≠ ω. Then y ≤ x→c gives a path (θ;c) of nf(Sy) with Sx ≤ θ.
2. y→c ≤ y forces every path of Sy to be (θ';c) with θ' ≤ Sy, so θ ≤ Sy.
3. Hence Sx ≤ Sy, and the meets of V are ω, Sx and Sy.
4. θ ≢ ω, since otherwise Sy ≡ ω.
5. θ ≢ Sy, since r(θ) < r(Sy).
6. nf(Sx) = {(nf Sy; e), (ω; c)}: the atoms differ, so no absorption. Hence r(Sx) > r(Sy) > r(θ),
   and θ ≢ Sx. ∎

So the retraction approach with Γ'₀ = V∩ needs extra letters. In Q8 the extra letter ω→c is
exactly the ω-approximant Y^(1) of the oscillating canonical letter Y = Y→c.

(Note: among 1,677 random solvable problems and 5,571 planted ones, every problem *did* have a
V-closed solution of size ≤ 7. Q8 had to be constructed by hand.)

### 5.3 P♯: per-variable approximation is incomplete

**Gadget** Godd(y, x; c, e): y→c ≤ y, y ≤ x→c, x ≐ (y→e) ∩ (ω→c) (this is Q8).

**P♯** := Godd(y₁, x₁; c, e) ∪ Godd(y₂, x₂; a, e) ∪ { t ≐ y₁ ∩ (y₂→a) }.

It is solvable:
* y₁ = (ω→c)→c, x₁ = (ω→c) ∩ (y₁→e);
* y₂ = (ω→a)→a, x₂ = (ω→a) ∩ (y₂→e);
* t = y₁ ∩ (y₂→a).

**Proposition.** For every solution S of P♯ and every ℓ ∈ {−1,0,1,…}^Var, the substitution
S'(x) := τ_{ℓ(x)}(Sx) is **not** a solution. (In particular P♯ is not κ-aligned.)

*Proof.*
1. As in 5.2, nf(Sy₁) has a letter θ with Sx₁ ≤ θ ≤ Sy₁ and θ ≢ Sx₁. Every path of θ is above a
   path of Sx₁, so θ has atoms c/e only. Sy₂ and Sx₂ are nonempty and contain a-paths, so θ is not
   below them. Hence ρθ = Sy₁.
2. Every path of Sy₁ is a length-1 c-path with letter ≤ Sy₁. So in u^(n+1)_{Sy₁} = Sy₁[c^(n)] the
   path (u^(n)_{Sy₁}; c) carries the ≤-largest letter and survives in nf. Hence
   r(u^(n+1)_{Sy₁}) > r(u^(n)_{Sy₁}), and all u^(n)_{Sy₁} are pairwise inequivalent. The same holds
   for y₂.
3. Under S', the constraint y₁→c ≤ y₁ needs u^(ℓ₁)_{Sy₁} = c^(ℓ₁)(θ) ≤ S'(y₁) = u^(ℓ₁+1)_{Sy₁}.
   * For ℓ₁ even, Lemma 3.2 gives the reverse inequality, hence equivalence, contradicting step 2.
   * ℓ₁ = −1 violates y₁ ≤ x₁→c.
   * So ℓ₁ is odd, and likewise ℓ₂ is odd.
4. Separating atoms in S'(t) ≡ S'(y₁) ∩ (S'(y₂)→a) gives
   u^(ℓ_t+1)_{Sy₁} ≡ u^(ℓ₁+1)_{Sy₁} and u^(ℓ_t)_{Sy₂} ≡ u^(ℓ₂+1)_{Sy₂}.
   By step 2, ℓ_t = ℓ₁ and ℓ_t = ℓ₂+1. That contradicts ℓ₁, ℓ₂ both odd. ∎

* *Why it fails:* t's value needs its y₁-part at level ℓ₁ and its y₂-part at level ℓ₂+1, and these
  have different parities.
* Letting t take the derived value S'(y₁) ∩ (S'(y₂)→a) fixes P♯; eliminating t (Corollary K3) has
  the same effect.
* **P♯+** := P♯ ∪ {s ≐ t→c} makes t a letter value. The same argument then defeats every scheme
  that replaces letters equal to letter values by *uniform* approximants. This includes per-
  (variable, ρ-profile) depths, which I tested.
* What works on P♯ and P♯+ is to keep letter values *structural* (machine-checked).

### 5.4 Other negative findings

* **Rank-parity heuristics.** "Approximant depth = rank(θ) + 2K, per letter" passed 14,160 random
  solutions. It is false in general: x ≤ z with x = (ω→e)→a, z = (((ω→c)→c) ∩ (ω→e))→a, plus a
  letter value (ω→e)→e. The two compared letters have ranks of different parity but the same
  oscillating ρ-image.
* **Mixed max/min canonicalization** of a *given* oscillating planted solution often fails. That
  does not contradict anything: a different solution has to be chosen.

## 6. The remaining gap

Let P be flat, so that every letter subterm is a variable. Given a solution S and depths
n: Var → ℕ, define S^Λ by recursion on rank:

S^Λ(x) := S(x)[θ ↦ Λ_x(θ)], where Λ_x(θ) := S^Λ(y) if θ ≡ S(y) for a letter variable y, and
Λ_x(θ) := c^(n_x)(θ) otherwise.

So letter values are kept structurally, and all other letters become ω-approximants of their
canonical images at the containing variable's depth.

**Conjecture Λ.** For every finite solution S of a flat P there is n, with all n_x ≤ B(|V|, |Var|),
such that S^Λ is a solution.

**Evidence.** 0 failures on:
* 18,901 random solutions (1,500 problems);
* 4,518 planted solutions with oscillating canonical system (4 variables, up to 7 constraints);
* every designed case: P♯, P♯+, Q8, P2/P7/P7' (two-atom gadgets with forced opposite parities), and
  the brief's examples.

Depths ≤ 2 always sufficed.

**Conjecture Λ ⇒ decidability (sketch, not fully checked).**
* Hereditary letters of S^Λ are either values S^Λ(y) (≤ |Var|) or approximants ⋂u^(k) with
  k ≤ max n (≤ (B+1)·2^|V|). So there are boundedly many, and fact 6 (FL0 pumping) finishes.
* Without an a-priori B: comparisons between approximants g^(i), h^(j) of a fixed regular system
  depend only on sign(i−j) and on min(i,j), and are ultimately periodic in min(i,j). The threshold
  and period are ≤ 2^(2|V∩|²), because the comparison game has only the pairs of R-letters as
  positions.
* Whether S^Λ is a solution therefore depends only on a finite pattern of n (order, residues,
  thresholds), so a small n exists.
* The structural layers add only a bounded number of descents (rank strictly decreases along
  letter-value nesting, so ≤ |V|).

**Why a proof is hard (diagnosis).**
1. After one structural step, the approximant world forgets S: comparing c^(i)(α) with c^(j)(β)
   reduces to comparing c^(j−1)(κ) with c^(i−1)(κ) for letters κ of letter values.
2. So the real ranks of α and β play no role. The constraints are pure order/parity constraints
   between depths, generated by how S's certificates use letters.
3. Their satisfiability is what has to be derived from the finiteness of S. Pinned cycles such as
   y ≐ y→c are exactly the cases where these constraints contradict each other.
4. P♯ shows the constraints cannot always be met with one depth per variable. Conjecture Λ says
   they can be met once letter values are not approximated.
5. A proof would need, for an arbitrary finite S, a potential (depth labelling) satisfying all
   order/parity constraints that S's certificates generate on non-letter-value letters. I could not
   find an invariant of finite S that provides it.
6. Real ranks do not work (§5.4), and V-profiles alone do not either, because of misaligned nesting.

**On undecidability.** Every mechanism I found is order+parity on depths (semilinear) on top of
FL0. There is no visible way to encode two counters; this agrees with NOTES.md.

## 7. Small examples requested in the task

| problem | solution | V-closed | κ-aligned (ℓ) | PV depths |
|---|---|---|---|---|
| y→c ≤ y, y ≤ z→c | y=(ω→c)→c, z=ω→c | yes | yes (1,0) | (1,0) |
| x≐y→c, y≐z→c, z≤x→c | ((ω→c)→c)→c, (ω→c)→c, ω→c | yes | yes (2,1,0) | (2,1,0) |
| (x→c)→c ≤ x, x ≤ z→c | x=(ω→c)→c, z=ω→c | yes | yes | (1,0) |
| x ≤ (x→c)→c | x=ω→c | yes | yes (0) | (0) |
| y ≐ y→c | none (regular: Y=Y→c) | – | no | – |
| x ≐ c∩(a→x) | none (tail cycle; FL0-unsolvable) | – | – | – |
| Q8 | y=(ω→c)→c, x=(ω→c)∩(((ω→c)→c)→e) | **no** (proved) | no (syntactically) | (1,2) |
| P♯ | see 5.3 | – | no | **none** (proved); Λ: yes |

## 8. Reproduction

Build: `cd /tmp/explore_B && PATH=/opt/elan/bin:$PATH lake build`, then copy the binary:
`cp .lake/build/bin/explore /tmp/exB`.

| what | command |
|---|---|
| Theorem K check / coverage | `exB kappa3 2000 777 7 60`; `exB kappa5 2000 777 7 60` |
| P♯ / P♯+ | `exB sharp 5` |
| Q8 and other designed cases | `exB designed 11 400` |
| PV, random | `exB pvrand …` |
| PV, planted oscillating | `exB planted2 20000 7 20 30 9 7 5` |
| Λ, random | `exB lrand 1500 31 7 40 4` |
| Λ, planted | `exB lplant 20000 41 20 30 9 7 4` |
| V-closedness | `exB vclosed …`; `exB pvc …` |
