# Research A: a computable bound on the number of hereditary letters

**Result (claimed, with complete proof below).** Let P be a unifiable BCD problem and let n be
the number of distinct letter-subterms of P (subterms σ that occur as σ in some σ→τ of P),
so n ≤ |P|. Then P has a solution S' such that

* S' has **at most 4ⁿ distinct hereditary letters**, and
* every hereditary letter of S' has letter-nesting depth **at most 4ⁿ**.

In fact *any* solution S can be turned into such an S'. The map that does this depends only
on the finite set Π of values of the letter-subterms under S. It is not a retraction onto
old letters. Each letter is sent to a **minimal-depth representative of its "profile"** with
respect to Π. Monotonicity comes from a ∨∩ (join-of-meets) combination that only combines
representatives of no greater depth.

Everything below is self-contained. I use only fact 1 (path normal form and the subtyping
criterion) and fact 3 (types mod ≡ form a lattice: ∩ is meet, J is join). I re-prove the
transfer step (facts 4/6) in the form I need. I have not used the minimal certificate
preorder, and I did not need it.

---

## 0. Conventions

* Types are taken modulo ≡ and are represented by their normal form nf (an antichain of paths
  (θ₁…θ_k; a) with each θ_i in normal form). Atoms are constants. ω is the empty path set.
* **depth**: depth(T) = 0 if every path of nf(T) has length 0 (so T is ω or a meet of
  constants). Otherwise depth(T) = 1 + max depth of a letter of nf(T). This is ≡-invariant,
  and the letters of nf(T) have depth < depth(T).
  For any path-set representation of T, depth(T) is at most the syntactic depth of that
  representation (nf only deletes dominated paths and normalises letters recursively). Hence:
  - depth(A ∩ B) ≤ max(depth A, depth B), because the path set of A∩B is the union;
  - depth(A ∨ B) ≤ max(depth A, depth B), because the join J(A,B) (fact 3) is represented by
    paths whose letters are p_i ∩ q_i with p, q paths of A, B.
* J really is the least upper bound. A ≤ J because p ≤ (p∩q) letterwise. If A, B ≤ C, then
  for a path r of C pick p ≤ r in A and q ≤ r in B. Then r_i ≤ p_i ∩ q_i, so the
  (p∩q)-path of J is ≤ r.
* **Pins.** Fix a solution S. Π := {λS : λ a letter-subterm of P}, a finite set of types
  with |Π| ≤ n.

## 1. Transfer lemma (a direct form of facts 4 and 6)

**Lemma 1.** Let ψ : Types → Types satisfy:

1. (monotone) θ ≤ θ' ⇒ ψ(θ) ≤ ψ(θ');
2. (pins) ψ(π) ≡ π for every π ∈ Π;
3. (depth) depth(ψ(k)) ≤ depth(k) for every type k.

Let Λ := image(ψ). Then P has a solution S' whose hereditary letters all lie in R(Λ). Here
R is defined below, so S' has at most |Λ| distinct hereditary letters, and their nesting depth
is at most the length of the longest chain in Λ under strictly decreasing depth (≤ |Λ|).

*Proof.* Define R on Λ by recursion on depth:
R(g) := nf(g) with every letter k replaced by R(ψ(k)).
This is well-founded because a letter k of nf(g) has depth(ψ(k)) ≤ depth(k) < depth(g)
by (3), and ψ(k) ∈ Λ.

*R is monotone on Λ.* Induction on max(depth g, depth g'). Suppose g ≤ g'. Every path p' of g'
is dominated by a path p of g of the same shape, with p'_i ≤ p_i. By (1), ψ(p'_i) ≤ ψ(p_i).
Both lie in Λ and have depth < max(depth g, depth g'), so by induction
R(ψ(p'_i)) ≤ R(ψ(p_i)). Therefore the replaced path of g dominates the replaced path of g'.

For an arbitrary type T, let Φ(T) be T (any path representation) with each letter k replaced
by R(ψ(k)). The letter map k ↦ R(ψ(k)) is monotone, so Φ is monotone (same argument). In
particular Φ is well defined on ≡-classes and commutes with ∩, with constants and with ω.

Put S'(x) := Φ(S(x)).

*Claim: tS' ≡ Φ(tS) for every subterm t of P.* By structural induction on t.
* Variables, constants, ω, ∩: immediate.
* t = λ→τ: here tS' = λS' → τS' ≡ λS' → Φ(τS), and Φ(λS → τS) = R(ψ(λS)) → Φ(τS).
  By induction λS' ≡ Φ(λS). Since λS ∈ Π, (2) gives ψ(λS) ≡ λS, hence
  R(ψ(λS)) = Φ(ψ(λS)) ≡ Φ(λS) ≡ λS'.

So sS ≡ tS implies sS' ≡ Φ(sS) ≡ Φ(tS) ≡ tS', and S' is a solution.

The letters of Φ(T) and of R(g) are of the form R(ψ(k)) ∈ R(Λ). Normalisation only deletes
paths. Hence every hereditary letter of S' lies in R(Λ). Along a letter chain of S' the
"source" depth in Λ strictly decreases, which gives the depth bound. ∎

The brief's earlier canonical maps fail exactly at hypothesis (3). For example, the upper
retraction c(θ) = ∩{π ≥ θ} can raise depth, which is what produces the cyclic systems.

## 2. The selection lemma

For a type x put Lo(x) := {π∈Π : π ≤ x}, Hi(x) := {π∈Π : x ≤ π}, and p(x) := (Lo(x), Hi(x))
(its **profile**). Let Prof := {p(x) : x a type}; it has at most 4^{|Π|} elements.

Order profiles by q ≤ q' :⇔ Lo_q ⊆ Lo_{q'} and Hi_q ⊇ Hi_{q'}. Then x ≤ x' ⇒ p(x) ≤ p(x').

For q ∈ Prof let I(q) := {x : Lo(x) ⊇ Lo_q, Hi(x) ⊇ Hi_q}, the convex set of types lying
above all of Lo_q and below all of Hi_q. It is nonempty. Put d(q) := min{depth x : x ∈ I(q)}
and fix x_q ∈ I(q) with depth(x_q) = d(q). Define

* g_q := ⋂ { x_s : s ∈ Prof, s ≥ q, d(s) ≤ d(q) } (this includes s = q);
* c_q := ⋁ { g_r : r ∈ Prof, r ≤ q, d(r) ≤ d(q) } (this includes r = q);
* ψ(x) := c_{p(x)}.

**Lemma 2.**
(a) g_q ∈ I(q) and c_q ∈ I(q).
(b) depth(c_q) = d(q).
(c) q ≤ q' ⇒ c_q ≤ c_{q'}.
(d) Consequently ψ satisfies (1), (2) and (3) of Lemma 1, and |image ψ| ≤ |Prof| ≤ 4^{|Π|}.

*Proof.*
(a) Take s ≥ q. Then Lo_s ⊇ Lo_q, so x_s ≥ π for all π ∈ Lo_q. A meet of elements ≥ π is
≥ π, so g_q ≥ every π ∈ Lo_q. Also g_q ≤ x_q ≤ every π ∈ Hi_q. So g_q ∈ I(q).
Now take r ≤ q. Then Hi_r ⊇ Hi_q, and g_r ∈ I(r) gives g_r ≤ π for all π ∈ Hi_q. A join of
elements ≤ π is ≤ π, so c_q ≤ every π ∈ Hi_q. Finally c_q ≥ g_q ≥ every π ∈ Lo_q.

(b) Every x_s used in g_q has depth ≤ d(q), and every g_r used in c_q has depth ≤ d(r) ≤ d(q).
Meets and joins do not increase depth, so depth(c_q) ≤ d(q). Since c_q ∈ I(q), equality holds.

(c) Let q ≤ q', and take a joinand g_r of c_q (so r ≤ q and d(r) ≤ d(q)).
* If d(r) ≤ d(q'): since r ≤ q ≤ q', g_r is also a joinand of c_{q'}.
* If d(r) > d(q'): the index set {s ≥ q', d(s) ≤ d(q')} is contained in
  {s ≥ r, d(s) ≤ d(r)}. Therefore g_r ≤ g_{q'} ≤ c_{q'}.

Hence c_q ≤ c_{q'}.

(d) Monotone: x ≤ x' ⇒ p(x) ≤ p(x') ⇒ ψ(x) ≤ ψ(x').
Pins: π ∈ Lo(π) ∩ Hi(π), so I(p(π)) = {≡ π} and ψ(π) ≡ π.
Depth: k ∈ I(p(k)), so depth ψ(k) = d(p(k)) ≤ depth(k). ∎

**Theorem.** If P is unifiable, it has a solution with at most 4ⁿ distinct hereditary letters,
all of nesting depth ≤ 4ⁿ, where n = number of distinct letter-subterms of P. Moreover the
letter system of fact 6 can be taken to have |Γ| ≤ 4ⁿ.
*Proof.* Lemma 2 followed by Lemma 1. ∎

**Finite / constructive variant (retraction form).** Let U be the sublattice (closed under ∩
and J) generated by Π ∪ {ω} ∪ the hereditary letters of S. U is finite, because a finitely
generated distributive lattice is finite. U is letter-closed, because the letters of a meet
are letters of its arguments and the letters of a join are meets of letters.

Lemma 2 holds verbatim with every type replaced by an element of U (I(q) ∩ U, minimum
depth taken in U, and Prof the profiles realised in U). The proof only uses closure under
∩, ∨ and letters. Lemma 1 only needs ψ on the letters of S and of elements of image ψ, and
those lie in U. So the answer to the brief's question is:

* a **mixed retraction of the lattice generated by the hereditary letters onto at most 4ⁿ
  elements** always works;
* the retraction must use **joins** and **depth-minimal interval representatives**, not
  just meets of letter-variable values.

## 3. The test examples

Write F^k = F^k(ω), with F(v) = v→c.

* **y→c ≤ y, y ≤ z→c**, with the non-minimal solution y = F⁴, z = F¹. Π = {F⁴, F¹}.
  - The letter F³ of y has profile ({F¹},{F⁴}). Its interval is [F¹, F⁴], and the only
    depth-1 element there is F¹, so ψ(F³) = F¹.
  - F¹'s letter ω has the top profile, so ψ(ω) = ω.
  - Result: y' = F², z' = F¹, which is the minimal solution. The upper retraction gives the
    cycle F⁴ → F⁴ instead.
* **x ≐ y→c, y ≐ z→c, z ≤ x→c**, solution x = F³, y = F², z = F¹. Every letter is a pin or ω,
  ψ is the identity on them, and there are 4 letters.
* **(x→c)→c ≤ x, x ≤ z→c**, with the non-minimal solution x = F⁴, z = F¹.
  Π = {F⁴, F⁵, F¹}.
  - The letter F³ of x has profile ({F¹},{F⁴,F⁵}), interval [F¹, F⁵], minimal depth 1 at F¹.
  - Result: x' = F², z' = F¹, the minimal solution.
* **y ≐ y→c**. There is no solution, so the construction never starts. The only "solution"
  is the cyclic system, whose pin would need a letter ≡ itself. A finite type cannot have
  that, and Lemma 1 (3) rules it out.
* **y ≤ y→c, y→c ≤ y combinations.** Here the upper retraction fails for some solutions
  and the lower retraction fails for others:
  - Upper fails for y→c ≤ y: the case above.
  - Lower fails for y ≤ y→c together with w ≐ v→c, with solution y = F³, v = (F¹∩a)→c
    (hand-checked). Then ∨{π ≤ F²} = F³, so F³ uses F³.
  - The profile construction handles both. In the second case the interval [F³, v] has
    minimal depth 2, so there is no cycle.

## 4. Why simpler variants fail (found with the explorer)

Code is in /tmp/explore_A/Main.lean. Commands: `retract`, `rretract`, `synth`, `synth2`,
`dm`, `dmfixed`, `synthdm`.

* **Upper retraction onto Γ'₀** (∩-closure of the pins plus ω) is cyclic for about 2–4% of
  all solutions of random problems. For example it is cyclic for 14 of the 18 solutions of
  y→c ≤ y, y ≤ z→c that have size ≤ 9.
* **Profile-meet without a depth threshold**, i.e. ψ(h) = ⋂{m(q) : q ≥ p(h)} with m(q) a
  minimal-depth representative, is cyclic in 13 of about 280,000 solutions. Example:
  - Problem: z→x ≤ z, x→x ≤ y. Solution: x = (c∩ω→c)→c, z = c∩(c→c)→c, y = ω.
  - The letter c→c has profile (∅,{π_x}). The higher profile ({π_z},{π_x}), with interval
    [π_z, π_x], has minimal depth 2 and representative π_z.
  - Then (c→c) ∩ π_z = c ∩ c→c ∩ (c→c)→c, which contains the letter c→c again, so it uses
    itself.
  - The condition d(s) ≤ d(q) in g_q is exactly what excludes this.
* **The construction of §2** was implemented over the finite lattice U, with the new solution
  realised and every equation of P re-checked. Results:
  - about 107,000 solutions of 3,200 random problems, plus 806 solutions of the 20 hand-made
    problems: 0 failures. The checks were pins fixed, no depth increase, monotonicity,
    acyclicity, and validity of the realised solution. The largest |Λ| was 16, with at most
    4 pins.
  - about 5,700 synthetic (U, Π) pairs, with full monotonicity checked over all of U: 0
    failures.

## 5. Assessment

* **I believe this is a complete, rigorous answer to the core question.** The proof is
  elementary: the depth-respecting ∨∩ selection plus a structural induction. It uses only
  facts 1 and 3, which I re-checked: the subtyping criterion with incomparable constants and
  ω on top, and J as the least upper bound. It needs neither the minimal certificate preorder
  nor the choice of a minimal solution.
* **Consequence (not verified by me in detail).** By the brief's fact 6 and its claim that,
  once the alphabet is bounded, the remaining problem is FL0 unification over an ordered
  alphabet (decidable via Baader–Narendran), this would make BCD unification decidable,
  which is open in the literature.
* **That FL0 step should be checked carefully before anything is announced.** In particular
  check:
  - the per-atom decomposition;
  - the reduction from ordered alphabets to plain FL0;
  - the rank restriction "W_g uses only letters of rank < r(g)", i.e. per-variable alphabet
    restrictions in FL0. I expect this is harmless for the looping-tree-automaton method,
    but I did not check it.
* Because the conclusion is strong, an independent check of Lemma 2 (c) and of the claim in
  Lemma 1 is worthwhile; these are the two load-bearing steps. A Lean formalisation looks
  feasible, since everything is finite lattice algebra plus one structural induction.
