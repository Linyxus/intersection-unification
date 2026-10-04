# Research C: bounding word lengths together with letters

## Result

**Theorem C.** Let P be a unifiable BCD problem. Write

* n for the number of letter-subterms of P,
* c for the number of constants of P,
* v for the number of entities of the flattened problem (§0), so v ≤ |P|.

Then P has a ground solution S″ over the constants of P with the following bounds:

* every hereditary letter of S″ has depth ≤ R := 4ⁿ;
* every path of every S″(x) has length < N*;
* every S″(x) has at most c·N*·m^{N*} paths;

where

* m := 2^{4ⁿ+1};
* q_{R+1} := 2^{c(v+m)};
* q_r := 2^{cm + q_{r+1}} for r = R, …, 1;
* N* := q_1 + q_2 + … + q_{R+1}.

Consequently the syntactic size of every S″(x) is bounded by an explicit, computable
(non-elementary) function B(P). Since ≤ is decidable, **BCD unification is decidable**: enumerate
all ground substitutions of size ≤ B(P).

The proof is conditional only on the letter bound of research_A (Lemmas 1–2 there) and on facts
1 and 3 of RESEARCH_BRIEF.md (path normal form and subtyping criterion; ∩ is meet).

**Idea in one paragraph.** Fix the finite letter set Γ of the research_A solution. Encode
every entity (problem variables and the letters themselves) by its up-set labelling over Γ-words.
Property (R′) of RESEARCH_BRIEF2.md is then exactly an invariance:

> ℓ_g(w) = ℓ_g(φ_r(w)), where r is the rank of g and φ_r is the canonical upgrade to rank < r.

Instead of pumping branch-wise on Γ* (which breaks this invariance), we *store* the labels of
rank-r letters only on the sub-trie T_r = (Γ_{<r})*. Everything at higher levels reads them
through φ_r. The φ_r form a tower of tree retractions Γ* → T_R → … → T_1. A subtree of a higher
level is therefore determined, as an input-labelled tree, by its projection to a lower level. So
each level can be eliminated by the usual "acceptance-set" (powerset) construction, as one does
for projections of tree automata. Only the bottom level T_1 has no cross-branch constraint, and
only there do we pump, with the standard minimal-height argument. Each higher level is then
re-solved inside the acceptance sets, and it becomes trivial after at most |Q_r| further steps
(least-fixed-point stratification). No pumping ever happens at a level where (R′) could break.

---

## 0. Setting and data

Types are taken modulo ≡ and identified with their path normal forms; ω is the empty path set.
A is the set of constants of P (if A = ∅, every type is ≡ ω and S ≡ ω solves P).
For a word w = (w₁,…,w_k) of types and a ∈ A, write (w;a) := w₁→…→w_k→a.
Fact 1 gives:

* (θ;a) ≤ (θ';a) iff θ'ᵢ ≤ θᵢ for all i;
* T ≤ (w;a) iff some path p of T has the same length and atom with wᵢ ≤ pᵢ for all i.

**Flattening.** Introduce an entity x_t for every subterm t of P. We get the entity set V, with
|V| = v. Every equation then has one of the forms

* x ≐ x′;
* x ≐ x₁ ∩ x₂;
* x ≐ y → z;
* x ≐ a;
* x ≐ ω.

The *letter variables* Y ⊆ V are the y occurring as y in y → z. A substitution solves P iff
its extension to V (x_t ↦ tS) satisfies the flat equations, so we work with the flat equations.

**The research_A solution.** By research_A, P has a solution S′ and a set R(Λ) of at most 4ⁿ
types with these properties:

* R(Λ) contains all hereditary letters of all S′(x) and all pins S′(y), y ∈ Y;
* R(Λ) is closed under taking letters (the letters of R(g) are of the form R(ψ(k)));
* its elements have depth ≤ 4ⁿ.

(The pins S′(y) ≡ R(ψ(yS)) lie in R(Λ) by the proof of Lemma 1.)

Let Γ be the ∩-closure of R(Λ) ∪ {ω}. Then:

* |Γ| ≤ 2^{4ⁿ+1} = m;
* Γ is closed under letters, because the letters of nf(A∩B) are letters of A or of B;
* Γ is closed under ∩ by construction;
* every element of Γ has depth ≤ R := 4ⁿ, because ∩ does not increase depth.

**Data D.** Put rk(g) := depth(g) and write ⪯ for ≤ restricted to Γ. Let γ(y) ∈ Γ be the
element with γ(y) ≡ S′(y). For r ≥ 1 let

* Λ_r := {g ∈ Γ : rk g < r} (so ω ∈ Λ_r), and Λ_{R+1} = Γ;
* T_r := Λ_r* (finite words), so T_1 ⊆ T_2 ⊆ … ⊆ T_{R+1} = Γ*;
* φ_r(h) := ⋂{k ∈ Λ_r : h ≤ k} for h ∈ Γ, extended letterwise to words.

**Lemma 0 (upgrade maps).**

(i) φ_r(h) ∈ Λ_r and h ≤ φ_r(h). Moreover, if k ∈ Λ_r and h ≤ k, then φ_r(h) ≤ k.

(ii) φ_r is the identity on Λ_r. For s ≤ r, φ_s ∘ φ_r = φ_s. As maps on words, φ_r(h::w) = φ_r(h)::φ_r(w).

(iii) Let g ∈ Γ with rk g = r ≥ 1, let w ∈ Γ* and a ∈ A. Then g ≤ (w;a) ⟺ g ≤ (φ_r w; a).
If rk g = 0, then g ≤ (w;a) implies w = [].

*Proof.*

(i) Λ_r is ∩-closed (depth(A∩B) ≤ max) and contains ω, so the meet is a nonempty meet inside Λ_r.

(ii) The identity part is clear. For s ≤ r we have Λ_s ⊆ Λ_r. For k ∈ Λ_s, h ≤ k ⟺ φ_r(h) ≤ k
by (i). Hence both meets range over the same set.

(iii) Since wᵢ ≤ φ_r(wᵢ), contravariance gives (φ_r w;a) ≤ (w;a). This proves ⇐.
For ⇒, take a path p of g with wᵢ ≤ pᵢ. Each letter pᵢ of nf(g) lies in Γ (letter-closure) and
has depth < r, so pᵢ ∈ Λ_r. By (i), φ_r(wᵢ) ≤ pᵢ.
A depth-0 type has only paths of length 0. ∎

(iii) is the precise form of (R′) and of the brief's observation "B(y,w) = B(y,φ(w))", now for all
letters at once. It was checked mechanically (§5).

## 1. The abstract problem AP(D)

Unknowns: for each entity e ∈ V ∪ Γ, a labelling ℓ_e : Γ* → 2^A.

* **(A1) Flat equations.**
  - x ≐ x′: ℓ_x = ℓ_{x′}.
  - x ≐ x₁∩x₂: ℓ_x(w) = ℓ_{x₁}(w) ∪ ℓ_{x₂}(w).
  - x ≐ y→z: ℓ_x([]) = ∅, and ℓ_x(h::w) = ℓ_z(w) if h ⪯ γ(y), ∅ otherwise.
  - x ≐ a: ℓ_x([]) = {a}, and ℓ_x(w) = ∅ for w ≠ [].
  - x ≐ ω: ℓ_x ≡ ∅.
* **(A2) Ties.** ℓ_y = ℓ_{γ(y)} for y ∈ Y.
* **(A3) Consistency.** g ⪯ g′ ⇒ ℓ_{g′}(w) ⊆ ℓ_g(w) for all w.
* **(A4) Invariance.**
  - rk g = r ≥ 1 ⇒ ℓ_g(w) = ℓ_g(φ_r w) for all w ∈ Γ*.
  - rk g = 0 ⇒ ℓ_g(w) = ∅ for w ≠ [].
* **(A5) Finite support.** There is N with ℓ_e(w) = ∅ whenever |w| ≥ N. Call the least such N
  the *support*.

**Lemma 1 (completeness).** The assignment ℓ_e(w) := {a : S′(e) ≤ (w;a)} solves AP(D). Here
S′(g) := g for g ∈ Γ, and words are read as types.

*Proof.*

(A1), cases other than →: immediate from the criterion.

(A1), case x ≐ y→z, with S′(x) ≡ γ(y) → S′(z):
* The paths of S′(x) are (γ(y), p) for paths p of S′(z), or there are none if S′(z) ≡ ω.
* (h::w; a) is dominated by such a path iff h ≤ γ(y) and wᵢ ≤ pᵢ₊₁.
* Length-0 paths are never dominated.

(A2) holds because S′(y) ≡ γ(y). (A3) is transitivity. (A4) is Lemma 0(iii). (A5) holds because
each type has finitely many paths. ∎

**Lemma 2 (soundness / realization).** Let ℓ solve AP(D) with support N. Define T_g for g ∈ Γ by
recursion on rk:

T_g := ⋂{ T(w;a) : w ∈ Λ_{rk g}*, |w| < N, a ∈ ℓ_g(w) },

where Λ₀ := ∅ and T(w;a) := T_{w₁}→…→T_{w_k}→a. The letters T_{wᵢ} have rank < rk g, so the
recursion is well founded. For every entity e put

U_e := ⋂{ T(w;a) : w ∈ Γ*, |w| < N, a ∈ ℓ_e(w) }.

Then:

(a) g ⪯ g′ ⇒ T_g ≤ T_{g′};

(b) U_g ≡ T_g for g ∈ Γ;

(c) x ↦ U_x satisfies all flat equations. Hence S″(x) := U_x, for x a variable of P, solves P.

*Proof.*

(a) By induction on max(rk g, rk g′). Let T(w;a) be a meetand of T_{g′}, so w ∈ Λ_{rk g′}* and
a ∈ ℓ_{g′}(w). By (A3), a ∈ ℓ_g(w).
* If rk g = 0, then w = [] by (A4), and a is a meetand of T_g.
* If r := rk g ≥ 1, then by (A4) a ∈ ℓ_g(φ_r w) with φ_r w ∈ Λ_r*. So T(φ_r w;a) is a meetand
  of T_g, and |φ_r w| = |w| < N.
* Moreover wᵢ ⪯ φ_r(wᵢ), and max(rk wᵢ, rk φ_r wᵢ) < max(rk g′, rk g). By induction
  T_{wᵢ} ≤ T_{φ_r wᵢ}, so by contravariance T(φ_r w;a) ≤ T(w;a).

In every case T_g ≤ T(w;a).

(b) U_g ≤ T_g, because the meetands of T_g are among those of U_g. Conversely, let a ∈ ℓ_g(w).
* If rk g = r ≥ 1, then a ∈ ℓ_g(φ_r w), so T_g ≤ T(φ_r w;a) ≤ T(w;a), using (a) on wᵢ ⪯ φ_r wᵢ.
* If rk g = 0, then w = [].

(c) The ∩, ≐, a and ω cases are immediate, since a meet over a union of index sets is the meet of
the two meets.

For x ≐ y→z: the meetands of U_x are T_h → T(w;a) with h ⪯ γ(y) and a ∈ ℓ_z(w). By (a),
T_h ≤ T_{γ(y)}, so T_{γ(y)}→τ ≤ T_h→τ. The case h = γ(y) occurs. Using
σ→(τ₁∩τ₂) ≡ (σ→τ₁)∩(σ→τ₂) and σ→ω ≡ ω, we get U_x ≡ T_{γ(y)} → U_z. By (A2) and (b),
U_y = U_{γ(y)} ≡ T_{γ(y)}, so U_x ≡ U_y → U_z.

A structural induction over the subterms of P (with x_t ≐ … for each t) then gives
tS″ ≡ U_{x_t}. ∎

Note that Lemma 2 needs nothing about the order beyond ⪯ ⊆ (realized ≤), which (a) supplies.
By Lemmas 1–2, **P is unifiable iff AP(D) is solvable**, and small solutions of AP(D) give small
solutions of P. It remains to bound the support.

## 2. AP(D) as a tower of tree automata

Write Sym_r := {g ∈ Γ : rk g = r}. A solution of AP(D) is the same thing as the following data:

* labellings f_r : T_r → (2^A)^{Sym_r} for 1 ≤ r ≤ R (the rank-r letters, stored on T_r only);
* a top labelling L : Γ* → Q_{R+1} := (2^A)^{V ∪ Γ}.

These must satisfy, for all w ∈ Γ* and h ∈ Γ:

* NV(L(w), ι(w)), where ι(w) := (f_r(φ_r w))_{1≤r≤R};
* CV(L(w), h, L(h::w));
* RV(L([]));
* finite support.

The predicates are:

* **NV(q, ι)** (node-wise conditions):
  - the ≐, ∩ and ω cases of (A1) at q;
  - (A2) and (A3) at q;
  - q_g = (ι_{rk g})_g for every g with rk g ≥ 1.
* **CV(q, h, q′)** (parent–child conditions):
  - q′_x = q_z if h ⪯ γ(y), ∅ otherwise, for x ≐ y→z;
  - q′_x = ∅ for x ≐ a;
  - q′_g = ∅ for rk g = 0.
* **RV(q)** (root conditions): q_x = ∅ for x ≐ y→z, and q_x = {a} for x ≐ a.

The correspondence is:

* (⇒) take f_r := ℓ restricted to T_r and Sym_r.
* (⇐) set ℓ_e(w) := L(w)_e.
  - (A4) holds: ℓ_g(w) = f_r(φ_r w)_g, and since φ_r(φ_r w) = φ_r w this equals ℓ_g(φ_r w).
  - For rk g = 0, CV gives ∅ at every non-root node.

The zero vector 0 satisfies NV(0,0) and CV(0,h,0). All conditions are homogeneous.

**Levels.** For r = R+1, R, …, 1 we define:

* a finite state set Q_r;
* a quiet set Z_r ⊆ Q_r;
* a root set Rt_r;
* a transition relation Δ_r(q, ι, (q_λ)_{λ∈Λ_r}), where the input ι ∈ In_r := ∏_{1≤k<r} (2^A)^{Sym_k}.

All of these are uniform, i.e. independent of the node.

*Top level, r = R+1.*

* Q_{R+1} as above.
* Δ_{R+1}(q, ι, (q_h)_{h∈Γ}) :⟺ NV(q,ι) and CV(q,h,q_h) for all h.
* Z_{R+1} := {0}.
* Rt_{R+1} := {q : RV(q)}.

*Acceptance sets.* Given level k, let 0 denote the all-∅ input. Define

* K₀ := Z_k;
* K_{j+1} := K_j ∪ {q : ∃(q_λ) ∈ K_j^{Λ_k}, Δ_k(q, 0, (q_λ))};
* Acc_k := ⋃_j K_j = K_{|Q_k|}.

*Level r ≤ R (given level r+1).*

* Q_r := (2^A)^{Sym_r} × 2^{Q_{r+1}}.
* Δ_r((F,X), ι, ((F_μ,X_μ))_{μ∈Λ_r}) holds iff for every p ∈ X there are p_λ ∈ X_{φ_r(λ)},
  for λ ∈ Λ_{r+1}, with Δ_{r+1}(p, (ι,F), (p_λ)_λ).
  (This is well typed because φ_r(λ) ∈ Λ_r for λ ∈ Λ_{r+1}.)
* Z_r := {(∅, X) : X ⊆ Acc_{r+1}}.
* Rt_r := {(F, X) : X ∩ Rt_{r+1} ≠ ∅}.

Then |Q_{R+1}| = 2^{c(v+|Γ|)} ≤ q_{R+1} and |Q_r| ≤ 2^{cm+|Q_{r+1}|} ≤ q_r.

*Runs.* Fix inputs f_1, …, f_{r−1}, where f_k : T_k → (2^A)^{Sym_k}. A level-r run on the subtree
of T_r at node u is a map ρ on {t·u : t ∈ Λ_r*} such that, at every node t·u,

Δ_r(ρ(t·u), ι_r(t·u), (ρ(μ::t·u))_μ), where ι_r(s) := (f_k(φ_k s))_{k<r}.

Its *f-part* is f_r(s) := first component of ρ(s), for r ≤ R. The run is
* *eventually quiet* if ρ(s) ∈ Z_r for all s from some depth on;
* *accepting* if moreover it is a run on all of T_r with ρ([]) ∈ Rt_r.

A top run, with inputs f_1, …, f_R, is exactly a labelling L as above, with RV for acceptance and
finite support for eventual quietness.

**Lemma 3 (quiet states are self-sustaining).**

(i) Every p ∈ Acc_k has a transition Δ_k(p, 0, (p_λ)) with all p_λ ∈ Acc_k.

(ii) For r ≤ R, every (∅,X) ∈ Z_r satisfies Δ_r((∅,X), 0, ((∅, Acc_{r+1}))_μ).

(iii) Let p ∈ Q_k. Then p ∈ Acc_k iff there is an eventually quiet level-k run starting in p on a
subtree all of whose inputs are 0.

*Proof.* By downward induction on the level.

(i), for k = R+1: 0 → 0 is a transition. For a state in K₀ = Z_k with k ≤ R, use (ii) at level k:
its children (∅, Acc_{k+1}) are quiet, hence in K₀. For a state in K_{j+1} \ K_j, use the
definition.

(ii) Follows from (i) at level r+1, because the input (0, ∅) is 0.

(iii) ⇐: let all nodes at relative depth ≥ M be quiet. By downward induction, nodes at relative
depth M − j are in K_j.
⇒: from p ∈ K_j, choose children in K_{j−1}, down to K₀, and then continue quietly using (i). ∎

**Lemma 4 (lifting is determined by the projection).** Let r ≤ R, fix inputs f_1, …, f_r, and let
s, s′ ∈ T_{r+1} with φ_r(s) = φ_r(s′) =: t. Then the map u·s ↦ u·s′ preserves the level-(r+1)
inputs.

*Proof.* The input at u·s is (f_k(φ_k(u)·φ_k(s)))_{k≤r}, and φ_k(s) = φ_k(φ_r s) = φ_k(t) by
Lemma 0(ii). ∎

So the set X^r_t := {p : some eventually quiet level-(r+1) run from p exists on the subtree at s}
depends only on t = φ_r(s).

**Lemma 5 (completeness of the tower).** If AP(D) is solvable, level 1 has an accepting,
eventually quiet run.

*Proof.* Let ℓ have support D ≥ 1, let f_r be its restrictions, and let ρ_{R+1} := L. This is an
accepting, eventually quiet top run.

Downward, for r = R, …, 1, put ρ_r(t) := (f_r(t), X^r_t). We check that ρ_r is a run:
* Let p ∈ X^r_t, with witness run ρ′ on the subtree at some s with φ_r(s) = t.
* Then p_λ := ρ′(λ::s) ∈ X^r_{φ_r(λ)::t}, because the subtree of ρ′ at λ::s is eventually quiet
  and φ_r(λ::s) = φ_r(λ)::t.
* Also Δ_{r+1}(p, (ι_r(t), f_r(t)), (p_λ)) holds, because the level-(r+1) input at s is
  (ι_r(t), f_r(t)) by Lemma 4.

It is eventually quiet: for |t| ≥ D, f_r(t) = ∅ and every input in the subtree is 0, so
X^r_t = Acc_{r+1} by Lemma 3(iii).

It is accepting: ρ_{r+1} is accepting and eventually quiet (induction), so
ρ_{r+1}([]) ∈ X^r_{[]} ∩ Rt_{r+1}. ∎

**Lemma 6 (small run at level 1).** If level 1 has an accepting, eventually quiet run, it has one
that is quiet from depth |Q_1| on.

*Proof.* Level 1 has no inputs, so Δ_1 does not depend on the node, and the standard argument
applies.

* Let ρ be the run. For a node t, let qh(t) be the least j such that every node at relative depth
  ≥ j below t is quiet.
* For a state q occurring in ρ, let H(q) := min{qh(t) : ρ(t) = q}, attained at a node t_q.
* Define ρ̃([]) := ρ([]), and ρ̃(μ::t) := ρ(μ::t_{ρ̃(t)}). Transitions are copied, so ρ̃ is an
  accepting run.
* We have H(ρ̃(μ::t)) ≤ qh(μ::t_{ρ̃(t)}) ≤ max(H(ρ̃(t)) − 1, 0).
* So along any branch, H strictly decreases until it reaches 0, through pairwise distinct states.
  That takes fewer than |Q_1| steps.
* A state with H = 0 is quiet and is followed only by such states. ∎

**Lemma 7 (unwinding with depth control).** Suppose that for some r ≤ R:
* the inputs f_1, …, f_{r−1} are fixed;
* ρ_r is an accepting level-r run, quiet from depth N_r ≥ 1;
* each f_k vanishes from depth N_k ≤ N_r.

Then there is an accepting level-(r+1) run, with inputs f_1, …, f_r (f_r the f-part of ρ_r),
that is quiet from depth N_{r+1} := N_r + |Q_{r+1}|.

*Proof.*

*Normalize.* Replace ρ_r(t) by (∅, Acc_{r+1}) for |t| ≥ N_r.
* This is still an accepting run. Δ_r is monotone in the children's X-components, Lemma 3(ii)
  covers the replaced nodes, and the root is untouched because N_r ≥ 1.
* f_r is unchanged, because quiet states have F = ∅.

*Build ρ_{r+1} top-down* with the invariant ρ_{r+1}(s) ∈ X_{φ_r(s)} (X taken from the
normalized ρ_r).
* At the root, pick a state in X_{[]} ∩ Rt_{r+1}.
* At node s with t = φ_r(s), the Δ_r-condition at t supplies children p_λ ∈ X_{φ_r(λ)::t}
  satisfying Δ_{r+1}(ρ_{r+1}(s), (ι_r(t), f_r(t)), (p_λ)). The input of level r+1 at s is
  exactly (ι_r(t), f_r(t)).
* When |s| ≥ N_r, all inputs are 0 and X_{child} = Acc_{r+1}. So if ρ_{r+1}(s) ∈ K_{j+1} \ K_j,
  we may pick children in K_j. If ρ_{r+1}(s) ∈ K₀, we pick quiet children (Lemma 3(i)).
* Since K_{|Q_{r+1}|} = Acc, the run is in K₀ = Z_{r+1} from depth N_r + |Q_{r+1}| on. ∎

**Theorem 8 (small model for AP(D)).** If AP(D) is solvable, it has a solution with support
≤ N* = Σ_{r=1}^{R+1} |Q_r|.

*Proof.*
* Lemma 5 gives an accepting, eventually quiet level-1 run.
* Lemma 6 makes it quiet from depth N_1 := |Q_1| ≥ 1.
* Lemma 7 is applied R times; the f-part of each ρ_r becomes the input f_r of the next level.
* The resulting accepting top run ρ_{R+1} is a labelling L that is 0 from depth N*.
* By NV, its letter components are the stored f_r read through φ_r.
* By §2, this gives a solution of AP(D). ∎

(When R = 0 there are no intermediate levels. The top level is T_1 = Γ* without inputs, and
Lemma 6 is ordinary FL0 pumping.)

## 3. Proof of Theorem C

* Lemma 1 shows that AP(D) is solvable.
* Theorem 8 gives a solution with support ≤ N*.
* Lemma 2 realizes it as a solution S″ of P.

The bounds follow:
* The letters of S″ are the T_h, h ∈ Γ, which have depth ≤ rk h ≤ R.
* Paths have length < N*.
* S″(x) has at most c·Σ_{k<N*} |Γ|^k ≤ c·N*·m^{N*} paths.
* Inductively, a representation of T_g with rk g = r has size at most s_r, where s_0 ≤ 2c and
  s_r ≤ c·N*·m^{N*}·(N*(s_{r−1}+1)+2).

All quantities depend only on n, c and v. ∎

## 4. How this meets the obstacle of RESEARCH_BRIEF2, and the test examples

* **Where (R′) went.** (R′) is (A4). It is never re-established after pumping. It holds by
  construction, because the labels of rank-r letters exist only on T_r and every higher node
  reads them through φ_r (the NV copy condition).
* **What replaces pumping above level 1.** Branch-wise pumping happens only on T_1, where no
  cross-branch constraint exists. Higher levels are not pumped at all. Their behaviour above a
  node t of the lower trie is summarized by the acceptance set X_t, which is legitimate by
  Lemma 4 (all fibres over t carry the same inputs). They are re-solved inside these sets.
  Depth is controlled by the stratification K_j instead of by pigeonhole on branches.
* **Relation to the suggested ideas.** This is idea (1) (a structure that respects the canonical
  maps φ) combined with idea (4) (induction on rank). The induction runs as an automaton
  construction, from the top level down for completeness and from the bottom level up for the
  construction.

**y→c ≤ y, y ≤ z→c**, with S′: y = F², z = F¹ (F(v) = v→c).
* Γ = {ω, F¹, F²} with ranks 0, 1, 2.
* φ_1 ≡ ω, φ_2(F²) = ω (since F² ≰ F¹), φ_2(F¹) = F¹.
* f_1(ω) = {c}, i.e. F¹ ≤ ω→c. f_2([F¹]) = {c}, i.e. F² ≤ F¹→c.
* At the top, ℓ_y([h]) = f_2([φ_2 h]) = {c} exactly for h = F¹. This is the up-set of F¹→c over Γ.
* The brief's problematic high-rank words, e.g. (y;c) in y ≤ y→c, are exactly these φ-copies.

**x ≐ y→c, y ≐ z→c, z ≤ x→c**: here Γ = {ω, F¹, F², F³}, a 4-level tower. The words are
short and the construction leaves the solution essentially unchanged.

**FL0-type x ≐ c ∩ (a→u), x ≤ u**: the only letters are rank-0 constants, so R = 0. This is the
pure FL0 case, covered by Lemma 6. Here the forced words are those of u, which may be ω.

**Long letter words, y ≐ a→a→c, x ≐ y→c, z ≤ x→c**: here the pin y has rank 1 and its words have
length 2. Its labels live on T_1 = (rank-0 letters)*, and x reads them via φ_1 at the top. If y
were forced to have longer words (e.g. through FL0-type constraints on a variable u with
y ≐ … ∩ u), they would be bounded at level 1 by Lemma 6. The variables that use y as a letter
are bounded at the top by Lemma 7.

The problems in the brief whose minimal solutions involve odd/even approximants (cycles) need no
special treatment. Cycles were already removed by research_A. After that, Γ, ⪯ and the ranks are
a fixed finite structure, and only the words are re-chosen.

## 5. Mechanical checks (/tmp/explore_C, commands `lift`, `liftv`, `rlift`)

The encoding (Lemmas 0, 1 and the realization identities (b) of Lemma 2) was tested as follows.
For each solution S of each problem:

* Γ is computed as the ∩-closure of the hereditary letters, the pins and ω.
* Checked: letter-closure; φ_r(h) ∈ Λ_r and h ≤ φ_r(h); the tower identity φ_s∘φ_r = φ_s.
* Checked, for all g ∈ Γ, all words w over Γ up to length (max path length + 1) and all atoms a:
  g ≤ (w;a) ⟺ g ≤ (φ_{rk g} w; a), and that rank-0 letters have only empty words.
* Checked: that ⋂ of the labelled *low-rank* words of g is ≡ g, and that ⋂ of all labelled
  Γ-words of S(x) is ≡ S(x).

Problems covered:
* the 20 hand-made problems of research_A;
* x ≐ c∩(a→u), x ≤ u;
* y ≐ a→a→c, x ≐ y→c, z ≤ x→c;
* y ≐ (a→c)∩u, y→c ≤ u;
* y ≤ a→a→c, y→c ≤ x, x ≤ z→c;
* 400 random problems.

Results: 62 + 1194 solutions, about 386,000 individual checks, **0 failures**.

The automaton part (§2) is generic finite-state reasoning and was checked by hand only. Its
state spaces (towers of exponentials) are far too large to run.

## 6. Assessment

* **Completeness.** I believe §§0–3 form a complete and rigorous proof of the requested bound,
  given research_A's Theorem. The steps that carry the weight are:
  - Lemma 0(iii), (R′) as invariance under φ — simple, and tested;
  - Lemma 2(a), monotone realization — an induction on rank that uses (A3) and (A4);
  - Lemma 4, independence of fibres — immediate from φ_k∘φ_r = φ_k;
  - Lemmas 5 and 7, the powerset elimination and unwinding of one level.
  These are standard in spirit, but the details (quiet sets, normalization at depth ≥ N_r ≥ 1
  so the root is untouched) deserve an independent check.
* **Dependencies.** The proof uses research_A (letter bound and pins ∈ R(Λ)), facts 1 and 3, and
  flattening. It does not use the FL0 / Baader–Narendran results or the ordered-alphabet
  reduction; Lemma 6 re-proves the needed pumping.
* **Consequence.** Together with research_A this yields decidability of BCD unification, which is
  stated as open in the literature (Dudenhefner–Martens–Rehof). Because of that, the whole
  chain — research_A Lemmas 1–2 and this note — should be verified independently, ideally
  formalized in Lean, before any claim is made. Everything here is finite combinatorics plus two
  structural inductions, and should be formalizable.
* **Bound quality.** The bound is a tower of exponentials of height about 4ⁿ + 2, with no attempt
  at optimality. The lower bound is EXPTIME-hardness.
