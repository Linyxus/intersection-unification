# Research brief 2: bounding WORD LENGTHS given bounded letters

Read RESEARCH_BRIEF.md and research_A.md first. research_A.md proves (verified):

**Letter bound (Lemmas 1–2 of research_A).** If P is unifiable, it has a solution S' whose
hereditary letters lie (up to ≡) in a set of at most 4ⁿ types (n = #letter-subterms of P),
each of letter-nesting depth ≤ 4ⁿ. Construction: pins Π = values of letter-subterms;
ψ(x) := c_{profile(x)} (depth-minimal profile representatives combined by meet-then-join);
R(g) := rep(g) with each letter k replaced by R(ψ(k)) (well-founded on depth);
S'(x) := S(x) with each letter k replaced by R(ψ(k)). The measure "depth" can be replaced by
any ≡-invariant measure μ with μ(A∩B), μ(A∨B) ≤ max and letters of a minimal representative
strictly smaller; e.g. μ = height (counting both letters and tails).

**What remains for decidability: a computable bound on WORD LENGTHS (path lengths).**
Word lengths of S'(x) are those of S(x) — unbounded. Letters' own word lengths are bounded by
pin word lengths (a depth-minimal element of an interval [∨Lo, ∧Hi] of pins only needs words of
the pins' shapes), and pins are values of letter-subterms, i.e. involve variables. So
everything reduces to bounding word lengths of variables, jointly with the letters.

## The FL0 view and the obstacle
Fix the finite alphabet Γ of letters (symbols with the actual order ⪯). Represent each entity e
(variables, and letters themselves) by its up-set labelling B(e,w,a) := [T_e ≤ (w;a)] over words
w ∈ Γ*. In the trie of REVERSED words (node = reversed word; child = prepend a letter), the
flattened constraints are LOCAL: x ≐ y∩z ⇒ B(x,w)=B(y,w)∨B(z,w); x ≐ γ→z ⇒
B(x,h::w)=[h⪯γ]∧B(z,w), B(x,[])=∅; x ≐ a, x ≐ ω similar; consistency g⪯g' ⇒ B(g')⊆B(g);
ties (letter-variable y has the letter γ(y) as value) B(y)=B(γ(y)). Conversely, ANY labelling
satisfying these local constraints yields an abstract solution (word-sets = labelled words;
∩_{h⪯γ}(h→z) ≡ γ→z), and if the symbols are realized by types with an order containing ⪯ the
realized assignment solves P. Branch-wise pumping (replace the subtree at a deep node by the
subtree at a descendant with the same label-vector) preserves all local constraints and bounds
depth by the number of label-vectors. So for VARIABLES with FIXED letters this is fine
(Baader–Narendran style FL0 pumping).

THE OBSTACLE: letters are entities too (letter-variables' values are letters; letters contain
letters). To realize a symbol g after pumping we recurse on rank: T_g := ∩ realized words of
B'(g) using only symbols of rank < rank(g). This needs (R'): every labelled word of g that
contains a symbol of rank ≥ rank(g) is ⪯-above some labelled word of g using only lower-rank
symbols. (R') holds before pumping (up-sets of normal forms), but branch-wise pumping can break
it, because the witness lives in a different branch (it differs from the word at positions in
the suffix leading to the pumped node). Such "high-rank" words are unavoidable: e.g. for
y ≤ y→c with y = ω→c, the up-set of y contains (y;c) because y ⪯ ω. One cannot restrict ⪯ to
rank-monotone pairs (y ⪯ ω is needed). Pumping only below the depth of all letters' labels is
safe but then the bound depends on the letters' lengths (circular). Level-uniform pumping
(insert a fixed segment at a fixed position from the end in ALL words) preserves (R') but needs
a global repetition with no pigeonhole.
Observation: for a single pin y with symbol κ_y and other letters fixed, the (R') witness is
canonical: φ(κ_y) := ⋀{fixed letters L : κ_y ⪯ L} (in the ∩-closure), and B(y,w) = B(y,φ(w)).

## Task
Find a rigorous proof that if P is unifiable then it has a solution with all word lengths (and
hence sizes) bounded by a computable function of P — e.g. by a pumping argument compatible with
the letter structure, a smarter choice of representation, a second "profile/representative"
argument for tails, an induction on rank or on the number of letter variables, or any other
idea. Alternatively find an argument that the abstract finite structure (bounded symbols, ranks,
order) has a decidable solvability problem by other means. Be rigorous; test on examples.
