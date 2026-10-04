# Working notes (intersection type unification)

Status: literature (DMR FSCD'16 / LMCS'17) says decidability is OPEN (EXPTIME-hard).

## Done in Lean
- `Resolution/Paths.lean`: path normal form, `Ty.leb` decision procedure, `Ty.le_iff_leb`,
  `DecidableRel Le`, substitution stability (`Le.subst`, `Le.csubst`), structural lemmas.

## Math facts
- Types = finite sets of paths (θ₁…θₖ; a). T ≤ T' iff ∀p'∈T' ∃p∈T, same length/atom,
  letters contravariant (θ'ᵢ ≤ θᵢ).
- WLOG solutions ground over constants of P (csubst others ↦ ω; subst vars ↦ ω).
- K-canonicalization: letters outside K (= hereditary letters of letter-variable values)
  can be replaced by ∩{κ∈K : θ ≤ κ} (monotone, commutes with problem) → WLOG all letters in K∩.
- Max-canonical letters relative to letter-variable values create CYCLES (e.g. y ≥ y→c forces
  every letter θ of y to satisfy θ ≤ y; finite solution y=(ω→c)→c, but canonical θ:=y is cyclic).
- Ordered-alphabet FL0 reduces to plain FL0: γ→z ↦ ⋂_{γ'≤γ} (γ'→z) on upsets.
- Cyclic examples: y ≤ y→c solvable (ω→c); y ≡ y→c unsolvable; thresholds live in intervals
  [λS, M]; pinned cyclic intervals are fatal, slack ones can be broken.

## Insights (session 1, continued)
- Lifting κ-abstraction (letters ↦ ∩ of fresh consts e_y per profile) works iff acyclic;
  monotone substitution ι(e_y) := S''(y) needs only POSITIVE facts y' ∈ cl(y) ⇒ S(y) ≤ S(y').
- Cycle-breaking needs approximants F^{2m+1}(ω) (odd unfoldings ≤ fixpoint); equalities through
  a letter cycle ("pinned") are fatal (y ≐ y→c). Truncation by counting free-letter nestings
  commutes with problem structure but compared positions may have misaligned counts → parity
  problems. Looks like a parity-game-flavoured condition. Hard.
- Undecidability probe agent: strong evidence for decidability (one stack only; letters only
  support monotone comparisons).

## STATUS (update) — decidability proof found (research_A + research_C), being formalized
- research_A.md: letter bound (profiles + depth-minimal reps, meet-then-join) — FORMALIZED in
  Resolution/LetterBound.lean (`letter_bound`, `letter_bound_strong`).
- research_C.md: word-length bound via abstract problem AP(D) over the finite letter set Γ
  (∩-closure of letters ∪ ω, rank = sdepth, φ_r = least rank-<r upgrade) + tower of tree automata
  (store rank-r letter labels on Λ_r*, eliminate levels by powerset/acceptance sets, pump only
  at the bottom). Verified by hand (me). To formalize:
  F1 Tower.lean (generic multi-level automata small model, induction on #levels),
  F2 Ground/Alphabet (ground solutions + Γ list with closure properties),
  F3 APD.lean (AP(D), Lemma 0/1/2 incl. size bound), F4 final bound + decision + computability.

## DONE (2026-10-04): `Intersection.decidable` proved, axioms = propext, Classical.choice, Quot.sound.
Chain: GammaExists (letter bound) → APD.complete → MLP.small_model (Tower) → APD.realize →
Final.small_ground_solution (explicit bound `bigBound`, primrec) → Decide.computablePred_of_bound.
