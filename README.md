# Intersection type unification is decidable

Unification of intersection types with constants, modulo the BCD subtyping relation, asks
whether a finite system of equations between types has a substitution making both sides of
every equation equal up to mutual subtyping. Dudenhefner, Martens and Rehof studied this
problem ("The Intersection Type Unification Problem", FSCD 2016; LMCS 2017) and left its
decidability open. This repository contains a machine-checked proof, in Lean 4 with Mathlib,
that the problem is decidable.

## What is proved

```lean
theorem Intersection.decidable : ComputablePred Intersection.Unifiable
```

stated in `Resolution.lean` and proved via `Intersection.decidable_final` in
`Resolution/Final.lean`. The definitions of types, subtyping, substitution, problems and
unifiability, together with the numbering of types that fixes what "computable" means, are in
`Intersection/Basic.lean` and take 145 lines. The proof is kernel-checked. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`, and contains no `sorry` and no
`native_decide`.

## Structure of the proof

The modules under `Resolution/`, in dependency order:

| Module | Content |
| --- | --- |
| `Paths` | The path normal form of types and the verified subtyping decider `Ty.leb`. |
| `Computability` | The decider and the type constructors are primitive recursive in the numbering `Ty.toNat`. |
| `Lattice` | The join of two types, the least upper bound for BCD subtyping. |
| `LetterMap` | Letter maps `mapLetters`: a unifier composed letterwise with a monotone map that fixes the pins is again a unifier. |
| `LetterBound` | Semantic depth and reduced representatives; the selection lemma; the transfer lemma; the letter bound (at most `4^n` letters). |
| `GammaData` | The interface for the finite letter set `Γ`: `∩`-closed, letter-closed, deduplicated up to equivalence. |
| `GammaExists` | Construction of `Γ` from the letter bound, with `|Γ| ≤ 2^(4^n+1)`. |
| `MLP` | Multi-level problems: a generic class of labelling problems on words over a finite alphabet with projections. |
| `Tower` | The small-model theorem for multi-level problems: elimination of a level by the acceptance-set construction, pumping at the bottom, the bound `towerBound`. |
| `APDBase` | Ranks of letters, the upgrade maps `phi`, and the abstract problem as a multi-level problem (node, parent–child and root conditions). |
| `APD` | Completeness of the abstract problem (the canonical solution from a unifier) and its realisation (a ground unifier of size at most `realizeBound` from a solution). |
| `Decide` | The bounded search `smallCheck` and decidability from a primitive recursive size bound. |
| `Final` | The bound `bigBound`, the small ground unifier theorem, and the final assembly. |

## Building

The project uses Lean `v4.34.0` and Mathlib `v4.34.0` (see `lean-toolchain` and
`lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

To check the axioms of the main theorem after building:

```sh
scripts/check-axioms.sh
```

which runs `lake env lean Check.lean` and fails unless the output is exactly

```
'Intersection.decidable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The GitHub Actions workflow in `.github/workflows/build.yml` does both on every push.

## Provenance

The proof was produced by Claude Opus 5.5 (Anthropic) on 3–4 October 2026 in a single
session, from the definitions in `Intersection/Basic.lean` alone, as a task of the
frontier-formal benchmark. The first commit of this repository is the run's output
unchanged; the second commit adds comments and this scaffolding and changes no proof. A paper
describing the proof is in preparation.

## Authors

Claude Opus 5.5 and Yichen Xu.

## License

Apache License 2.0, see `LICENSE`.
