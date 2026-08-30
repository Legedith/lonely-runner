# Odd-Color Amplitude Filters for Lonely Runner Riesz Products

This repository contains a self-contained research note and a Lean 4 formalization of a finite cancellation mechanism for Riesz-product approaches to the Lonely Runner Conjecture.

## Main verified result

Let `(Z₀, Z₁)` take the values `(1, 1)`, `(1, -1)`, and `(-1, 1)` with probabilities `1/2`, `1/4`, and `1/4`. Each coordinate has mean `1/2`, while `E[Z₀ Z₁] = 0`.

If a finite support has even cardinality and a Boolean coloring with an odd color class, the exact mixed moment associated with its two color multiplicities vanishes. The Lean declaration is:

```lean
theorem twoColor_oddSupport_moment_zero
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V)
    (heven : Even S.card) (hodd : OddOnSupport color S) :
    twoColorExpectationLinear
      (fun o =>
        twoColorValue false o ^ colorMultiplicity color S false *
        twoColorValue true o ^ colorMultiplicity color S true) = 0
```

The package also formalizes sharp scalar filters with vanishing third, or third and fifth, moments; abstract low-level parity cancellation; and nonnegativity of the associated Riesz factors.

## Scope

This is not a proof of the full Lonely Runner Conjecture. The finite cancellation interface is formalized. The remaining tasks are arithmetic control of the odd chromatic number of the actual relation hypergraph and a complete analytic transfer.

## Website

GitHub Pages is served from the repository root:

- `index.html` — overview;
- `research.html` — self-contained research note;
- `formalization.html` — theorem map, trust boundary, and reproduction steps.

## Build

```bash
cd lrc-lean4
lake update
lake exe cache get
lake build
```

Pinned versions: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Authorship and tools

Research and formalization by Jatin Dehmiwal. GPT-5.6 Pro was used for exploratory mathematics, literature search, Lean proof engineering, and exposition. Machine checking validates the formal declarations, not the provisional novelty assessment or the unformalized analytic implications.
