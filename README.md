# Odd-Color Amplitude Filters for Lonely Runner Riesz Products

This repository contains a self-contained research note and a Lean 4 formalization of a finite cancellation interface for Riesz-product approaches to the Lonely Runner Conjecture.

## Main verified result

Let `(Z₀, Z₁)` take the values `(1, 1)`, `(1, -1)`, and `(-1, 1)` with probabilities `1/2`, `1/4`, and `1/4`. Each coordinate has mean `1/2`, while `E[Z₀ Z₁] = 0`.

For every even finite support, odd coloring is exactly the zero-moment condition:

```lean
theorem twoColor_oddSupport_iff_moment_zero
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V) (heven : Even S.card) :
    OddOnSupport color S ↔
      twoColorExpectationLinear
        (fun o =>
          twoColorValue false o ^ colorMultiplicity color S false *
          twoColorValue true o ^ colorMultiplicity color S true) = 0
```

Mathematically,

```text
E[∏ x ∈ S, Z_(color x)] = 0
    iff
some color occurs an odd number of times in S,
```

provided `|S|` is even. If the support is not odd-colored, both color multiplicities are even and the mixed moment is exactly `1`.

The package also formalizes sharp scalar filters with vanishing third, or third and fifth, moments; abstract low-level parity cancellation; bounded amplitudes; and nonnegativity of the associated Riesz factors.

## What is new

The individual ingredients are not claimed as new: Riesz products, phase randomization, odd hypergraph coloring, and Chebyshev-type moment inequalities all predate this work.

The contribution is their exact synthesis for Lonely Runner Riesz products:

1. harmful low-order signed relations are encoded by their supports as a hypergraph;
2. the explicit positive-mean sign law detects odd coloring exactly, not merely sufficiently;
3. an independent scalar filter separates the odd support levels from the even support levels;
4. failure of odd two-colorability has an exact `F₂` certificate: an odd family of relation supports with empty symmetric difference.

A targeted search of public papers, arXiv, and public code through 31 August 2026 found no earlier Lonely Runner construction using this complete interface. This supports a provisional public-priority claim, not an assertion that unpublished or differently phrased equivalent work cannot exist.

## Scope

This is not a proof of the full Lonely Runner Conjecture. The finite cancellation interface is formalized. The remaining tasks are arithmetic control of the odd-color structure of the actual relation hypergraph and a complete analytic transfer.

## Website

GitHub Pages is served from the repository root:

- `index.html` — overview and precise novelty statement;
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

Research and formalization by Jatin Dehmiwal. GPT-5.6 Pro was used for exploratory mathematics, literature search, Lean proof engineering, and exposition. Machine checking validates the formal declarations, not the priority assessment or the unformalized analytic implications.
