# Lean 4 formalization of the odd-color amplitude interface

This package formalizes the finite, hypothesis-transparent part of a proposed
Riesz-product method for the Lonely Runner Conjecture.

The main theorem is `twoColor_oddSupport_iff_moment_zero`: for an even finite
support, odd Boolean coloring is equivalent to exact zero mixed moment under an
explicit three-atom correlated sign law. The reverse direction is also checked:
if the support is not odd-colored, both color counts are even and the moment is
exactly one.

The package additionally proves:

* normalization, boundedness, and mean `1/2` for the explicit two-color law;
* zero odd–odd moment and unit even–even moment;
* bounded affine amplitudes and abstract pair cancellation;
* the scalar square-root obstruction;
* pullback of cancellation through support colorings;
* sharp scalar filters with zero third, or zero third and fifth, moments;
* abstract parity cancellation through low Riesz levels;
* pointwise nonnegativity of the associated Riesz factors and finite products.

It does **not** claim a proof of the Lonely Runner Conjecture or of the
conditional asymptotic transfer. Those require substantial Fourier-analytic and
additive-combinatorial results not encoded here, including control of the odd
coloring of the actual arithmetic relation hypergraph.

Pinned versions: Lean 4.33.1 and Mathlib v4.33.1.
