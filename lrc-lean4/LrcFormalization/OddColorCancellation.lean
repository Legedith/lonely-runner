import LrcFormalization.TwoColorAmplitude

/-!
# Exact cancellation from odd two-coloring data

This file isolates the parity argument used by the two-color amplitude law.
If a support has even size and one of its two color classes has odd size, then
both color classes have odd size.  The explicit three-atom law from
`TwoColorAmplitude` then annihilates the corresponding mixed moment exactly.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- In an even total, if either summand is odd then both summands are odd. -/
theorem both_odd_of_even_sum_of_one_odd
    {m n : ℕ} (heven : Even (m + n)) (hone : Odd m ∨ Odd n) :
    Odd m ∧ Odd n := by
  have hiff : Odd m ↔ Odd n := Nat.even_add'.mp heven
  rcases hone with hm | hn
  · exact ⟨hm, hiff.mp hm⟩
  · exact ⟨hiff.mpr hn, hn⟩

/--
The explicit two-color law kills every mixed monomial whose total degree is
even and for which at least one color multiplicity is odd.
-/
theorem twoColor_even_total_odd_class_moment_zero
    {m n : ℕ} (heven : Even (m + n)) (hone : Odd m ∨ Odd n) :
    twoColorExpectationLinear
      (fun o => twoColorValue false o ^ m * twoColorValue true o ^ n) = 0 := by
  have hboth := both_odd_of_even_sum_of_one_odd heven hone
  exact twoColor_odd_odd_moment_zero hboth.1 hboth.2

end

end LonelyRunner.CorrelatedAmplitude
