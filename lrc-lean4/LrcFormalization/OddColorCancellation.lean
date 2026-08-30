import LrcFormalization.TwoColorAmplitude

/-!
# Exact cancellation from odd two-coloring data

This file isolates the parity argument used by the two-color amplitude law.
If a support has even size and one of its two color classes has odd size, then
both color classes have odd size. The explicit three-atom law from
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

/-- The two Boolean color classes partition a finite support. -/
theorem bool_colorMultiplicity_sum
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V) :
    colorMultiplicity color S false + colorMultiplicity color S true = S.card := by
  induction S using Finset.induction_on with
  | empty => simp [colorMultiplicity]
  | @insert a S ha ih =>
      cases hca : color a <;>
        simp [colorMultiplicity, ha, hca, ih, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

/--
An odd two-coloring of an even finite support annihilates its exact color-count
moment under the explicit three-atom law.
-/
theorem twoColor_oddSupport_moment_zero
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V)
    (heven : Even S.card) (hodd : OddOnSupport color S) :
    twoColorExpectationLinear
      (fun o =>
        twoColorValue false o ^ colorMultiplicity color S false *
        twoColorValue true o ^ colorMultiplicity color S true) = 0 := by
  apply twoColor_even_total_odd_class_moment_zero
  · rw [bool_colorMultiplicity_sum]
    exact heven
  · rcases hodd with ⟨c, hc⟩
    cases c
    · exact Or.inl hc
    · exact Or.inr hc

end

end LonelyRunner.CorrelatedAmplitude
