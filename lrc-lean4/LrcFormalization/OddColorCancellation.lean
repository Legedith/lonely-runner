import LrcFormalization.TwoColorAmplitude

/-!
# Exact cancellation from odd two-coloring data

This file isolates the parity argument used by the two-color amplitude law.
If a support has even size and one of its two color classes has odd size, then
both color classes have odd size. The explicit three-atom law from
`TwoColorAmplitude` then annihilates the corresponding mixed moment exactly.
Conversely, on an even support, failure of odd coloring makes both color counts
even and the mixed moment equal to one. Thus odd coloring is the exact zero-
moment condition for this law.
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

/--
For even total degree, the mixed moment vanishes exactly when at least one color
multiplicity is odd. If neither is odd, both are even and the moment is one.
-/
theorem twoColor_even_total_moment_zero_iff_odd_class
    {m n : ℕ} (heven : Even (m + n)) :
    twoColorExpectationLinear
        (fun o => twoColorValue false o ^ m * twoColorValue true o ^ n) = 0 ↔
      Odd m ∨ Odd n := by
  constructor
  · intro hzero
    by_contra hnot
    have hm_not : ¬ Odd m := by
      intro hm
      exact hnot (Or.inl hm)
    have hn_not : ¬ Odd n := by
      intro hn
      exact hnot (Or.inr hn)
    have hm_even : Even m := Nat.not_odd_iff_even.mp hm_not
    have hn_even : Even n := Nat.not_odd_iff_even.mp hn_not
    have hone := twoColor_even_even_moment_one hm_even hn_even
    rw [hone] at hzero
    norm_num at hzero
  · intro hodd
    exact twoColor_even_total_odd_class_moment_zero heven hodd

/-- The two Boolean color classes partition a finite support. -/
theorem bool_colorMultiplicity_sum
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V) :
    colorMultiplicity color S false + colorMultiplicity color S true = S.card := by
  simpa [colorMultiplicity] using
    (Finset.sum_filter_add_sum_filter_not S
      (fun v => color v = false) (fun _ : V => (1 : ℕ)))

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

/--
On an even finite support, odd two-coloring is equivalent to exact cancellation
under the explicit three-atom law.
-/
theorem twoColor_oddSupport_iff_moment_zero
    {V : Type*} [DecidableEq V]
    (color : V → Bool) (S : Finset V) (heven : Even S.card) :
    OddOnSupport color S ↔
      twoColorExpectationLinear
        (fun o =>
          twoColorValue false o ^ colorMultiplicity color S false *
          twoColorValue true o ^ colorMultiplicity color S true) = 0 := by
  constructor
  · intro hodd
    exact twoColor_oddSupport_moment_zero color S heven hodd
  · intro hzero
    have hsum : Even
        (colorMultiplicity color S false + colorMultiplicity color S true) := by
      rw [bool_colorMultiplicity_sum]
      exact heven
    have hcounts :
        Odd (colorMultiplicity color S false) ∨
          Odd (colorMultiplicity color S true) :=
      (twoColor_even_total_moment_zero_iff_odd_class hsum).mp hzero
    rcases hcounts with hfalse | htrue
    · exact ⟨false, hfalse⟩
    · exact ⟨true, htrue⟩

end

end LonelyRunner.CorrelatedAmplitude
