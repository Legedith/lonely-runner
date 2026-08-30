import LrcFormalization.OddMomentFilter

/-!
# Exact low-level cancellation by parity

The graph-sign law kills even clique moments. An independent scalar law kills
odd moments. Moment factorization then annihilates every designated level.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- If a moment factors and either factor vanishes, the combined moment vanishes. -/
theorem factored_moment_zero {scalar sign combined : ℝ}
    (hfactor : combined = scalar * sign)
    (hzero : scalar = 0 ∨ sign = 0) :
    combined = 0 := by
  rcases hzero with hs | hz
  · simp [hfactor, hs]
  · simp [hfactor, hz]

/--
For the `K = 5` filter, levels `2`, `3`, and `4` vanish: even levels are
annihilated by the graph-sign factor and level `3` by the scalar filter.
-/
theorem levels_two_to_four_vanish
    (signMoment combinedMoment : ℕ → ℝ)
    (hfactor : ∀ k, combinedMoment k = oddFilter3Moment k * signMoment k)
    (hsign2 : signMoment 2 = 0)
    (hsign4 : signMoment 4 = 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk5 : k < 5) :
    combinedMoment k = 0 := by
  have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl
  · rw [hfactor, hsign2]
    ring
  · rw [hfactor, oddFilter3Moment_three]
    ring
  · rw [hfactor, hsign4]
    ring

/-- For the `K = 7` filter, every level from `2` through `6` vanishes exactly. -/
theorem levels_two_to_six_vanish
    (signMoment combinedMoment : ℕ → ℝ)
    (hfactor : ∀ k, combinedMoment k = oddFilter5Moment k * signMoment k)
    (hsign2 : signMoment 2 = 0)
    (hsign4 : signMoment 4 = 0)
    (hsign6 : signMoment 6 = 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk7 : k < 7) :
    combinedMoment k = 0 := by
  have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · rw [hfactor, hsign2]
    ring
  · rw [hfactor, oddFilter5Moment_three]
    ring
  · rw [hfactor, hsign4]
    ring
  · rw [hfactor, oddFilter5Moment_five]
    ring
  · rw [hfactor, hsign6]
    ring

end

end LonelyRunner.CorrelatedAmplitude
