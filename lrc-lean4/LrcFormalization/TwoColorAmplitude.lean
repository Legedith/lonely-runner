import LrcFormalization.SupportColoring
import LrcFormalization.OddColoring

/-!
# An explicit two-color amplitude law

There is a three-outcome sign law with both color means equal to `1/2`, zero
mixed second moment, and zero mixed moment whenever both color multiplicities
are odd. This is the exact finite law needed by an odd two-coloring.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The three atoms of the two-color sign law. -/
inductive TwoColorOutcome where
  | both
  | left
  | right
  deriving DecidableEq

/-- Probability weights `1/2, 1/4, 1/4`. -/
def twoColorWeight : TwoColorOutcome → ℝ
  | .both => 1 / 2
  | .left => 1 / 4
  | .right => 1 / 4

/-- The two sign coordinates on the three atoms. -/
def twoColorValue : Bool → TwoColorOutcome → ℝ
  | false, .both => 1
  | true, .both => 1
  | false, .left => 1
  | true, .left => -1
  | false, .right => -1
  | true, .right => 1

/-- Explicit expectation under the three-atom law. -/
def twoColorExpectation (f : TwoColorOutcome → ℝ) : ℝ :=
  twoColorWeight .both * f .both +
  twoColorWeight .left * f .left +
  twoColorWeight .right * f .right

/-- The explicit expectation as a real linear map. -/
def twoColorExpectationLinear :
    (TwoColorOutcome → ℝ) →ₗ[ℝ] ℝ where
  toFun := twoColorExpectation
  map_add' := by
    intro f g
    simp [twoColorExpectation]
    ring
  map_smul' := by
    intro a f
    simp [twoColorExpectation]
    ring

/-- The three weights sum to one. -/
theorem twoColor_weight_sum :
    twoColorWeight .both + twoColorWeight .left + twoColorWeight .right = 1 := by
  norm_num [twoColorWeight]

/-- Every weight is nonnegative. -/
theorem twoColor_weight_nonneg (o : TwoColorOutcome) : 0 ≤ twoColorWeight o := by
  cases o <;> norm_num [twoColorWeight]

/-- Every coordinate is a sign. -/
theorem twoColor_value_sign (c : Bool) (o : TwoColorOutcome) :
    twoColorValue c o = 1 ∨ twoColorValue c o = -1 := by
  cases c <;> cases o <;> simp [twoColorValue]

/-- Every coordinate is bounded by one. -/
theorem twoColor_value_bound (c : Bool) (o : TwoColorOutcome) :
    |twoColorValue c o| ≤ 1 := by
  cases c <;> cases o <;> norm_num [twoColorValue]

/-- The expectation is normalized. -/
theorem twoColor_expectation_one :
    twoColorExpectationLinear (1 : TwoColorOutcome → ℝ) = 1 := by
  norm_num [twoColorExpectationLinear, twoColorExpectation, twoColorWeight]

/-- Both colors have mean `1/2`. -/
theorem twoColor_mean (c : Bool) :
    twoColorExpectationLinear (twoColorValue c) = 1 / 2 := by
  cases c <;>
    norm_num [twoColorExpectationLinear, twoColorExpectation,
      twoColorWeight, twoColorValue]

/-- Distinct colors have zero mixed second moment. -/
theorem twoColor_pair_zero {c d : Bool} (hcd : c ≠ d) :
    twoColorExpectationLinear
      (fun o => twoColorValue c o * twoColorValue d o) = 0 := by
  cases c <;> cases d <;>
    norm_num [twoColorExpectationLinear, twoColorExpectation,
      twoColorWeight, twoColorValue] at hcd ⊢

/-- The concrete law as a `PairCancellingFamily`. -/
def twoColorPairCancellingFamily :
    PairCancellingFamily Bool TwoColorOutcome where
  expectation := twoColorExpectationLinear
  value := twoColorValue
  normalized := twoColor_expectation_one
  bound := twoColor_value_bound
  mean := 1 / 2
  commonMean := twoColor_mean
  pairZero := by
    intro c d hcd
    exact twoColor_pair_zero hcd

/-- Odd powers of a sign equal the sign. -/
theorem sign_pow_eq_self_of_odd
    {x : ℝ} (hx : x = 1 ∨ x = -1) {n : ℕ} (hn : Odd n) :
    x ^ n = x := by
  rcases hx with rfl | rfl
  · simp
  · rcases hn with ⟨k, hk⟩
    rw [hk]
    simp [pow_add, pow_mul]

/-- If both color multiplicities are odd, the corresponding mixed moment vanishes. -/
theorem twoColor_odd_odd_moment_zero
    {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    twoColorExpectationLinear
      (fun o => twoColorValue false o ^ m * twoColorValue true o ^ n) = 0 := by
  have hm' : ∀ o, twoColorValue false o ^ m = twoColorValue false o := by
    intro o
    exact sign_pow_eq_self_of_odd (twoColor_value_sign false o) hm
  have hn' : ∀ o, twoColorValue true o ^ n = twoColorValue true o := by
    intro o
    exact sign_pow_eq_self_of_odd (twoColor_value_sign true o) hn
  simp_rw [hm', hn']
  exact twoColor_pair_zero (by decide)

/-- The weighted first-level gain is exactly half of the total class mass. -/
theorem twoColor_weighted_gain (a₀ a₁ : ℝ) :
    a₀ * twoColorExpectationLinear (twoColorValue false) +
      a₁ * twoColorExpectationLinear (twoColorValue true) =
      (a₀ + a₁) / 2 := by
  rw [twoColor_mean, twoColor_mean]
  ring

end

end LonelyRunner.CorrelatedAmplitude
