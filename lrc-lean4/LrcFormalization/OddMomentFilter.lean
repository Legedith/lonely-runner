import Mathlib

/-!
# Sharp finite odd-moment filters

The scalar filter is independent of the graph-sign filter. Its odd moments
annihilate the odd Riesz levels. This file certifies the sharp filters needed
for cutoffs `K = 5` and `K = 7`, together with matching upper bounds.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The two-atom scalar filter that kills the third moment. -/
def oddFilter3Value : Bool → ℝ
  | false => 1 / 2
  | true => -1

/-- Probability weights for `oddFilter3Value`. -/
def oddFilter3Weight : Bool → ℝ
  | false => 8 / 9
  | true => 1 / 9

/-- Expectation under the two-atom third-moment filter. -/
def oddFilter3Expectation (f : Bool → ℝ) : ℝ :=
  oddFilter3Weight false * f false + oddFilter3Weight true * f true

/-- The two weights form a probability law. -/
theorem oddFilter3_weight_sum :
    oddFilter3Weight false + oddFilter3Weight true = 1 := by
  norm_num [oddFilter3Weight]

/-- Every weight in the two-atom law is nonnegative. -/
theorem oddFilter3_weight_nonneg (b : Bool) : 0 ≤ oddFilter3Weight b := by
  cases b <;> norm_num [oddFilter3Weight]

/-- The two-atom filter is supported in `[-1,1]`. -/
theorem oddFilter3_value_bound (b : Bool) : |oddFilter3Value b| ≤ 1 := by
  cases b <;> norm_num [oddFilter3Value]

/-- The sharp surviving mean for a filter with zero third moment is `1/3`. -/
theorem oddFilter3_mean :
    oddFilter3Expectation oddFilter3Value = 1 / 3 := by
  norm_num [oddFilter3Expectation, oddFilter3Weight, oddFilter3Value]

/-- The third moment vanishes exactly. -/
theorem oddFilter3_third_moment :
    oddFilter3Expectation (fun b => oddFilter3Value b ^ 3) = 0 := by
  norm_num [oddFilter3Expectation, oddFilter3Weight, oddFilter3Value]

/-- The moment function of the two-atom filter. -/
def oddFilter3Moment (k : ℕ) : ℝ :=
  oddFilter3Expectation (fun b => oddFilter3Value b ^ k)

@[simp] theorem oddFilter3Moment_one : oddFilter3Moment 1 = 1 / 3 := by
  simpa [oddFilter3Moment] using oddFilter3_mean

@[simp] theorem oddFilter3Moment_three : oddFilter3Moment 3 = 0 := by
  simpa [oddFilter3Moment] using oddFilter3_third_moment

/-- `sqrt 5`, named to keep the exact three-atom formulas readable. -/
def sqrtFive : ℝ := Real.sqrt 5

@[simp] theorem sqrtFive_sq : sqrtFive ^ 2 = 5 := by
  simpa [sqrtFive] using Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)

theorem sqrtFive_nonneg : 0 ≤ sqrtFive := by
  exact Real.sqrt_nonneg 5

theorem one_lt_sqrtFive : 1 < sqrtFive := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem sqrtFive_lt_three : sqrtFive < 3 := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

/-- Three atoms for the sharp filter with zero third and fifth moments. -/
inductive OddFilter5Atom where
  | endpoint
  | positive
  | negative
  deriving DecidableEq

/-- Support points of the `N = 5` Chebyshev filter. -/
def oddFilter5Value : OddFilter5Atom → ℝ
  | .endpoint => 1
  | .positive => (sqrtFive - 1) / 4
  | .negative => -(sqrtFive + 1) / 4

/-- Probability weights of the `N = 5` Chebyshev filter. -/
def oddFilter5Weight : OddFilter5Atom → ℝ
  | .endpoint => 1 / 25
  | .positive => 4 * (3 + sqrtFive) / 25
  | .negative => 4 * (3 - sqrtFive) / 25

/-- Expectation under the three-atom fifth-moment filter. -/
def oddFilter5Expectation (f : OddFilter5Atom → ℝ) : ℝ :=
  oddFilter5Weight .endpoint * f .endpoint +
  oddFilter5Weight .positive * f .positive +
  oddFilter5Weight .negative * f .negative

/-- The three exact weights sum to one. -/
theorem oddFilter5_weight_sum :
    oddFilter5Weight .endpoint + oddFilter5Weight .positive +
      oddFilter5Weight .negative = 1 := by
  simp [oddFilter5Weight]
  ring

/-- Every weight in the three-atom law is nonnegative. -/
theorem oddFilter5_weight_nonneg (a : OddFilter5Atom) : 0 ≤ oddFilter5Weight a := by
  cases a <;> simp [oddFilter5Weight] <;>
    nlinarith [sqrtFive_nonneg, sqrtFive_lt_three]

/-- The three-atom filter is supported in `[-1,1]`. -/
theorem oddFilter5_value_bound (a : OddFilter5Atom) : |oddFilter5Value a| ≤ 1 := by
  rw [abs_le]
  cases a <;> simp [oddFilter5Value] <;>
    constructor <;> nlinarith [sqrtFive_nonneg, sqrtFive_lt_three]

/-- The sharp surviving mean with zero third and fifth moments is `1/5`. -/
theorem oddFilter5_mean :
    oddFilter5Expectation oddFilter5Value = 1 / 5 := by
  simp only [oddFilter5Expectation, oddFilter5Weight, oddFilter5Value]
  rw [show
      1 / 25 * 1 +
          (4 * (3 + sqrtFive) / 25) * ((sqrtFive - 1) / 4) +
          (4 * (3 - sqrtFive) / 25) * (-(sqrtFive + 1) / 4) =
        (2 * sqrtFive ^ 2 - 5) / 25 by ring]
  rw [sqrtFive_sq]
  norm_num

/-- The third moment of the three-atom filter vanishes exactly. -/
theorem oddFilter5_third_moment :
    oddFilter5Expectation (fun a => oddFilter5Value a ^ 3) = 0 := by
  simp only [oddFilter5Expectation, oddFilter5Weight, oddFilter5Value]
  rw [show
      1 / 25 * 1 ^ 3 +
          (4 * (3 + sqrtFive) / 25) * (((sqrtFive - 1) / 4) ^ 3) +
          (4 * (3 - sqrtFive) / 25) * ((-(sqrtFive + 1) / 4) ^ 3) =
        ((sqrtFive - 1) * (sqrtFive + 1) * (sqrtFive ^ 2 - 5)) / 200 by ring]
  rw [sqrtFive_sq]
  norm_num

/-- The fifth moment of the three-atom filter vanishes exactly. -/
theorem oddFilter5_fifth_moment :
    oddFilter5Expectation (fun a => oddFilter5Value a ^ 5) = 0 := by
  simp only [oddFilter5Expectation, oddFilter5Weight, oddFilter5Value]
  rw [show
      1 / 25 * 1 ^ 5 +
          (4 * (3 + sqrtFive) / 25) * (((sqrtFive - 1) / 4) ^ 5) +
          (4 * (3 - sqrtFive) / 25) * ((-(sqrtFive + 1) / 4) ^ 5) =
        ((sqrtFive ^ 2 - 5) ^ 2 * (sqrtFive ^ 2 + 5)) / 3200 by ring]
  rw [sqrtFive_sq]
  norm_num

/-- The moment function of the three-atom Chebyshev filter. -/
def oddFilter5Moment (k : ℕ) : ℝ :=
  oddFilter5Expectation (fun a => oddFilter5Value a ^ k)

@[simp] theorem oddFilter5Moment_one : oddFilter5Moment 1 = 1 / 5 := by
  simpa [oddFilter5Moment] using oddFilter5_mean

@[simp] theorem oddFilter5Moment_three : oddFilter5Moment 3 = 0 := by
  simpa [oddFilter5Moment] using oddFilter5_third_moment

@[simp] theorem oddFilter5Moment_five : oddFilter5Moment 5 = 0 := by
  simpa [oddFilter5Moment] using oddFilter5_fifth_moment

/-- Chebyshev's sharp upper bound when the third moment vanishes. -/
theorem mean_le_one_third_of_third_moment_zero
    {Ω : Type*}
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (X : Ω → ℝ)
    (hEone : E (1 : Ω → ℝ) = 1)
    (hEpos : ∀ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) → 0 ≤ E f)
    (hlower : ∀ ω, -1 ≤ X ω)
    (hthird : E (fun ω => X ω ^ 3) = 0) :
    E X ≤ 1 / 3 := by
  let Q : Ω → ℝ := fun ω => 1 + 4 * X ω ^ 3 - 3 * X ω
  have hQ : ∀ ω, 0 ≤ Q ω := by
    intro ω
    dsimp [Q]
    rw [show 1 + 4 * X ω ^ 3 - 3 * X ω =
        (X ω + 1) * (2 * X ω - 1) ^ 2 by ring]
    exact mul_nonneg (by linarith [hlower ω]) (sq_nonneg _)
  have hnonneg := hEpos Q hQ
  have hfun : Q =
      (1 : Ω → ℝ) + 4 • (fun ω => X ω ^ 3) + (-3 : ℝ) • X := by
    funext ω
    simp [Q]
    ring
  rw [hfun] at hnonneg
  simp only [map_add, map_smul] at hnonneg
  rw [hEone, hthird] at hnonneg
  norm_num at hnonneg ⊢
  linarith

/-- Chebyshev's sharp upper bound when the third and fifth moments vanish. -/
theorem mean_le_one_fifth_of_odd_moments_zero
    {Ω : Type*}
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (X : Ω → ℝ)
    (hEone : E (1 : Ω → ℝ) = 1)
    (hEpos : ∀ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) → 0 ≤ E f)
    (hupper : ∀ ω, X ω ≤ 1)
    (hthird : E (fun ω => X ω ^ 3) = 0)
    (hfifth : E (fun ω => X ω ^ 5) = 0) :
    E X ≤ 1 / 5 := by
  let Q : Ω → ℝ := fun ω =>
    1 + 20 * X ω ^ 3 - 16 * X ω ^ 5 - 5 * X ω
  have hQ : ∀ ω, 0 ≤ Q ω := by
    intro ω
    dsimp [Q]
    rw [show 1 + 20 * X ω ^ 3 - 16 * X ω ^ 5 - 5 * X ω =
        (1 - X ω) * (4 * X ω ^ 2 + 2 * X ω - 1) ^ 2 by ring]
    exact mul_nonneg (sub_nonneg.mpr (hupper ω)) (sq_nonneg _)
  have hnonneg := hEpos Q hQ
  have hfun : Q =
      (1 : Ω → ℝ) + 20 • (fun ω => X ω ^ 3) +
        (-16 : ℝ) • (fun ω => X ω ^ 5) + (-5 : ℝ) • X := by
    funext ω
    simp [Q]
    ring
  rw [hfun] at hnonneg
  simp only [map_add, map_smul] at hnonneg
  rw [hEone, hthird, hfifth] at hnonneg
  norm_num at hnonneg ⊢
  linarith

end

end LonelyRunner.CorrelatedAmplitude
