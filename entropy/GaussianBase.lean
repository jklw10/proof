import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

open Real
open MeasureTheory

noncomputable section
set_option linter.style.longLine false
set_option linter.style.emptyLine false
/-- The standard Gaussian probability density function (PDF). -/
def standard_normal_pdf (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2)

/-- The standard Gaussian is continuous everywhere. -/
lemma standard_normal_continuous : Continuous standard_normal_pdf := by
  unfold standard_normal_pdf
  refine continuous_const.mul ?_
  -- Rewrite -x^2 / 2 to -(1/2) * x^2 to avoid division-by-constant hurdles
  have h_eq : (fun x : ℝ => exp (- x^2 / 2)) = (fun x : ℝ => exp (-(1/2 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  rw [h_eq]
  refine continuous_exp.comp ?_
  refine continuous_const.mul ?_
  exact continuous_pow 2

/-- The standard Gaussian is strictly positive everywhere. -/
lemma standard_normal_pos (x : ℝ) : 0 < standard_normal_pdf x := by
  dsimp [standard_normal_pdf]
  have h_pi : 0 < 2 * Real.pi := by positivity
  have h_sqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_pi
  have h_inv : 0 < 1 / Real.sqrt (2 * Real.pi) := div_pos (by linarith) h_sqrt
  exact mul_pos h_inv (exp_pos _)

/-- The derivative of the standard Gaussian is -x * \phi(x). -/
lemma standard_normal_deriv (x : ℝ) :
    HasDerivAt standard_normal_pdf (- x * standard_normal_pdf x) x := by
  -- Use `change` to cleanly unfold the LHS function of `HasDerivAt`
  change HasDerivAt (fun y => (1 / Real.sqrt (2 * Real.pi)) * exp (- y^2 / 2)) (- x * standard_normal_pdf x) x
  -- Rewrite the expression to make chain rule easier
  have h_eq : (fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) * exp (- y^2 / 2)) =
              (fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) • exp (- (1/2 : ℝ) * y^2)) := by
    ext y
    simp only [smul_eq_mul]
    congr 2
    ring --here
  rw [h_eq]
  -- Apply derivative of exp(-b * y^2) scaled by constant
  have h_exp : HasDerivAt (fun y : ℝ => exp (- (1/2 : ℝ) * y^2)) (exp (- (1/2 : ℝ) * x^2) * (- x)) x := by
    -- Chain rule for exp (g(x))
    have h_inner : HasDerivAt (fun y : ℝ => - (1/2 : ℝ) * y^2) (- x) x := by
      have h2 : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
        have h_pow := hasDerivAt_pow 2 x
        have h_sub : 2 - 1 = 1 := rfl
        rw [h_sub, pow_one] at h_pow
        exact h_pow
      have h3 := HasDerivAt.const_mul (- (1/2 : ℝ)) h2
      -- Use congr_deriv to safely modify the derivative value without altering the function structure
      refine h3.congr_deriv ?_
      ring
    have h_outer := hasDerivAt_exp (- (1/2 : ℝ) * x^2)
    have h_comp := HasDerivAt.comp x h_outer h_inner
    exact h_comp

  have h_scaled := HasDerivAt.const_smul (1 / Real.sqrt (2 * Real.pi)) h_exp
  simp only [smul_eq_mul] at h_scaled
  -- Restructure the derivative term to match the goal
  have h_goal_eq : (1 / Real.sqrt (2 * Real.pi)) * (exp (- (1 / 2 : ℝ) * x^2) * -x) = -x * standard_normal_pdf x := by
    unfold standard_normal_pdf
    have h_arg : - x^2 / 2 = - (1/2 : ℝ) * x^2 := by ring
    rw [h_arg]
    ring --here
  rw [h_goal_eq] at h_scaled
  exact h_scaled

/-- Normalization property proven using Mathlib's `integral_gaussian` -/
theorem standard_normal_integral_eq_one : ∫ x : ℝ, standard_normal_pdf x = 1 := by
  unfold standard_normal_pdf
  rw [integral_const_mul]
  -- Rewrite exp(-x^2 / 2) as exp(- (1/2) * x^2) to match `integral_gaussian`
  have h_exp : (fun x : ℝ => exp (- x^2 / 2)) = (fun x : ℝ => exp (- (1/2 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  rw [h_exp]
  -- Use Mathlib's `integral_gaussian` with b = 1/2
  have h_int := integral_gaussian (1/2 : ℝ)
  rw [h_int]
  -- Simplify: sqrt(pi / (1/2)) = sqrt(2 * pi)
  have h_simpl : Real.sqrt (Real.pi / (1 / 2)) = Real.sqrt (2 * Real.pi) := by
    congr 1
    ring
  rw [h_simpl]
  -- Finally (1 / sqrt(2*pi)) * sqrt(2*pi) = 1
  have h_sqrt_pos : Real.sqrt (2 * Real.pi) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.mpr (by positivity)
  exact one_div_mul_cancel h_sqrt_pos
