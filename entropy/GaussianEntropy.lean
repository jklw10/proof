import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import entropy.GaussianBase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

open Real
open MeasureTheory
open Set
open Filter Topology
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section

/-- Analytical expansion of standard normal log density. -/
lemma log_standard_normal_pdf (x : ℝ) :
    log (standard_normal_pdf x) = - (1/2) * log (2 * Real.pi) - x^2 / 2 := by
  dsimp [standard_normal_pdf]
  -- Use the explicit Real namespace to avoid type mismatches
  rw [Real.log_mul]
  · have h_inv : log (1 / sqrt (2 * Real.pi)) = - (1/2) * log (2 * Real.pi) := by
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Real.log_one, Real.log_sqrt (by positivity)]
      ring
    rw [h_inv, Real.log_exp]
    ring
  · -- Prove the first term inside log_mul is non-zero
    positivity
  · -- Prove the exp term is non-zero
    exact exp_ne_zero _

/-- The standard normal PDF is integrable over the real line. -/
lemma integrable_standard_normal_pdf : Integrable standard_normal_pdf := by
  unfold standard_normal_pdf
  apply Integrable.const_mul
  have h_eq : (fun x : ℝ => exp (- x^2 / 2)) = (fun x : ℝ => exp (- (1/2 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  rw [h_eq]
  exact integrable_exp_neg_mul_sq (by positivity)

/-- Pointwise bound: x^2 is bounded by 4 * exp(x^2 / 4). -/
lemma x_sq_le_four_mul_exp (x : ℝ) : x^2 ≤ 4 * exp (x^2 / 4) := by
  have h := Real.add_one_le_exp (x^2 / 4)
  have h2 : x^2 / 4 ≤ x^2 / 4 + 1 := by linarith
  have h3 : x^2 / 4 ≤ exp (x^2 / 4) := le_trans h2 h
  have h4 : 4 * (x^2 / 4) ≤ 4 * exp (x^2 / 4) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have h5 : 4 * (x^2 / 4) = x^2 := by ring
  rwa [h5] at h4


/-- x^2 * standard_normal_pdf x is integrable over the real line. -/
lemma integrable_x_sq_mul_standard_normal_pdf : Integrable (fun x : ℝ => x^2 * standard_normal_pdf x) := by
  apply Integrable.mono' (g := fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * 4 * exp (- (1/4 : ℝ) * x^2))
  · -- Prove g is integrable
    apply Integrable.const_mul
    exact integrable_exp_neg_mul_sq (by norm_num)
  · -- Prove f is strongly measurable (continuous implies strongly measurable)
    have h_cont : Continuous (fun x : ℝ => x^2 * standard_normal_pdf x) := by
      refine Continuous.mul (continuous_pow 2) standard_normal_continuous
    exact h_cont.aestronglyMeasurable
  · -- Prove pointwise bound
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h_nonneg : 0 ≤ x^2 * standard_normal_pdf x := by
      apply mul_nonneg (sq_nonneg x) (standard_normal_pos x).le
    rw [abs_of_nonneg h_nonneg]
    dsimp [standard_normal_pdf]
    have h_pos : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by
      apply le_of_lt
      apply div_pos (by norm_num)
      apply Real.sqrt_pos.mpr
      apply mul_pos (by norm_num) Real.pi_pos
    have h_exp_pos : 0 ≤ exp (- x^2 / 2) := (exp_pos _).le
    have h_le : x^2 * exp (- x^2 / 2) ≤ 4 * exp (- (1/4 : ℝ) * x^2) := by
      have h1 := x_sq_le_four_mul_exp x
      have h2 : x^2 * exp (- x^2 / 2) ≤ 4 * exp (x^2 / 4) * exp (- x^2 / 2) := by
        exact mul_le_mul_of_nonneg_right h1 h_exp_pos
      have h3 : 4 * exp (x^2 / 4) * exp (- x^2 / 2) = 4 * exp (- (1/4 : ℝ) * x^2) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring
      rwa [h3] at h2
    have h_mul := mul_le_mul_of_nonneg_left h_le h_pos
    have h_lhs : (1 / Real.sqrt (2 * Real.pi)) * (x^2 * exp (- x^2 / 2)) = x^2 * ((1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2)) := by ring
    have h_rhs : (1 / Real.sqrt (2 * Real.pi)) * (4 * exp (- (1/4 : ℝ) * x^2)) = (1 / Real.sqrt (2 * Real.pi)) * 4 * exp (- (1/4 : ℝ) * x^2) := by ring
    rw [h_lhs, h_rhs] at h_mul
    exact h_mul

/-- The auxiliary function g(x) = -x * phi(x) has derivative (x^2 - 1) * phi(x). -/
lemma auxiliary_deriv (x : ℝ) :
    HasDerivAt (fun y => -y * standard_normal_pdf y) ((x^2 - 1) * standard_normal_pdf x) x := by
  have h_prod := HasDerivAt.mul (hasDerivAt_id' x).neg (standard_normal_deriv x)
  change HasDerivAt (fun y => -y * standard_normal_pdf y)
    (-1 * standard_normal_pdf x + -x * (-x * standard_normal_pdf x)) x at h_prod
  have h_eq : -1 * standard_normal_pdf x + -x * (-x * standard_normal_pdf x) = (x^2 - 1) * standard_normal_pdf x := by
    ring
  rw [h_eq] at h_prod
  exact h_prod

/-- (x^2 - 1) * standard_normal_pdf x is integrable over the real line. -/
lemma integrable_deriv_helper : Integrable (fun x : ℝ => (x^2 - 1) * standard_normal_pdf x) := by
  -- Rewrite (x^2 - 1) * phi(x) as x^2 * phi(x) - phi(x)
  have h_eq : (fun x : ℝ => (x^2 - 1) * standard_normal_pdf x) =
              (fun x : ℝ => x^2 * standard_normal_pdf x - standard_normal_pdf x) := by
    ext x
    ring
  rw [h_eq]
  apply Integrable.sub
  · exact integrable_x_sq_mul_standard_normal_pdf
  · exact integrable_standard_normal_pdf

/-- auxiliary function g(x) = -x * phi(x) vanishes at infinity. -/
lemma tendsto_aux_atTop : Tendsto (fun x : ℝ => -x * standard_normal_pdf x) atTop (nhds 0) := by
  -- We express this as - (1 / sqrt (2 * pi)) * (x * exp(-x^2 / 2))
  have h_eq : (fun x : ℝ => -x * standard_normal_pdf x) =
              (fun x : ℝ => - (1 / Real.sqrt (2 * Real.pi)) * (x * exp (- (1/2 : ℝ) * x^2))) := by
    ext x
    dsimp [standard_normal_pdf]
    ring_nf
  rw [h_eq]
  -- Constant factor doesn't affect the limit of 0
  have h_lim : Tendsto (fun x : ℝ => x * exp (- (1/2 : ℝ) * x^2)) atTop (nhds 0) := by
    have h_lim1 : Tendsto (fun x : ℝ => |x| ^ (1 : ℝ) * exp (- (1/2 : ℝ) * x^2)) (cocompact ℝ) (nhds 0) := by
      exact tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num) 1
    have h_lim2 : Tendsto (fun x : ℝ => |x| ^ (1 : ℝ) * exp (- (1/2 : ℝ) * x^2)) atTop (nhds 0) := by
      exact h_lim1.mono_left atTop_le_cocompact
    have h_eq2 : (fun x : ℝ => x * exp (- (1/2 : ℝ) * x^2)) =ᶠ[atTop] (fun x : ℝ => |x| ^ (1 : ℝ) * exp (- (1/2 : ℝ) * x^2)) := by
      filter_upwards [eventually_ge_atTop 0] with x hx
      have hx_abs : |x| = x := abs_of_nonneg hx
      rw [hx_abs, Real.rpow_one]
    rw [tendsto_congr' h_eq2]
    exact h_lim2

  have h_scaled := h_lim.const_mul (- (1 / Real.sqrt (2 * Real.pi)))
  simp only [mul_zero] at h_scaled
  exact h_scaled


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_Ioi_eq_integral_Ici (a : ℝ) (f : ℝ → E) :
    (∫ x in Ioi a, f x) = ∫ x in Ici a, f x := by
  -- Unfold the set integral definition to expose the underlying restricted measures
  change (∫ x, f x ∂(volume.restrict (Ioi a))) = ∫ x, f x ∂(volume.restrict (Ici a))
  -- Rewrite the domain using the almost-everywhere equality of the sets
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici]

/-- The integral over the whole real line of the auxiliary derivative is zero by odd symmetry. -/
lemma integral_deriv_eq_zero : ∫ x : ℝ, (x^2 - 1) * standard_normal_pdf x = 0 := by
  have h_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi

  let f := fun x : ℝ => (x^2 - 1) * standard_normal_pdf x

  have h_split : ∫ x : ℝ, f x = (∫ x in Set.Ioi 0, f x) + ∫ x in Set.Iic 0, f x := by
    rw [← integral_add_compl h_meas integrable_deriv_helper, compl_Ioi]

  have h_even : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f, standard_normal_pdf]
    ring_nf

  have h_left_ray : ∫ x in Set.Iic 0, f x = ∫ x in Set.Ioi 0, f x := by
    have h_reflect := integral_comp_neg_Iic (0 : ℝ) f
    simp only [neg_zero] at h_reflect
    rw [← h_reflect]
    congr 1
    ext x
    exact (h_even x).symm

  have h_double : ∫ x : ℝ, f x = 2 * ∫ x in Set.Ioi 0, f x := by
    rw [h_split, h_left_ray]
    ring

  have h_ray_zero : ∫ x in Set.Ioi 0, f x = 0 := by
    have h_ftc : ∫ x in Set.Ioi 0, f x = 0 - (- (0 : ℝ) * standard_normal_pdf 0) := by
      refine integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => auxiliary_deriv x)
        integrable_deriv_helper.integrableOn tendsto_aux_atTop
    rw [h_ftc]
    ring

  rw [h_double, h_ray_zero, mul_zero]


/-- The second moment of the standard normal distribution is 1. -/
lemma standard_normal_second_moment : ∫ x : ℝ, x^2 * standard_normal_pdf x = 1 := by
  have h_split : (fun x : ℝ => x^2 * standard_normal_pdf x) =
                 (fun x : ℝ => (x^2 - 1) * standard_normal_pdf x + standard_normal_pdf x) := by
    ext x
    ring
  rw [h_split]
  rw [integral_add]
  · rw [integral_deriv_eq_zero, zero_add, standard_normal_integral_eq_one]
  · exact integrable_deriv_helper
  · exact integrable_standard_normal_pdf


/-- The exact evaluation of the continuous differential entropy of the standard normal distribution. -/
theorem continuous_standard_normal_entropy :
    - ∫ x : ℝ, standard_normal_pdf x * log (standard_normal_pdf x) = (1/2) * log (2 * Real.pi * exp 1) := by
  -- Substitute the log expansion
  have h_integrand : (fun x : ℝ => standard_normal_pdf x * log (standard_normal_pdf x)) =
                     (fun x : ℝ => - (1/2) * log (2 * Real.pi) * standard_normal_pdf x - (1/2) * (x^2 * standard_normal_pdf x)) := by
    ext x
    rw [log_standard_normal_pdf x]
    ring
  rw [h_integrand]
  -- Split the integral
  rw [integral_sub]
  · rw [integral_const_mul, standard_normal_integral_eq_one]
    rw [integral_const_mul, standard_normal_second_moment]
    -- Simplify terms
    have h_log_e : log (2 * Real.pi * exp 1) = log (2 * Real.pi) + 1 := by
      rw [log_mul (by positivity) (exp_pos 1).ne', log_exp]
    rw [h_log_e]
    ring
  · -- Prove integrability of first term
    apply Integrable.const_mul
    exact integrable_standard_normal_pdf
  · -- Prove integrability of second term
    apply Integrable.const_mul
    exact integrable_x_sq_mul_standard_normal_pdf
