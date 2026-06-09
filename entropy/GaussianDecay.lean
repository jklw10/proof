import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import entropy.GaussianBase
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Abs

open Real
open MeasureTheory
open Set

noncomputable section
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- Helper algebraic inequality: for x ≥ 1, exp(-x^2 / 2) is bounded by exp(-x + 1/2). -/
lemma exp_bound_for_tail (x : ℝ) (hx : 1 ≤ x) : exp (- x^2 / 2) ≤ exp (- x + 1/2) := by
  have _ := hx -- satisfy linter on unused variables
  apply exp_le_exp.mpr
  -- We prove: -x^2 / 2 ≤ -x + 1/2, which is equivalent to 0 ≤ x^2 - 2x + 1 = (x - 1)^2
  have h_sq : 0 ≤ (x - 1)^2 := sq_nonneg (x - 1)
  linarith

/-- The tail integral of the standard normal PDF outside a bound b ≥ 1 is bounded exponentially. -/
lemma standard_normal_tail_decay (b : ℝ) (hb : 1 ≤ b) :
    ∫ x in Ici b, standard_normal_pdf x ≤ (1 / Real.sqrt (2 * Real.pi)) * exp (1/2) * exp (-b) := by
  dsimp [standard_normal_pdf]
  -- Factor out the constant factor
  rw [integral_const_mul]
  -- Set up inequality of integrals based on pointwise bound
  have h_le : ∫ (x : ℝ) in Ici b, exp (- x ^ 2 / 2) ≤ ∫ (x : ℝ) in Ici b, exp (- x + 1 / 2) := by
    apply setIntegral_mono_on
    · -- Integrability of the left function
      have h_int_gauss : Integrable (fun x : ℝ => exp (- x^2 / 2)) := by
        have h_eq : (fun x : ℝ => exp (- x^2 / 2)) = (fun x : ℝ => exp (- (1/2 : ℝ) * x^2)) := by
          ext x
          congr 1
          ring
        rw [h_eq]
        exact integrable_exp_neg_mul_sq (by positivity)
      exact h_int_gauss.integrableOn
    · -- Integrability of the right function
      have h_int_neg_exp : IntegrableOn (fun x : ℝ => exp (-x)) (Ici b) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        exact integrableOn_exp_neg_Ioi b
      have h_int_mul := h_int_neg_exp.const_mul (exp (1/2))
      have h_eq : (fun x : ℝ => exp (- x + 1 / 2)) = (fun x : ℝ => exp (1/2 : ℝ) * exp (-x)) := by
        ext x
        rw [add_comm, exp_add]
      rw [h_eq]
      exact h_int_mul
    · exact measurableSet_Ici
    · intro x h_mem
      rw [mem_Ici] at h_mem
      have hx1 : 1 ≤ x := le_trans hb h_mem
      exact exp_bound_for_tail x hx1

  -- Calculate the right integral using the Fundamental Theorem of Calculus
  have h_int_eval : ∫ (x : ℝ) in Ici b, exp (- x + 1 / 2) = exp (- b + 1 / 2) := by
    have h_eq : (fun x : ℝ => exp (- x + 1 / 2)) = (fun x : ℝ => exp (1/2 : ℝ) * exp (-x)) := by
      ext x
      rw [add_comm, exp_add]
    rw [h_eq]
    rw [integral_const_mul]
    rw [integral_Ici_eq_integral_Ioi]
    rw [integral_exp_neg_Ioi]
    have h_add : exp (1/2) * exp (-b) = exp (-b + 1/2) := by
      rw [← exp_add]
      congr 1
      ring
    exact h_add

  -- Rewrite the exp term on the RHS
  have h_exp_eq : exp (- b + 1 / 2) = exp (1 / 2) * exp (-b) := by
    rw [add_comm, exp_add]
  rw [h_exp_eq] at h_int_eval

  -- Combine inequalities
  have h_combined : ∫ (x : ℝ) in Ici b, exp (- x ^ 2 / 2) ≤ exp (1/2) * exp (-b) := by
    rw [← h_int_eval]
    exact h_le
  have h_const_pos : 0 < 1 / Real.sqrt (2 * Real.pi) := by
    have h_pi : 0 < 2 * Real.pi := by positivity
    have h_sqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_pi
    exact div_pos (by linarith) h_sqrt
  have h_final := mul_le_mul_of_nonneg_left h_combined (le_of_lt h_const_pos)
  have h_assoc : (1 / Real.sqrt (2 * Real.pi)) * (exp (1 / 2) * exp (-b)) =
                 (1 / Real.sqrt (2 * Real.pi)) * exp (1 / 2) * exp (-b) := by ring
  rw [h_assoc] at h_final
  exact h_final


-- =========================================================================
-- PART 3: Global Polynomial Decay Verification
-- =========================================================================

/-- Helper constant bound: 1 / √(2π) ≤ 1. -/
lemma one_div_sqrt_two_pi_le_one : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := by
  have h1 : 2 * Real.pi ≥ 1 := by
    have : Real.pi ≥ 3 := Real.pi_gt_three.le
    linarith
  have h2 : Real.sqrt (2 * Real.pi) ≥ 1 := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt h1
  have h3 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [div_le_iff₀ h3]
  linarith

/-- Global O(x⁻⁴) bound on the Gaussian using the squared exponential expansion. -/
lemma exp_bound_four (x : ℝ) : exp (- x^2 / 2) ≤ 16 / (x^4 + 16) := by
  have h1 : 1 + x^2 / 4 ≤ exp (x^2 / 4) := by linarith [Real.add_one_le_exp (x^2 / 4)]
  have h2 : 0 < 1 + x^2 / 4 := by positivity
  have h3 : (1 + x^2 / 4)^2 ≤ (exp (x^2 / 4))^2 := by gcongr
  have h4 : (exp (x^2 / 4))^2 = exp (x^2 / 2) := by
    have : (exp (x^2 / 4))^2 = exp (x^2 / 4) * exp (x^2 / 4) := by ring
    rw [this, ← Real.exp_add]
    congr 1
    ring
  rw [h4] at h3
  have h5 : (1 + x^2 / 4)^2 = 1 + x^2 / 2 + x^4 / 16 := by ring
  have h6 : 1 + x^2 / 2 + x^4 / 16 ≥ (x^4 + 16) / 16 := by
    have : 1 + x^2 / 2 + x^4 / 16 = (x^4 + 16) / 16 + x^2 / 2 := by ring
    rw [this]
    have : 0 ≤ x^2 / 2 := by positivity
    linarith
  have h7 : (1 + x^2 / 4)^2 ≥ (x^4 + 16) / 16 := by linarith [h5, h6]
  have h8 : (x^4 + 16) / 16 ≤ exp (x^2 / 2) := by linarith [h3, h7]
  have h9 : 0 < (x^4 + 16) / 16 := by positivity
  have h10 : (exp (x^2 / 2))⁻¹ ≤ ((x^4 + 16) / 16)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) h9]
    exact h8
  have h11 : (exp (x^2 / 2))⁻¹ = exp (- x^2 / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have h12 : ((x^4 + 16) / 16)⁻¹ = 16 / (x^4 + 16) := by
    rw [inv_div]
  linarith [h10, h11, h12]

/-- Global O(x⁻⁶) bound on the Gaussian using the cubed exponential expansion. -/
lemma exp_bound_six (x : ℝ) : exp (- x^2 / 2) ≤ 216 / (x^6 + 216) := by
  have h1 : 1 + x^2 / 6 ≤ exp (x^2 / 6) := by linarith [Real.add_one_le_exp (x^2 / 6)]
  have h2 : 0 < 1 + x^2 / 6 := by positivity
  have h3 : (1 + x^2 / 6)^3 ≤ (exp (x^2 / 6))^3 := by gcongr
  have h4 : (exp (x^2 / 6))^3 = exp (x^2 / 2) := by
    have : (exp (x^2 / 6))^3 = exp (x^2 / 6) * (exp (x^2 / 6) * exp (x^2 / 6)) := by ring
    rw [this, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h4] at h3
  have h5 : (1 + x^2 / 6)^3 = 1 + x^2 / 2 + x^4 / 12 + x^6 / 216 := by ring
  have h6 : 1 + x^2 / 2 + x^4 / 12 + x^6 / 216 ≥ (x^6 + 216) / 216 := by
    have : 1 + x^2 / 2 + x^4 / 12 + x^6 / 216 = (x^6 + 216) / 216 + (x^2 / 2 + x^4 / 12) := by ring
    rw [this]
    have : 0 ≤ x^2 / 2 + x^4 / 12 := by positivity
    linarith
  have h7 : (1 + x^2 / 6)^3 ≥ (x^6 + 216) / 216 := by linarith [h5, h6]
  have h8 : (x^6 + 216) / 216 ≤ exp (x^2 / 2) := by linarith [h3, h7]
  have h9 : 0 < (x^6 + 216) / 216 := by positivity
  have h10 : (exp (x^2 / 2))⁻¹ ≤ ((x^6 + 216) / 216)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) h9]
    exact h8
  have h11 : (exp (x^2 / 2))⁻¹ = exp (- x^2 / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have h12 : ((x^6 + 216) / 216)⁻¹ = 216 / (x^6 + 216) := by
    rw [inv_div]
  linarith [h10, h11, h12]


/-- Proves that the standard normal PDF decays at a polynomial rate faster than x⁻² (we choose p = 3). -/
theorem standard_normal_pdf_decay :
    ∃ (C : ℝ) (p : ℝ), 2 < p ∧ ∀ x, standard_normal_pdf x ≤ C / (1 + |x|)^p := by
  use 256, 3
  refine ⟨by norm_num, fun x => ?_⟩
  unfold standard_normal_pdf
  have h_gauss : (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2) ≤ exp (- x^2 / 2) := by
    have h_coeff : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := one_div_sqrt_two_pi_le_one
    have h_exp : 0 ≤ exp (- x^2 / 2) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_right h_coeff h_exp
    rwa [one_mul] at this
  have h_bound := exp_bound_four x
  have h_trans : (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2) ≤ 16 / (x^4 + 16) := by
    linarith [h_gauss, h_bound]
  apply le_trans h_trans
  -- Cast real power back to natural power for algebraic simplification
  have h_rpow : (1 + |x|) ^ (3 : ℝ) = (1 + |x|) ^ 3 := Real.rpow_natCast (1 + |x|) 3
  rw [h_rpow]
  -- We prove 16 / (x^4 + 16) ≤ 256 / (1 + |x|)^3 by showing (1 + |x|)^3 ≤ 16 * (x^4 + 16)
  have h_denom_pos1 : 0 < x^4 + 16 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^3 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : (1 + |x|)^3 ≤ 16 * (x^4 + 16) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · -- Case 1: |x| ≤ 1
      have h_cube_le : (1 + |x|)^3 ≤ 8 := by
        have h_pos : 0 ≤ 1 + |x| := by positivity
        have h_le : 1 + |x| ≤ 2 := by linarith
        have h_pow := pow_le_pow_left₀ h_pos h_le 3
        have h_two_cube : (2 : ℝ)^3 = 8 := by norm_num
        rwa [h_two_cube] at h_pow
      have h_denom_ge : 16 * (x^4 + 16) ≥ 256 := by
        have : x^4 ≥ 0 := by positivity
        linarith
      linarith
    · -- Case 2: |x| > 1
      have h_poly : (1 + |x|)^3 ≤ 8 * x^4 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_cube : (1 + |x|)^3 ≤ 8 * |x|^3 := by
          have h_pow : (1 + |x|)^3 ≤ (2 * |x|)^3 := by
            gcongr

          have h_ring : (2 * |x|)^3 = 8 * |x|^3 := by ring
          linarith [h_pow, h_ring]
        have h_pow : |x|^3 ≤ x^4 := by
          have h_x_ge : 1 ≤ |x| := by linarith
          have : |x|^4 = x^4 := by
            calc |x|^4 = (|x|^2)^2 := by ring
            _ = (x^2)^2 := by rw [sq_abs]
            _ = x^4 := by ring
          rw [← this]
          have h_cube_ge : 1 ≤ |x|^3 := by
            have h_one : (1 : ℝ) = 1^3 := by ring
            rw [h_one]
            gcongr

          have h_le : |x|^3 * 1 ≤ |x|^3 * |x| := by
            apply mul_le_mul_of_nonneg_left h_x_ge
            positivity
          linarith [show |x|^4 = |x|^3 * |x| by ring]
        linarith
      linarith
  linarith [h_algebraic]


/-- Proves that the derivative of standard normal PDF decays at a polynomial rate faster than x⁻¹ (we choose q = 2). -/
theorem standard_normal_deriv_decay :
    ∃ (C' : ℝ) (q : ℝ), 1 < q ∧ ∀ x, |deriv standard_normal_pdf x| ≤ C' / (1 + |x|)^q := by
  use 1728, 2
  refine ⟨by norm_num, fun x => ?_⟩
  have h_deriv_eq : deriv standard_normal_pdf x = - x * standard_normal_pdf x :=
    (standard_normal_deriv x).deriv
  rw [h_deriv_eq]
  have h_abs : |- x * standard_normal_pdf x| = |x| * standard_normal_pdf x := by
    rw [abs_mul, abs_neg, abs_of_pos (standard_normal_pos x)]
  rw [h_abs]
  unfold standard_normal_pdf
  have h_gauss : |x| * ((1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2)) ≤ |x| * exp (- x^2 / 2) := by
    have h_coeff : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := one_div_sqrt_two_pi_le_one
    have h_exp : 0 ≤ exp (- x^2 / 2) := (Real.exp_pos _).le
    have h_inner : (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2) ≤ exp (- x^2 / 2) := by
      have := mul_le_mul_of_nonneg_right h_coeff h_exp
      rwa [one_mul] at this
    exact mul_le_mul_of_nonneg_left h_inner (abs_nonneg x)
  have h_bound := exp_bound_six x
  have h_trans : |x| * ((1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2)) ≤ 216 * |x| / (x^6 + 216) := by
    have h_mul : |x| * exp (- x^2 / 2) ≤ |x| * (216 / (x^6 + 216)) := by
      apply mul_le_mul_of_nonneg_left h_bound (abs_nonneg x)
    have h_eq : |x| * (216 / (x^6 + 216)) = 216 * |x| / (x^6 + 216) := by ring
    linarith [h_gauss, h_mul, h_eq]
  apply le_trans h_trans
  -- Cast real power back to natural power for algebraic simplification
  have h_rpow : (1 + |x|) ^ (2 : ℝ) = (1 + |x|) ^ 2 := Real.rpow_natCast (1 + |x|) 2
  rw [h_rpow]
  -- We prove 216 * |x| / (x^6 + 216) ≤ 1728 / (1 + |x|)^2 by showing 216 * |x| * (1 + |x|)^2 ≤ 1728 * (x^6 + 216)
  have h_denom_pos1 : 0 < x^6 + 216 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^2 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : 216 * |x| * (1 + |x|)^2 ≤ 1728 * (x^6 + 216) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · -- Case 1: |x| ≤ 1
      have h_pow : (1 + |x|)^2 ≤ 4 := by
        have : (4 : ℝ) = 2^2 := by ring
        rw [this]
        gcongr
        linarith
      have h_x_nonneg : 0 ≤ |x| := abs_nonneg x
      have h_mul1 : |x| * (1 + |x|)^2 ≤ |x| * 4 := mul_le_mul_of_nonneg_left h_pow h_x_nonneg
      have h_mul2 : |x| * 4 ≤ 1 * 4 := mul_le_mul_of_nonneg_right h_small (by positivity)
      have h_num_le : 216 * |x| * (1 + |x|)^2 ≤ 864 := by linarith
      have h_denom_ge : 1728 * (x^6 + 216) ≥ 1728 * 216 := by
        have : x^6 ≥ 0 := by positivity
        linarith
      linarith
    · -- Case 2: |x| > 1
      have h_poly : |x| * (1 + |x|)^2 ≤ 8 * x^6 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_pow_2 : (1 + |x|)^2 ≤ (2 * |x|)^2 := by
          gcongr

        have h_pow_2' : (1 + |x|)^2 ≤ 4 * |x|^2 := by
          have h_ring : (2 * |x|)^2 = 4 * |x|^2 := by ring
          linarith [h_pow_2, h_ring]
        have h_mul : |x| * (1 + |x|)^2 ≤ |x| * (4 * |x|^2) :=
          mul_le_mul_of_nonneg_left h_pow_2' (abs_nonneg x)
        have h_cube : |x| * (1 + |x|)^2 ≤ 4 * |x| ^ 3 := by
          have h_ring2 : |x| * (4 * |x|^2) = 4 * |x|^3 := by ring
          linarith [h_mul, h_ring2]
        have h_pow : |x|^3 ≤ x^6 := by
          have h_x_ge : 1 ≤ |x| := by linarith
          have : |x| ^ 6 = x ^ 6 := by
            calc |x|^6 = (|x|^2)^3 := by ring
            _ = (x^2)^3 := by rw [sq_abs]
            _ = x^6 := by ring
          rw [← this]
          have h_cube_ge : 1 ≤ |x|^3 := by
            have h_one : (1 : ℝ) = 1^3 := by ring
            rw [h_one]
            gcongr

          have h_le : |x|^3 * 1 ≤ |x|^3 * |x|^3 := by
            apply mul_le_mul_of_nonneg_left h_cube_ge
            positivity
          linarith [show |x|^6 = |x|^3 * |x|^3 by ring]
        have h_x6_nonneg : 0 ≤ x^6 := by positivity
        linarith
      linarith
  linarith [h_algebraic]


-- =========================================================================
-- HELPER LEMMAS FOR THE GLOBAL ENTROPY DECAY PROOFS
-- =========================================================================

/-- Upper bound on log √(2π) -/
lemma log_sqrt_two_pi_le_three : Real.log (Real.sqrt (2 * Real.pi)) ≤ 3 := by
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
    have h_pi : 0 < 2 * Real.pi := by positivity
    exact Real.sqrt_pos.mpr h_pi
  rw [Real.log_le_iff_le_exp h_sqrt_pos]
  have h_pos_exp : 0 ≤ Real.exp 3 := (Real.exp_pos _).le
  have h_pos_sqrt : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  rw [← abs_of_nonneg h_pos_sqrt, ← abs_of_nonneg h_pos_exp, ← sq_le_sq]
  have h_exp_6 : (Real.exp 3)^2 = Real.exp 6 := by
    have : (Real.exp 3)^2 = Real.exp 3 * Real.exp 3 := by ring
    rw [this, ← Real.exp_add]
    congr 1
    ring
  rw [h_exp_6, Real.sq_sqrt (by positivity)]
  have h_pi_le_4 : Real.pi ≤ 4 := Real.pi_le_four
  have h2pi : 2 * Real.pi ≤ 8 := by linarith
  have h_exp_2 : 3 ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    linarith
  have h_exp_6_ge : 27 ≤ Real.exp 6 := by
    have h_cube : (3:ℝ)^3 ≤ (Real.exp 2)^3 := by gcongr
    have h_eq : (Real.exp 2)^3 = Real.exp 6 := by
      have : (Real.exp 2)^3 = Real.exp 2 * (Real.exp 2 * Real.exp 2) := by ring
      rw [this, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    linarith [h_cube, h_eq]
  linarith

/-- Lower bound on log √(2π) -/
lemma log_sqrt_two_pi_nonneg : 0 ≤ Real.log (Real.sqrt (2 * Real.pi)) := by
  have h1 : 2 * Real.pi ≥ 1 := by
    have : Real.pi ≥ 3 := Real.pi_gt_three.le
    linarith
  have h2 : Real.sqrt (2 * Real.pi) ≥ 1 := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt h1
  have h_log_one := Real.log_le_log (by positivity) h2
  rwa [Real.log_one] at h_log_one

/-- First polynomial bound for the entropy decay -/
lemma bound_term1 (x : ℝ) : 48 / (x^4 + 16) ≤ 500 / (1 + |x|)^3 := by
  have h_denom_pos1 : 0 < x^4 + 16 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^3 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : 48 * (1 + |x|)^3 ≤ 500 * (x^4 + 16) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · have h_cube_le : (1 + |x|)^3 ≤ 8 := by
        have h_pos : 0 ≤ 1 + |x| := by positivity
        have h_le : 1 + |x| ≤ 2 := by linarith
        have h_pow := pow_le_pow_left₀ h_pos h_le 3
        rwa [show (2 : ℝ)^3 = 8 by norm_num] at h_pow
      have h_left : 48 * (1 + |x|)^3 ≤ 384 := by linarith
      have h_right : 500 * (x^4 + 16) ≥ 8000 := by
        have : x^4 ≥ 0 := by positivity
        linarith
      linarith
    · have h_poly : (1 + |x|)^3 ≤ 8 * x^4 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_cube : (1 + |x|)^3 ≤ 8 * |x|^3 := by
          have h_pow : (1 + |x|)^3 ≤ (2 * |x|)^3 := by gcongr
          linarith [h_pow, show (2 * |x|)^3 = 8 * |x|^3 by ring]
        have h_pow : |x|^3 ≤ x^4 := by
          have h_x_ge : 1 ≤ |x| := by linarith
          have : |x|^4 = x^4 := by
            calc |x|^4 = (|x|^2)^2 := by ring
            _ = (x^2)^2 := by rw [sq_abs]
            _ = x^4 := by ring
          rw [← this]
          have h_cube_ge : 1 ≤ |x|^3 := by
            have h_one : (1 : ℝ) = 1^3 := by ring
            rw [h_one]
            gcongr
          have h_le : |x|^3 * 1 ≤ |x|^3 * |x| := by
            apply mul_le_mul_of_nonneg_left h_x_ge
            positivity
          linarith [show |x|^4 = |x|^3 * |x| by ring]
        linarith
      linarith
  linarith
/-- Second polynomial bound for the entropy decay -/
lemma bound_term2 (x : ℝ) : 108 * x^2 / (x^6 + 216) ≤ 1500 / (1 + |x|)^3 := by
  have h_denom_pos1 : 0 < x^6 + 216 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^3 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : 108 * x^2 * (1 + |x|)^3 ≤ 1500 * (x^6 + 216) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · have h_cube_le : (1 + |x|)^3 ≤ 8 := by
        have h_pos : 0 ≤ 1 + |x| := by positivity
        have h_le : 1 + |x| ≤ 2 := by linarith
        have h_pow := pow_le_pow_left₀ h_pos h_le 3
        rwa [show (2 : ℝ)^3 = 8 by norm_num] at h_pow
      have h_x2_le : x^2 ≤ 1 := by
        have h_eq : x^2 = |x|^2 := (sq_abs x).symm
        rw [h_eq]
        have h_one : (1 : ℝ) = 1^2 := by ring
        rw [h_one]
        gcongr
      have h_mul : x^2 * (1 + |x|)^3 ≤ 8 := by
        have h_nonneg2 : 0 ≤ (1 + |x|)^3 := by positivity
        have h_one_nonneg : 0 ≤ (1 : ℝ) := by linarith
        have := mul_le_mul h_x2_le h_cube_le h_nonneg2 h_one_nonneg
        rwa [one_mul] at this
      have h_left : 108 * x^2 * (1 + |x|)^3 ≤ 864 := by
        calc 108 * x^2 * (1 + |x|)^3
          _ = 108 * (x^2 * (1 + |x|)^3) := by ring
          _ ≤ 108 * 8 := mul_le_mul_of_nonneg_left h_mul (by linarith)
          _ = 864 := by ring
      have h_right : 1500 * (x^6 + 216) ≥ 324000 := by
        have : x^6 ≥ 0 := by positivity
        linarith
      linarith
    · have h_poly : x^2 * (1 + |x|)^3 ≤ 8 * x^6 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_cube : (1 + |x|)^3 ≤ 8 * |x|^3 := by
          have h_pow : (1 + |x|)^3 ≤ (2 * |x|)^3 := by gcongr
          linarith [h_pow, show (2 * |x|)^3 = 8 * |x|^3 by ring]
        have h_mul : x^2 * (1 + |x|)^3 ≤ x^2 * (8 * |x|^3) :=
          mul_le_mul_of_nonneg_left h_cube (sq_nonneg x)
        have h_ring : x^2 * (8 * |x|^3) = 8 * (x^2 * |x|^3) := by ring
        rw [h_ring] at h_mul
        have h_x_ge : 1 ≤ |x| := by linarith
        have : |x| ^ 6 = x ^ 6 := by
          calc |x|^6 = (|x|^2)^3 := by ring
          _ = (x^2)^3 := by rw [sq_abs]
          _ = x^6 := by ring
        have h_pow : x^2 * |x|^3 ≤ |x| ^ 6 := by
          have h_eq : x^2 * |x|^3 = |x|^5 := by
            rw [← sq_abs x]
            ring
          rw [h_eq]
          have h_pow5_ge : 1 ≤ |x|^5 := by
            have h_one : (1 : ℝ) = 1^5 := by ring
            rw [h_one]
            gcongr
          have h_le : |x|^5 * 1 ≤ |x|^5 * |x| := by
            apply mul_le_mul_of_nonneg_left h_x_ge
            positivity
          linarith [show |x|^6 = |x|^5 * |x| by ring]
        calc x^2 * (1 + |x|)^3
          _ ≤ 8 * (x^2 * |x|^3) := h_mul
          _ ≤ 8 * |x|^6 := mul_le_mul_of_nonneg_left h_pow (by linarith)
          _ = 8 * x^6 := by rw [this]
      linarith [show 108 * (x^2 * (1 + |x|)^3) = 108 * x^2 * (1 + |x|)^3 by ring, show 108 * (8 * x^6) = 864 * x^6 by ring]
  linarith


/-- First polynomial bound for the derivative decay -/
lemma bound_deriv_term1 (x : ℝ) : 48 * |x| / (x^4 + 16) ≤ 500 / (1 + |x|)^2 := by
  have h_denom_pos1 : 0 < x^4 + 16 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^2 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : 48 * |x| * (1 + |x|)^2 ≤ 500 * (x^4 + 16) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · have h_pow : (1 + |x|)^2 ≤ 4 := by
        have : (4 : ℝ) = 2^2 := by ring
        rw [this]
        gcongr
        linarith
      have h_mul1 : |x| * (1 + |x|)^2 ≤ |x| * 4 := mul_le_mul_of_nonneg_left h_pow (abs_nonneg x)
      have h_mul2 : |x| * 4 ≤ 1 * 4 := mul_le_mul_of_nonneg_right h_small (by positivity)
      have h_num_le : 48 * |x| * (1 + |x|)^2 ≤ 192 := by linarith
      have h_denom_ge : 500 * (x^4 + 16) ≥ 8000 := by
        have : x^4 ≥ 0 := by positivity
        linarith
      linarith
    · have h_poly : |x| * (1 + |x|)^2 ≤ 8 * x^4 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_pow_2 : (1 + |x|)^2 ≤ (2 * |x|)^2 := by gcongr
        have h_pow_2' : (1 + |x|)^2 ≤ 4 * |x|^2 := by
          have h_ring : (2 * |x|)^2 = 4 * |x|^2 := by ring
          linarith [h_pow_2, h_ring]
        have h_mul : |x| * (1 + |x|)^2 ≤ |x| * (4 * |x|^2) :=
          mul_le_mul_of_nonneg_left h_pow_2' (abs_nonneg x)
        have h_cube : |x| * (1 + |x|)^2 ≤ 4 * |x| ^ 3 := by
          have h_ring2 : |x| * (4 * |x|^2) = 4 * |x|^3 := by ring
          linarith [h_mul, h_ring2]
        have h_pow : |x|^3 ≤ x^4 := by
          have h_x_ge : 1 ≤ |x| := by linarith
          have : |x|^4 = x^4 := by
            calc |x|^4 = (|x|^2)^2 := by ring
            _ = (x^2)^2 := by rw [sq_abs]
            _ = x^4 := by ring
          rw [← this]
          have h_cube_ge : 1 ≤ |x|^3 := by
            have h_one : (1 : ℝ) = 1^3 := by ring
            rw [h_one]
            gcongr
          have h_le : |x|^3 * 1 ≤ |x|^3 * |x| := by
            apply mul_le_mul_of_nonneg_left h_x_ge
            positivity
          linarith [show |x|^4 = |x|^3 * |x| by ring]
        have h_x4_nonneg : 0 ≤ x^4 := by positivity
        linarith
      linarith [show 48 * (|x| * (1 + |x|)^2) = 48 * |x| * (1 + |x|)^2 by ring, show 48 * (8 * x^4) = 384 * x^4 by ring]
  linarith

/-- Second polynomial bound for the derivative decay -/
lemma bound_deriv_term2 (x : ℝ) : 108 * |x| * x^2 / (x^6 + 216) ≤ 9500 / (1 + |x|)^2 := by
  have h_denom_pos1 : 0 < x^6 + 216 := by positivity
  have h_denom_pos2 : 0 < (1 + |x|)^2 := by positivity
  rw [div_le_div_iff₀ h_denom_pos1 h_denom_pos2]
  have h_algebraic : 108 * |x| * x^2 * (1 + |x|)^2 ≤ 9500 * (x^6 + 216) := by
    rcases le_or_gt |x| 1 with h_small | h_large
    · have h_pow : (1 + |x|)^2 ≤ 4 := by
        have : (4 : ℝ) = 2^2 := by ring
        rw [this]
        gcongr
        linarith
      have h_x2_le : x^2 ≤ 1 := by
        have h_eq : x^2 = |x|^2 := (sq_abs x).symm
        rw [h_eq]
        have h_one : (1 : ℝ) = 1^2 := by ring
        rw [h_one]
        gcongr
      have h_abs_x3_le : |x| * x^2 ≤ 1 := by
        have h_eq : |x| * x^2 = |x|^3 := by rw [← sq_abs x]; ring
        rw [h_eq]
        have h_one : (1 : ℝ) = 1^3 := by ring
        rw [h_one]
        gcongr
      have h_mul : |x| * x^2 * (1 + |x|)^2 ≤ 4 := by
        calc |x| * x^2 * (1 + |x|)^2
          _ ≤ |x| * x^2 * 4 := mul_le_mul_of_nonneg_left h_pow (by positivity)
          _ = (|x| * x^2) * 4 := by ring
          _ ≤ 1 * 4 := mul_le_mul_of_nonneg_right h_abs_x3_le (by positivity)
          _ = 4 := by ring
      have h_left : 108 * |x| * x^2 * (1 + |x|)^2 ≤ 432 := by
        calc 108 * |x| * x^2 * (1 + |x|)^2
          _ = 108 * (|x| * x^2 * (1 + |x|)^2) := by ring
          _ ≤ 108 * 4 := mul_le_mul_of_nonneg_left h_mul (by linarith)
          _ = 432 := by ring
      have h_right : 9500 * (x^6 + 216) ≥ 2052000 := by
        have : x^6 ≥ 0 := by positivity
        linarith
      linarith
    · have h_poly : |x| * x^2 * (1 + |x|)^2 ≤ 8 * x^6 := by
        have h_sum : 1 + |x| ≤ 2 * |x| := by linarith
        have h_pow_2 : (1 + |x|)^2 ≤ (2 * |x|)^2 := by gcongr
        have h_pow_2' : (1 + |x|)^2 ≤ 4 * |x|^2 := by
          have h_ring : (2 * |x|)^2 = 4 * |x|^2 := by ring
          linarith [h_pow_2, h_ring]
        have h_mul : |x| * x^2 * (1 + |x|)^2 ≤ |x| * x^2 * (4 * |x|^2) :=
          mul_le_mul_of_nonneg_left h_pow_2' (by positivity)
        have h_cube : |x| * x^2 * (1 + |x|)^2 ≤ 4 * |x|^5 := by
          have h_eq : |x| * x^2 = |x|^3 := by
            rw [← sq_abs x]
            ring
          calc |x| * x^2 * (1 + |x|)^2
            _ ≤ |x| * x^2 * (4 * |x|^2) := h_mul
            _ = 4 * (|x| * x^2 * |x|^2) := by ring
            _ = 4 * (|x|^3 * |x|^2) := by rw [h_eq]
            _ = 4 * |x|^5 := by ring
        have h_pow : |x|^5 ≤ x^6 := by
          have h_x_ge : 1 ≤ |x| := by linarith
          have : |x|^6 = x^6 := by
            calc |x|^6 = (|x|^2)^3 := by ring
            _ = (x^2)^3 := by rw [sq_abs]
            _ = x^6 := by ring
          rw [← this]
          have h_five_ge : 1 ≤ |x|^5 := by
            have h_one : (1 : ℝ) = 1^5 := by ring
            rw [h_one]
            gcongr
          have h_le : |x|^5 * 1 ≤ |x|^5 * |x| := by
            apply mul_le_mul_of_nonneg_left h_x_ge
            positivity
          linarith [show |x|^6 = |x|^5 * |x| by ring]
        calc |x| * x^2 * (1 + |x|)^2
          _ ≤ 4 * |x|^5 := h_cube
          _ ≤ 4 * x^6 := mul_le_mul_of_nonneg_left h_pow (by linarith)
          _ ≤ 8 * x^6 := by
            have : 0 ≤ x^6 := by positivity
            linarith
      linarith [show 108 * (|x| * x^2 * (1 + |x|)^2) = 108 * |x| * x^2 * (1 + |x|)^2 by ring, show 108 * (8 * x^6) = 864 * x^6 by ring]
  linarith


-- =========================================================================
-- GLOBAL POLYNOMIAL DECAY PROOFS
-- =========================================================================

/-- Global polynomial decay on the Gaussian entropy density. -/
theorem gaussian_entropy_density_decay :
    ∃ (C_g : ℝ) (p_g : ℝ), 2 < p_g ∧ ∀ x, |standard_normal_pdf x * Real.log (standard_normal_pdf x)| ≤ C_g / (1 + |x|)^p_g := by
  use 2000, 3
  refine ⟨by norm_num, fun x => ?_⟩
  have h_ne1 : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≠ 0 := by
    have h_pi : 0 < 2 * Real.pi := by positivity
    have h_sqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_pi
    exact (div_pos (by linarith) h_sqrt).ne'
  have h_ne2 : exp (- x^2 / 2) ≠ 0 := (exp_pos _).ne'
  have h_log_pdf : Real.log (standard_normal_pdf x) = - Real.log (Real.sqrt (2 * Real.pi)) - x^2 / 2 := by
    have h_eq1 : standard_normal_pdf x = (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2) := rfl
    have h_div : (1 / Real.sqrt (2 * Real.pi) : ℝ) = (Real.sqrt (2 * Real.pi))⁻¹ := by ring
    rw [h_eq1, Real.log_mul h_ne1 h_ne2, h_div, Real.log_inv, Real.log_exp]
    ring

  have h_le_3 : Real.log (Real.sqrt (2 * Real.pi)) ≤ 3 := log_sqrt_two_pi_le_three
  have h_ge_0 : 0 ≤ Real.log (Real.sqrt (2 * Real.pi)) := log_sqrt_two_pi_nonneg

  have h_log_bound : |Real.log (standard_normal_pdf x)| ≤ 3 + x^2 / 2 := by
    rw [h_log_pdf]
    have h_neg : - Real.log (Real.sqrt (2 * Real.pi)) - x^2 / 2 ≤ 0 := by
      have : 0 ≤ x^2 / 2 := by positivity
      linarith [h_ge_0]
    rw [abs_of_nonpos h_neg]
    linarith [h_le_3]

  have h_entropy_le : |standard_normal_pdf x * Real.log (standard_normal_pdf x)| ≤
      standard_normal_pdf x * (3 + x^2 / 2) := by
    rw [abs_mul, abs_of_pos (standard_normal_pos x)]
    exact mul_le_mul_of_nonneg_left h_log_bound (standard_normal_pos x).le

  have h_gauss_le : standard_normal_pdf x ≤ exp (- x^2 / 2) := by
    have h_coeff : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := one_div_sqrt_two_pi_le_one
    have h_exp : 0 ≤ exp (- x^2 / 2) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_right h_coeff h_exp
    rwa [one_mul] at this

  have h_bound4 : standard_normal_pdf x ≤ 16 / (x^4 + 16) := by
    linarith [h_gauss_le, exp_bound_four x]

  have h_bound6 : x^2 * standard_normal_pdf x ≤ 216 * x^2 / (x^6 + 216) := by
    have h_mul : x^2 * standard_normal_pdf x ≤ x^2 * exp (- x^2 / 2) := by
      apply mul_le_mul_of_nonneg_left h_gauss_le (sq_nonneg x)
    have h_bound_six := exp_bound_six x
    have h_mul2 : x^2 * exp (- x^2 / 2) ≤ x^2 * (216 / (x^6 + 216)) :=
      mul_le_mul_of_nonneg_left h_bound_six (sq_nonneg x)
    have h_eq : x^2 * (216 / (x^6 + 216)) = 216 * x^2 / (x^6 + 216) := by ring
    linarith [h_mul, h_mul2, h_eq]

  have h_sum_bound : standard_normal_pdf x * (3 + x^2 / 2) ≤ 48 / (x^4 + 16) + 108 * x^2 / (x^6 + 216) := by
    calc standard_normal_pdf x * (3 + x^2 / 2)
      _ = 3 * standard_normal_pdf x + (1 / 2) * (x^2 * standard_normal_pdf x) := by ring
      _ ≤ 3 * (16 / (x^4 + 16)) + (1 / 2) * (216 * x^2 / (x^6 + 216)) := by gcongr
      _ = 48 / (x^4 + 16) + 108 * x^2 / (x^6 + 216) := by ring

  have h_rpow : (1 + |x|) ^ (3 : ℝ) = (1 + |x|) ^ 3 := Real.rpow_natCast (1 + |x|) 3
  rw [h_rpow]
  calc |standard_normal_pdf x * Real.log (standard_normal_pdf x)|
    _ ≤ standard_normal_pdf x * (3 + x^2 / 2) := h_entropy_le
    _ ≤ 48 / (x^4 + 16) + 108 * x^2 / (x^6 + 216) := h_sum_bound
    _ ≤ 500 / (1 + |x|)^3 + 1500 / (1 + |x|)^3 := add_le_add (bound_term1 x) (bound_term2 x)
    _ = 2000 / (1 + |x|)^3 := by ring


/-- Global polynomial decay on the derivative of the Gaussian entropy density. -/
theorem gaussian_entropy_density_deriv_decay :
    ∃ (C_g' : ℝ) (q_g : ℝ), 1 < q_g ∧ ∀ x, |deriv (fun y => standard_normal_pdf y * Real.log (standard_normal_pdf y)) x| ≤ C_g' / (1 + |x|)^q_g := by
  use 10000, 2
  refine ⟨by norm_num, fun x => ?_⟩
  have h_deriv_pdf : HasDerivAt standard_normal_pdf (- x * standard_normal_pdf x) x := standard_normal_deriv x
  have h_ne : standard_normal_pdf x ≠ 0 := (standard_normal_pos x).ne'
  have h_deriv_log : HasDerivAt (fun y => Real.log (standard_normal_pdf y)) (-x) x := by
    have h_log : HasDerivAt Real.log (standard_normal_pdf x)⁻¹ (standard_normal_pdf x) := Real.hasDerivAt_log h_ne
    have h_comp := HasDerivAt.comp x h_log h_deriv_pdf
    have h_eq : (standard_normal_pdf x)⁻¹ * (- x * standard_normal_pdf x) = - x := by
      calc (standard_normal_pdf x)⁻¹ * (- x * standard_normal_pdf x)
        _ = (standard_normal_pdf x)⁻¹ * standard_normal_pdf x * - x := by ring
        _ = 1 * - x := by rw [inv_mul_cancel₀ h_ne]
        _ = - x := by ring
    rw [h_eq] at h_comp
    exact h_comp

  have h_deriv_entropy : HasDerivAt (fun y => standard_normal_pdf y * Real.log (standard_normal_pdf y))
      (- x * standard_normal_pdf x * Real.log (standard_normal_pdf x) + standard_normal_pdf x * - x) x :=
    HasDerivAt.mul h_deriv_pdf h_deriv_log

  have h_deriv_eq : deriv (fun y => standard_normal_pdf y * Real.log (standard_normal_pdf y)) x =
      - x * standard_normal_pdf x * (1 + Real.log (standard_normal_pdf x)) := by
    have h_eq : - x * standard_normal_pdf x * Real.log (standard_normal_pdf x) + standard_normal_pdf x * - x =
                - x * standard_normal_pdf x * (1 + Real.log (standard_normal_pdf x)) := by ring
    rw [← h_eq]
    exact h_deriv_entropy.deriv

  have h_abs : |- x * standard_normal_pdf x * (1 + Real.log (standard_normal_pdf x))| =
               |x| * standard_normal_pdf x * |1 + Real.log (standard_normal_pdf x)| := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (standard_normal_pos x)]

  have h_ne1 : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≠ 0 := by
    have h_pi : 0 < 2 * Real.pi := by positivity
    have h_sqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_pi
    exact (div_pos (by linarith) h_sqrt).ne'
  have h_ne2 : exp (- x^2 / 2) ≠ 0 := (exp_pos _).ne'
  have h_log_pdf : Real.log (standard_normal_pdf x) = - Real.log (Real.sqrt (2 * Real.pi)) - x^2 / 2 := by
    have h_eq1 : standard_normal_pdf x = (1 / Real.sqrt (2 * Real.pi)) * exp (- x^2 / 2) := rfl
    have h_div : (1 / Real.sqrt (2 * Real.pi) : ℝ) = (Real.sqrt (2 * Real.pi))⁻¹ := by ring
    rw [h_eq1, Real.log_mul h_ne1 h_ne2, h_div, Real.log_inv, Real.log_exp]
    ring

  have h_le_3 : Real.log (Real.sqrt (2 * Real.pi)) ≤ 3 := log_sqrt_two_pi_le_three
  have h_ge_0 : 0 ≤ Real.log (Real.sqrt (2 * Real.pi)) := log_sqrt_two_pi_nonneg

  have h_K0_bound : |1 - Real.log (Real.sqrt (2 * Real.pi))| ≤ 3 := by
    rw [abs_le]
    constructor
    · linarith [h_le_3]
    · linarith [h_ge_0]

  have h_log_bound : |1 + Real.log (standard_normal_pdf x)| ≤ 3 + x^2 / 2 := by
    rw [h_log_pdf]
    have h_eq : 1 + (- Real.log (Real.sqrt (2 * Real.pi)) - x^2 / 2) =
                (1 - Real.log (Real.sqrt (2 * Real.pi))) + (- x^2 / 2) := by ring
    rw [h_eq]
    have h_add := abs_add_le (1 - Real.log (Real.sqrt (2 * Real.pi))) (- x^2 / 2)
    have h_abs_neg : |- x^2 / 2| = x^2 / 2 := by
      have h_nonneg : 0 ≤ x^2 / 2 := by positivity
      have h_nonpos : - x^2 / 2 ≤ 0 := by linarith
      rw [abs_of_nonpos h_nonpos]
      ring
    rw [h_abs_neg] at h_add
    linarith [h_add, h_K0_bound]

  have h_entropy_le : |deriv (fun y => standard_normal_pdf y * Real.log (standard_normal_pdf y)) x| ≤
      |x| * standard_normal_pdf x * (3 + x^2 / 2) := by
    rw [h_deriv_eq, h_abs]
    have h_nonneg : 0 ≤ |x| * standard_normal_pdf x := mul_nonneg (abs_nonneg x) (standard_normal_pos x).le
    exact mul_le_mul_of_nonneg_left h_log_bound h_nonneg

  have h_gauss_le : standard_normal_pdf x ≤ exp (- x^2 / 2) := by
    have h_coeff : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := one_div_sqrt_two_pi_le_one
    have h_exp : 0 ≤ exp (- x^2 / 2) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_right h_coeff h_exp
    rwa [one_mul] at this

  have h_bound4 : |x| * standard_normal_pdf x ≤ 16 * |x| / (x^4 + 16) := by
    have h_mul : |x| * standard_normal_pdf x ≤ |x| * exp (- x^2 / 2) :=
      mul_le_mul_of_nonneg_left h_gauss_le (abs_nonneg x)
    have h_bound_four := exp_bound_four x
    have h_mul2 : |x| * exp (- x^2 / 2) ≤ |x| * (16 / (x^4 + 16)) :=
      mul_le_mul_of_nonneg_left h_bound_four (abs_nonneg x)
    have h_eq : |x| * (16 / (x^4 + 16)) = 16 * |x| / (x^4 + 16) := by ring
    linarith [h_mul, h_mul2, h_eq]

  have h_bound6 : |x| * x^2 * standard_normal_pdf x ≤ 216 * |x| * x^2 / (x^6 + 216) := by
    have h_x_nonneg : 0 ≤ |x| * x^2 := mul_nonneg (abs_nonneg x) (sq_nonneg x)
    have h_mul : |x| * x^2 * standard_normal_pdf x ≤ |x| * x^2 * exp (- x^2 / 2) :=
      mul_le_mul_of_nonneg_left h_gauss_le h_x_nonneg
    have h_bound_six := exp_bound_six x
    have h_mul2 : |x| * x^2 * exp (- x^2 / 2) ≤ |x| * x^2 * (216 / (x^6 + 216)) :=
      mul_le_mul_of_nonneg_left h_bound_six h_x_nonneg
    have h_eq : |x| * x^2 * (216 / (x^6 + 216)) = 216 * |x| * x^2 / (x^6 + 216) := by ring
    linarith [h_mul, h_mul2, h_eq]

  have h_sum_bound : |x| * standard_normal_pdf x * (3 + x^2 / 2) ≤ 48 * |x| / (x^4 + 16) + 108 * |x| * x^2 / (x^6 + 216) := by
    calc |x| * standard_normal_pdf x * (3 + x^2 / 2)
      _ = 3 * (|x| * standard_normal_pdf x) + (1 / 2) * (|x| * x^2 * standard_normal_pdf x) := by ring
      _ ≤ 3 * (16 * |x| / (x^4 + 16)) + (1 / 2) * (216 * |x| * x^2 / (x^6 + 216)) := by gcongr
      _ = 48 * |x| / (x^4 + 16) + 108 * |x| * x^2 / (x^6 + 216) := by ring

  have h_rpow : (1 + |x|) ^ (2 : ℝ) = (1 + |x|) ^ 2 := Real.rpow_natCast (1 + |x|) 2
  rw [h_rpow]
  calc |deriv (fun y => standard_normal_pdf y * Real.log (standard_normal_pdf y)) x|
    _ ≤ |x| * standard_normal_pdf x * (3 + x^2 / 2) := h_entropy_le
    _ ≤ 48 * |x| / (x^4 + 16) + 108 * |x| * x^2 / (x^6 + 216) := h_sum_bound
    _ ≤ 500 / (1 + |x|)^2 + 9500 / (1 + |x|)^2 := add_le_add (bound_deriv_term1 x) (bound_deriv_term2 x)
    _ = 10000 / (1 + |x|)^2 := by ring
