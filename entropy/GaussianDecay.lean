import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import entropy.GaussianBase
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

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
-- PART 3: Global Polynomial Decay Verification (Proofs replacing Axioms)
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
